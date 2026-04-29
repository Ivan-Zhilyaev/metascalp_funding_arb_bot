#!/usr/bin/env python3
"""
Funding Rate Arbitrage Scanner + Executor for MetaScalp
Version: 1.6.2
"""

import os
import sys
import json
import time
import logging
import asyncio
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Set, Any, Tuple
from dataclasses import dataclass, asdict
from enum import Enum
from collections import deque
from logging.handlers import RotatingFileHandler
from contextlib import asynccontextmanager

import yaml
import aiohttp
import ccxt.async_support as ccxt
from fastapi import FastAPI, HTTPException
from fastapi.responses import HTMLResponse
import uvicorn


# ============================================================================
# Версия
# ============================================================================

__version__ = "1.6.2"
BOT_NAME = "Funding Arbitrage Bot"


# ============================================================================
# Конфигурация и структуры данных
# ============================================================================

class StrategyState(Enum):
    CLOSED = "closed"
    OPENING = "opening"
    OPENED = "opened"
    CLOSING = "closing"


class StrategyAction(Enum):
    NULL = "null"
    BUY_SPOT_SHORT_PERP = "buy_spot_short_perp"
    SELL_SPOT_LONG_PERP = "sell_spot_long_perp"


class ConnectionState(Enum):
    DISCONNECTED = "disconnected"
    CONNECTING = "connecting"
    CONNECTED = "connected"
    RECONNECTING = "reconnecting"


class ExitReason(Enum):
    NORMAL = "normal"
    FUNDING_RATE_SIGN_CHANGED = "funding_rate_sign_changed"
    MAX_POSITION_AGE = "max_position_age"
    MANUAL = "manual"
    ERROR = "error"
    UNKNOWN = "unknown"


@dataclass
class ArbitrageOpportunity:
    timestamp: float
    symbol: str
    spot_exchange: str
    perp_exchange: str
    funding_rate: float
    expected_profit_bps: float
    spot_price: float = 0.0
    perp_price: float = 0.0
    direction: str = ""
    next_funding_time: Optional[float] = None
    volume_24h_usdt: float = 0.0
    spread_pct: float = 0.0
    spot_fee_pct: float = 0.0
    perp_fee_pct: float = 0.0
    net_profit_bps: float = 0.0

    def to_dict(self) -> dict:
        return {
            'timestamp': self.timestamp,
            'datetime': datetime.fromtimestamp(self.timestamp).isoformat(),
            'symbol': self.symbol,
            'spot_exchange': self.spot_exchange,
            'perp_exchange': self.perp_exchange,
            'funding_rate': self.funding_rate,
            'funding_rate_pct': self.funding_rate * 100,
            'expected_profit_bps': self.expected_profit_bps,
            'net_profit_bps': self.net_profit_bps,
            'spot_price': self.spot_price,
            'perp_price': self.perp_price,
            'direction': self.direction,
            'next_funding_time': self.next_funding_time,
            'next_funding_datetime': datetime.fromtimestamp(self.next_funding_time).isoformat() if self.next_funding_time else None,
            'volume_24h_usdt': self.volume_24h_usdt,
            'spread_pct': self.spread_pct,
            'spot_fee_pct': self.spot_fee_pct,
            'perp_fee_pct': self.perp_fee_pct
        }


@dataclass
class Position:
    symbol: str
    spot_exchange: str
    perp_exchange: str
    direction: str
    entry_time: float
    entry_funding_rate: float
    size_usdt: float
    spot_order_id: Optional[str] = None
    perp_order_id: Optional[str] = None
    spot_filled: bool = False
    perp_filled: bool = False
    close_time: Optional[float] = None
    pnl: Optional[float] = None
    next_funding_time: Optional[float] = None
    leverage: int = 3
    exit_reason: Optional[str] = None
    spot_entry_fee: float = 0.0
    perp_entry_fee: float = 0.0
    spot_exit_fee: float = 0.0
    perp_exit_fee: float = 0.0


@dataclass
class TradeRecord:
    id: str
    symbol: str
    direction: str
    entry_time: float
    exit_time: float
    size_usdt: float
    entry_funding_rate: float
    pnl: float
    pnl_pct: float
    leverage: int = 3
    exit_reason: str = "normal"
    spot_entry_fee: float = 0.0
    perp_entry_fee: float = 0.0
    spot_exit_fee: float = 0.0
    perp_exit_fee: float = 0.0

    def to_dict(self) -> dict:
        return {
            'id': self.id,
            'symbol': self.symbol,
            'direction': self.direction,
            'entry_time': self.entry_time,
            'exit_time': self.exit_time,
            'entry_datetime': datetime.fromtimestamp(self.entry_time).isoformat(),
            'exit_datetime': datetime.fromtimestamp(self.exit_time).isoformat(),
            'size_usdt': self.size_usdt,
            'entry_funding_rate': self.entry_funding_rate,
            'pnl': self.pnl,
            'pnl_pct': self.pnl_pct,
            'leverage': self.leverage,
            'exit_reason': self.exit_reason,
            'spot_entry_fee': self.spot_entry_fee,
            'perp_entry_fee': self.perp_entry_fee,
            'spot_exit_fee': self.spot_exit_fee,
            'perp_exit_fee': self.perp_exit_fee
        }


# ============================================================================
# Главный класс бота
# ============================================================================

class FundingArbitrageBot:
    """Асинхронный бот для фандингового арбитража с поддержкой множественных позиций"""

    def __init__(self, config_path: str = "config.yaml"):
        self.config_path = config_path
        self.config = self._load_config(config_path)
        self._setup_logging()

        # === Состояние стратегии ===
        self.strategy_state = StrategyState.CLOSED
        self.last_strategy_action = StrategyAction.NULL
        self.positions: List[Position] = []
        self._last_current_rates: Dict[str, float] = {}
        self._pending_exit_reason: Optional[ExitReason] = None

        # === Тайминги ===
        self.in_flight_state_start_ts: float = 0
        self.in_flight_state_tolerance: int = self.config.get('in_flight_state_tolerance', 60)
        self.opened_state_start_ts: float = 0
        self.opened_state_tolerance: int = self.config.get('opened_state_tolerance', 7200)
        self.next_arbitrage_opening_ts: float = 0
        self.next_arbitrage_opening_delay: int = self.config.get('next_arbitrage_opening_delay', 10)
        self.max_concurrent_positions: int = self.config.get('max_concurrent_positions', 1)

        # === Белый список ===
        self.whitelist: Set[str] = set()
        self.whitelist_mtime: float = 0

        # === MetaScalp ===
        self.metascalp_port: Optional[int] = None
        self.metascalp_session: Optional[aiohttp.ClientSession] = None
        self.metascalp_state = ConnectionState.DISCONNECTED
        self.metascalp_connections: Dict[str, Dict] = {}
        self.metascalp_balances: Dict[int, float] = {}
        self.last_metascalp_check: float = 0
        self.last_balance_update: float = 0
        self.metascalp_reconnect_attempts = 0
        self.balance_update_interval = self.config.get('balance_update_interval', 30)

        # === Режимы ===
        self.auto_test_mode = True
        self.manual_test_mode = self.config.get('test_mode', True)

        # === CCXT биржи ===
        self.exchanges: Dict[str, ccxt.Exchange] = {}
        self.exchanges_online: Dict[str, bool] = {}

        # === Параметры ===
        self.base_order_amount = self.config.get('base_order_amount', 100.0)
        self.min_profit_bps = self.config.get('min_profit_bps', 10)
        self.slippage_buffer_bps = self.config.get('slippage_bps', 15)
        self.funding_rate_threshold = self.config.get('funding_rate_threshold', 0.0001)
        self.scan_interval = self.config.get('scan_interval', 5)
        self.leverage = self.config.get('leverage', 3)
        self.margin_enabled = self.config.get('margin_enabled', False)
        self.min_volume_24h_usdt = self.config.get('min_volume_24h_usdt', 10000)
        self.max_slippage_pct = self.config.get('max_slippage_pct', 1.0)
        self.max_recent_opportunities = self.config.get('max_recent_opportunities', 5)
        self.max_current_opportunities = self.config.get('max_current_opportunities', 5)

        # === Фильтры ===
        self.min_time_to_funding_minutes = self.config.get('min_time_to_funding_minutes', 0)
        self.check_trading_status = self.config.get('check_trading_status', True)
        self.deduct_fees_from_profit = self.config.get('deduct_fees_from_profit', True)
        self.manual_spot_fee_pct = self.config.get('manual_spot_fee_pct', 0.1)
        self.manual_futures_fee_pct = self.config.get('manual_futures_fee_pct', 0.05)

        # === Кэш комиссий ===
        self.spot_fees_cache: Dict[str, Dict[str, float]] = {}
        self.futures_fees_cache: Dict[str, Dict[str, float]] = {}

        # === Данные для дашборда ===
        self.current_opportunities: List[ArbitrageOpportunity] = []
        self.recent_opportunities: deque = deque(maxlen=self.max_recent_opportunities)
        self.last_scan_time: float = 0
        self.trades_history: List[TradeRecord] = []
        self._load_trades_history()

        # === Файл открытых позиций ===
        self.open_positions_file = self.config.get('open_positions_file', 'logs/open_positions.json')

        # === Статистика ===
        self.scan_count = 0
        self.opportunities_found = 0
        self.filtered_by_volume = 0
        self.filtered_by_spread = 0
        self.filtered_by_margin = 0
        self.filtered_by_time = 0
        self.filtered_by_status = 0
        self.filtered_by_fees = 0
        self.total_pnl = 0.0
        for trade in self.trades_history:
            self.total_pnl += trade.pnl

        # === Управление циклом ===
        self.is_running = True
        self.scan_task: Optional[asyncio.Task] = None

        self._log_startup_info()

    # ========================================================================
    # Конфигурация
    # ========================================================================

    def _load_config(self, path: str) -> dict:
        with open(path, 'r', encoding='utf-8') as f:
            config = yaml.safe_load(f)

        defaults = {
            'active_exchanges': [], 'margin_enabled': False, 'min_volume_24h_usdt': 10000,
            'max_slippage_pct': 1.0, 'max_recent_opportunities': 5, 'max_current_opportunities': 5,
            'min_time_to_funding_minutes': 0, 'check_trading_status': True,
            'deduct_fees_from_profit': True, 'manual_spot_fee_pct': 0.1, 'manual_futures_fee_pct': 0.05,
            'balance_update_interval': 30, 'max_concurrent_positions': 1,
            'signal_log_file': 'logs/signal.log', 'open_positions_file': 'logs/open_positions.json',
            'fallback_priority': ['binance', 'bybit', 'gate', 'kucoin', 'mexc', 'okx', 'bitget']
        }
        for key, value in defaults.items():
            if key not in config:
                config[key] = value

        if 'active_exchanges' not in config or not config['active_exchanges']:
            config['active_exchanges'] = config.get('enabled_exchanges', []).copy()

        return config

    def _save_config(self) -> None:
        with open(self.config_path, 'w', encoding='utf-8') as f:
            yaml.dump(self.config, f, default_flow_style=False, allow_unicode=True)

    def _setup_logging(self) -> None:
        log_format = '%(asctime)s | %(levelname)-8s | %(message)s'
        date_format = '%Y-%m-%d %H:%M:%S'

        log_file = self.config.get('log_file', 'logs/bot.log')
        Path(log_file).parent.mkdir(parents=True, exist_ok=True)

        logging.basicConfig(
            level=logging.INFO,
            format=log_format,
            datefmt=date_format,
            handlers=[
                logging.StreamHandler(sys.stdout),
                logging.FileHandler(log_file, encoding='utf-8')
            ]
        )
        self.logger = logging.getLogger(__name__)

        # Отдельный логгер для сигналов с ротацией
        signal_log_file = self.config.get('signal_log_file', 'logs/signal.log')
        Path(signal_log_file).parent.mkdir(parents=True, exist_ok=True)

        self.signal_logger = logging.getLogger('signal_logger')
        self.signal_logger.setLevel(logging.INFO)
        signal_handler = RotatingFileHandler(
            signal_log_file,
            maxBytes=10 * 1024 * 1024,
            backupCount=5,
            encoding='utf-8'
        )
        signal_handler.setFormatter(logging.Formatter('%(asctime)s | %(message)s', date_format))
        self.signal_logger.addHandler(signal_handler)
        self.signal_logger.propagate = False

    def _load_trades_history(self) -> None:
        trades_file = self.config.get('trades_file', 'logs/trades.json')
        try:
            path = Path(trades_file)
            if path.exists():
                with open(path, 'r') as f:
                    data = json.load(f)
                    for t in data:
                        t.pop('entry_datetime', None)
                        t.pop('exit_datetime', None)
                        t.setdefault('exit_reason', 'unknown')
                        t.setdefault('spot_entry_fee', 0.0)
                        t.setdefault('perp_entry_fee', 0.0)
                        t.setdefault('spot_exit_fee', 0.0)
                        t.setdefault('perp_exit_fee', 0.0)
                        self.trades_history.append(TradeRecord(**t))
                self.logger.info(f"📊 Загружено {len(self.trades_history)} записей о сделках")
        except Exception as e:
            self.logger.error(f"Ошибка загрузки истории: {e}")

    def _save_trades_history(self) -> None:
        trades_file = self.config.get('trades_file', 'logs/trades.json')
        try:
            path = Path(trades_file)
            path.parent.mkdir(parents=True, exist_ok=True)
            with open(path, 'w') as f:
                json.dump([t.to_dict() for t in self.trades_history], f, indent=2)
        except Exception as e:
            self.logger.error(f"Ошибка сохранения истории: {e}")

    def _add_trade_record(self, trade: TradeRecord) -> None:
        self.trades_history.append(trade)
        self.total_pnl += trade.pnl
        self._save_trades_history()

    # ========================================================================
    # Персистентность открытых позиций
    # ========================================================================

    def _load_open_positions(self) -> None:
        """Загрузка открытых позиций из файла"""
        try:
            path = Path(self.open_positions_file)
            if path.exists():
                with open(path, 'r') as f:
                    data = json.load(f)
                    for p in data:
                        pos = Position(**p)
                        self.positions.append(pos)
                self.logger.info(f"📂 Загружено {len(self.positions)} открытых позиций из файла")
            else:
                self.logger.info("📂 Файл открытых позиций не найден, начинаем с пустого списка")
        except Exception as e:
            self.logger.error(f"❌ Ошибка загрузки открытых позиций: {e}")

    def _save_open_positions(self) -> None:
        """Сохранение открытых позиций в файл"""
        try:
            path = Path(self.open_positions_file)
            path.parent.mkdir(parents=True, exist_ok=True)
            active = [asdict(p) for p in self.active_positions]
            with open(path, 'w') as f:
                json.dump(active, f, indent=2)
            self.logger.debug(f"💾 Сохранено {len(active)} открытых позиций")
        except Exception as e:
            self.logger.error(f"❌ Ошибка сохранения открытых позиций: {e}")

    async def _check_perp_position_exists(self, pos: Position) -> bool:
        """Проверяет, существует ли фьючерсная позиция на бирже через MetaScalp API"""
        if pos.perp_exchange not in self.metascalp_connections:
            return False
        
        perp_conn_id = self.metascalp_connections[pos.perp_exchange].get('perp_id')
        if not perp_conn_id:
            return False

        try:
            async with self.metascalp_session.get(
                f"http://127.0.0.1:{self.metascalp_port}/api/connections/{perp_conn_id}/positions"
            ) as resp:
                if resp.status != 200:
                    return False
                data = await resp.json()
                clean_symbol = pos.symbol.replace('/USDT:USDT', 'USDT').replace('/USDT', 'USDT')
                
                for real_pos in data.get('Positions', []):
                    if real_pos.get('Ticker') == clean_symbol:
                        if pos.direction == 'BUY_SPOT_SHORT_PERP' and real_pos.get('Side') == 2:
                            return True
                        elif pos.direction == 'SELL_SPOT_LONG_PERP' and real_pos.get('Side') == 1:
                            return True
                return False
        except Exception as e:
            self.logger.debug(f"Ошибка проверки позиции {pos.symbol}: {e}")
            return False

    async def _sync_positions_with_exchange(self) -> None:
        """Синхронизация позиций из файла с реальными на бирже (только для реальной торговли)"""
        if self.is_test_mode:
            self.logger.info(f"🧪 Тестовый режим: {len(self.positions)} позиций загружено из файла")
            return

        self.logger.info("🔄 Синхронизация позиций с биржей...")
        valid_positions = []
        
        for pos in self.positions:
            if await self._check_perp_position_exists(pos):
                valid_positions.append(pos)
                self.logger.info(f"   ✅ Позиция {pos.symbol} на {pos.perp_exchange} подтверждена")
            else:
                self.logger.warning(f"   ❌ Позиция {pos.symbol} на {pos.perp_exchange} не найдена на бирже, удалена")
        
        self.positions = valid_positions
        self._save_open_positions()
        self.logger.info(f"✅ Синхронизация завершена, осталось {len(self.positions)} позиций")

    def _log_startup_info(self) -> None:
        self.logger.info("=" * 70)
        self.logger.info(f"🤖 {BOT_NAME} v{__version__}")
        self.logger.info("=" * 70)
        self.logger.info(f"📁 Конфигурация: {self.config_path}")
        self.logger.info(f"🔄 Режим: {'ТЕСТОВЫЙ' if self.manual_test_mode else 'ТОРГОВЛЯ'}")
        self.logger.info(f"📊 Все биржи: {', '.join(self.config['enabled_exchanges'])}")
        self.logger.info(f"✅ Активные биржи: {', '.join(self.config['active_exchanges'])}")
        self.logger.info(f"💵 Размер позиции: {self.base_order_amount} USDT")
        self.logger.info(f"⚡ Плечо (фьючерсы): {self.leverage}x")
        self.logger.info(f"📈 Маржинальная торговля (спот): {'ВКЛЮЧЕНА' if self.margin_enabled else 'ВЫКЛЮЧЕНА'}")
        self.logger.info(f"🔢 Макс. одновременных сделок: {self.max_concurrent_positions}")
        self.logger.info(f"⏰ Мин. время до выплаты: {self.min_time_to_funding_minutes} мин")
        self.logger.info("=" * 70)

    # ========================================================================
    # Свойства
    # ========================================================================

    @property
    def is_test_mode(self) -> bool:
        return self.manual_test_mode

    @property
    def current_timestamp(self) -> float:
        return time.time()

    @property
    def active_positions(self) -> List[Position]:
        return [p for p in self.positions if not p.close_time]

    @property
    def exchange_status(self) -> str:
        if not self.exchanges:
            return "OFFLINE"
        online_count = sum(1 for v in self.exchanges_online.values() if v)
        total_count = len(self.exchanges)
        if online_count == total_count and total_count > 0:
            return "ONLINE"
        elif online_count > 0:
            return "PARTIAL"
        else:
            return "OFFLINE"

    # ========================================================================
    # Управление позициями
    # ========================================================================

    def can_open_new_position(self) -> bool:
        return len(self.active_positions) < self.max_concurrent_positions

    def is_position_already_open(self, symbol: str, spot_ex: str, perp_ex: str) -> bool:
        """Проверяет, открыта ли уже ТОЧНО ТАКАЯ ЖЕ позиция (символ + спот + перп)"""
        for p in self.active_positions:
            if p.symbol == symbol and p.spot_exchange == spot_ex and p.perp_exchange == perp_ex:
                return True
        return False

    def find_position_by_id(self, position_id: str) -> Optional[Position]:
        """Находит позицию по уникальному идентификатору"""
        for pos in self.active_positions:
            pos_id = f"{pos.symbol}_{pos.spot_exchange}_{pos.perp_exchange}_{pos.entry_time}"
            if pos_id == position_id:
                return pos
        return None

    # ========================================================================
    # Синхронизация с MetaScalp
    # ========================================================================

    def _sync_exchanges_from_metascalp(self) -> None:
        if not self.metascalp_connections:
            return

        current_enabled = set(self.config.get('enabled_exchanges', []))
        metascalp_exchanges = set(self.metascalp_connections.keys())
        new_exchanges = metascalp_exchanges - current_enabled

        if new_exchanges:
            self.config['enabled_exchanges'] = sorted(list(current_enabled | metascalp_exchanges))
            self._save_config()
            self.logger.info(f"📝 Добавлены новые биржи из MetaScalp: {', '.join(new_exchanges)}")

    def _sync_exchange_pairs_from_metascalp(self) -> None:
        if not self.metascalp_connections:
            return

        active_exchanges = set(self.config.get('active_exchanges', []))
        spot_exchanges = [ex for ex, conns in self.metascalp_connections.items() 
                         if 'spot_id' in conns and ex in active_exchanges]
        perp_exchanges = [ex for ex, conns in self.metascalp_connections.items() 
                         if 'perp_id' in conns and ex in active_exchanges]

        if not spot_exchanges or not perp_exchanges:
            return

        new_pairs = []
        for spot_ex in spot_exchanges:
            for perp_ex in perp_exchanges:
                new_pairs.append({'spot': spot_ex, 'perp': perp_ex})

        current_pairs = self.config.get('exchange_pairs', [])
        current_pairs_set = {f"{p['spot']}|{p['perp']}" for p in current_pairs}
        new_pairs_set = {f"{p['spot']}|{p['perp']}" for p in new_pairs}
        added_pairs = new_pairs_set - current_pairs_set

        if added_pairs:
            for pair_str in added_pairs:
                spot, perp = pair_str.split('|')
                current_pairs.append({'spot': spot, 'perp': perp})

            self.config['exchange_pairs'] = current_pairs
            self._save_config()
            self.logger.info(f"📝 Добавлены новые пары бирж в exchange_pairs: {len(added_pairs)} шт.")
            self.logger.info(f"   Всего комбинаций: {len(current_pairs)} (спот: {len(spot_exchanges)}, перп: {len(perp_exchanges)})")

    async def _update_metascalp_balances(self) -> None:
        if not self.metascalp_session or self.metascalp_state != ConnectionState.CONNECTED:
            self.logger.debug("MetaScalp не подключен, балансы не обновляются")
            return

        now = time.time()
        if now - self.last_balance_update < self.balance_update_interval:
            return
        self.last_balance_update = now

        self.logger.info("🔄 Обновление балансов MetaScalp...")
        updated_count = 0

        for ex_name, conns in self.metascalp_connections.items():
            if conns.get('view_mode', False):
                self.logger.debug(f"   ⏭️ {ex_name.upper()} пропущен (ViewMode)")
                continue

            for conn_type, conn_id in [('spot_id', conns.get('spot_id')), ('perp_id', conns.get('perp_id'))]:
                if conn_id:
                    try:
                        async with self.metascalp_session.get(
                            f"http://127.0.0.1:{self.metascalp_port}/api/connections/{conn_id}/balance"
                        ) as resp:
                            if resp.status == 200:
                                data = await resp.json()
                                balances = data.get('balances', data.get('Balances', []))
                                for b in balances:
                                    if b.get('Coin') == 'USDT':
                                        balance = float(b.get('Free', 0))
                                        self.metascalp_balances[conn_id] = balance
                                        self.logger.info(f"   💰 {ex_name.upper()} {conn_type}: {balance:.6f} USDT")
                                        updated_count += 1
                                        break
                            else:
                                self.logger.debug(f"   ⚠️ {ex_name} {conn_type}: HTTP {resp.status}")
                    except Exception as e:
                        self.logger.debug(f"   ❌ {ex_name} {conn_type}: {e}")

        self.logger.info(f"✅ Обновлено балансов: {updated_count}")

    # ========================================================================
    # Управление конфигурацией
    # ========================================================================

    def update_config(self, updates: Dict[str, Any]) -> None:
        old_deduct_fees = self.config.get('deduct_fees_from_profit', True)
        
        for key, value in updates.items():
            if key in self.config:
                self.config[key] = value
                self.logger.info(f"📝 Конфиг обновлён: {key} = {value}")

        self.scan_interval = self.config.get('scan_interval', 5)
        self.manual_test_mode = self.config.get('test_mode', True)
        self.base_order_amount = self.config.get('base_order_amount', 100.0)
        self.min_profit_bps = self.config.get('min_profit_bps', 10)
        self.leverage = self.config.get('leverage', 3)
        self.margin_enabled = self.config.get('margin_enabled', False)
        self.min_volume_24h_usdt = self.config.get('min_volume_24h_usdt', 10000)
        self.max_slippage_pct = self.config.get('max_slippage_pct', 1.0)
        self.min_time_to_funding_minutes = self.config.get('min_time_to_funding_minutes', 0)
        self.check_trading_status = self.config.get('check_trading_status', True)
        self.deduct_fees_from_profit = self.config.get('deduct_fees_from_profit', True)
        self.manual_spot_fee_pct = self.config.get('manual_spot_fee_pct', 0.1)
        self.manual_futures_fee_pct = self.config.get('manual_futures_fee_pct', 0.05)
        self.balance_update_interval = self.config.get('balance_update_interval', 30)
        self.max_concurrent_positions = self.config.get('max_concurrent_positions', 1)

        if old_deduct_fees and not self.deduct_fees_from_profit:
            self.spot_fees_cache.clear()
            self.futures_fees_cache.clear()
            self.logger.info("🧹 Кэш комиссий очищен")

        if self.manual_test_mode:
            self.auto_test_mode = False

        new_max = self.config.get('max_recent_opportunities', 5)
        if new_max != self.recent_opportunities.maxlen:
            old_items = list(self.recent_opportunities)
            self.recent_opportunities = deque(old_items, maxlen=new_max)

        self.max_current_opportunities = self.config.get('max_current_opportunities', 5)

        self._save_config()
        self.logger.info(f"🔄 Режим работы: {'ТЕСТОВЫЙ' if self.is_test_mode else 'ТОРГОВЛЯ'}")

    def update_active_exchanges(self, exchanges: List[str]) -> None:
        valid_exchanges = [e for e in exchanges if e in self.config['enabled_exchanges']]
        self.config['active_exchanges'] = valid_exchanges
        self._save_config()
        self.logger.info(f"📝 Активные биржи обновлены: {', '.join(valid_exchanges)}")
        self._sync_exchange_pairs_from_metascalp()

    def get_status(self) -> dict:
        active_positions = self.active_positions
        first_position = active_positions[0] if active_positions else None
        
        positions_with_id = []
        for p in active_positions:
            p_dict = asdict(p)
            p_dict['position_id'] = f"{p.symbol}_{p.spot_exchange}_{p.perp_exchange}_{p.entry_time}"
            
            if p.next_funding_time:
                time_to_funding = p.next_funding_time - self.current_timestamp
                if time_to_funding > 0:
                    hours = int(time_to_funding // 3600)
                    minutes = int((time_to_funding % 3600) // 60)
                    p_dict['funding_time_str'] = f"{hours}ч {minutes}м"
                else:
                    p_dict['funding_time_str'] = "выплата идёт"
            else:
                p_dict['funding_time_str'] = "—"
            
            positions_with_id.append(p_dict)
        
        next_funding_str = positions_with_id[0]['funding_time_str'] if positions_with_id else None

        current_rates = {}
        for pos in active_positions:
            rate = self._last_current_rates.get(pos.symbol)
            self.logger.debug(f"📊 get_status: {pos.symbol} -> {rate}")
            if rate is not None:
                current_rates[pos.symbol] = rate

        return {
            'version': __version__,
            'bot_name': BOT_NAME,
            'timestamp': self.current_timestamp,
            'datetime': datetime.now().isoformat(),
            'strategy_state': self.strategy_state.value,
            'connection_state': self.metascalp_state.value,
            'exchange_status': self.exchange_status,
            'test_mode': self.is_test_mode,
            'auto_test_mode': self.auto_test_mode,
            'metascalp_port': self.metascalp_port,
            'metascalp_connections': self.metascalp_connections,
            'metascalp_balances': self.metascalp_balances,
            'positions': positions_with_id,
            'position': asdict(first_position) if first_position else None,
            'active_positions_count': len(active_positions),
            'current_funding_rate': current_rates.get(first_position.symbol) if first_position else None,
            'current_funding_rates': current_rates,
            'next_funding_time_str': next_funding_str,
            'scan_count': self.scan_count,
            'opportunities_found': self.opportunities_found,
            'filtered_by_volume': self.filtered_by_volume,
            'filtered_by_spread': self.filtered_by_spread,
            'filtered_by_margin': self.filtered_by_margin,
            'filtered_by_time': self.filtered_by_time,
            'filtered_by_status': self.filtered_by_status,
            'filtered_by_fees': self.filtered_by_fees,
            'total_pnl': self.total_pnl,
            'trades_count': len(self.trades_history),
            'current_opportunities': [o.to_dict() for o in self.current_opportunities],
            'recent_opportunities': [o.to_dict() for o in self.recent_opportunities],
            'last_scan_time': self.last_scan_time,
            'config': {
                'enabled_exchanges': self.config.get('enabled_exchanges', []),
                'active_exchanges': self.config.get('active_exchanges', []),
                'scan_interval': self.scan_interval,
                'base_order_amount': self.base_order_amount,
                'min_profit_bps': self.min_profit_bps,
                'test_mode': self.manual_test_mode,
                'leverage': self.leverage,
                'margin_enabled': self.margin_enabled,
                'min_volume_24h_usdt': self.min_volume_24h_usdt,
                'max_slippage_pct': self.max_slippage_pct,
                'max_recent_opportunities': self.max_recent_opportunities,
                'max_current_opportunities': self.max_current_opportunities,
                'min_time_to_funding_minutes': self.min_time_to_funding_minutes,
                'check_trading_status': self.check_trading_status,
                'deduct_fees_from_profit': self.deduct_fees_from_profit,
                'manual_spot_fee_pct': self.manual_spot_fee_pct,
                'manual_futures_fee_pct': self.manual_futures_fee_pct,
                'balance_update_interval': self.balance_update_interval,
                'max_concurrent_positions': self.max_concurrent_positions
            },
            'trades_history': [t.to_dict() for t in self.trades_history[-10:]]
        }

    # ========================================================================
    # Инициализация и завершение
    # ========================================================================

    async def initialize(self) -> None:
        await self._init_exchanges()
        await self._connect_metascalp()
        self._load_open_positions()
        await self._sync_positions_with_exchange()
        
        # Запрашиваем актуальные ставки для всех загруженных позиций
        self.logger.info(f"🔄 Загрузка актуальных ставок для {len(self.positions)} позиций...")
        for pos in self.positions:
            if not pos.close_time:
                self.logger.info(f"   Запрос ставки для {pos.symbol} на {pos.perp_exchange}...")
                result = await self._fetch_funding_rate(pos.perp_exchange, pos.symbol)
                if result:
                    current_rate, _ = result
                    self._last_current_rates[pos.symbol] = current_rate
                    self.logger.info(f"   ✅ Ставка для {pos.symbol}: {current_rate*100:.4f}%")
                else:
                    self.logger.warning(f"   ❌ Не удалось получить ставку для {pos.symbol}")

    async def _connect_metascalp(self) -> bool:
        self.metascalp_state = ConnectionState.CONNECTING

        port = await self._discover_metascalp_port()
        if not port:
            self.logger.warning("⚠️ MetaScalp не найден.")
            self.metascalp_state = ConnectionState.DISCONNECTED
            if not self.manual_test_mode:
                self.auto_test_mode = True
                self.logger.warning("🔶 Включён АВТО-ТЕСТОВЫЙ режим (нет MetaScalp)")
            return False

        self.metascalp_port = port

        if self.metascalp_session:
            await self.metascalp_session.close()
        self.metascalp_session = aiohttp.ClientSession()

        success = await self._fetch_connection_ids()

        if success:
            self.metascalp_state = ConnectionState.CONNECTED
            self.metascalp_reconnect_attempts = 0
            self.auto_test_mode = False
            self._log_metascalp_connections()
            self._sync_exchanges_from_metascalp()
            self._sync_exchange_pairs_from_metascalp()
            self.last_balance_update = 0
            await self._update_metascalp_balances()
            self.logger.info(f"🔄 Режим работы: {'ТЕСТОВЫЙ' if self.is_test_mode else 'ТОРГОВЛЯ'}")
            return True
        else:
            self.logger.warning("⚠️ Не удалось получить ID подключений.")
            self.metascalp_state = ConnectionState.DISCONNECTED
            if not self.manual_test_mode:
                self.auto_test_mode = True
            return False

    async def _discover_metascalp_port(self) -> Optional[int]:
        for port in range(17845, 17856):
            try:
                async with aiohttp.ClientSession() as session:
                    async with session.get(
                        f"http://127.0.0.1:{port}/ping",
                        timeout=aiohttp.ClientTimeout(total=1)
                    ) as resp:
                        if resp.status == 200:
                            data = await resp.json()
                            app_name = data.get("App") or data.get("app") or ""
                            if app_name == "MetaScalp":
                                version = data.get("Version") or data.get("vers") or "unknown"
                                self.logger.info(f"✅ MetaScalp найден на порту {port}, версия {version}")
                                return port
            except:
                continue
        return None

    async def _fetch_connection_ids(self) -> bool:
        if not self.metascalp_session:
            return False

        try:
            async with self.metascalp_session.get(
                f"http://127.0.0.1:{self.metascalp_port}/api/connections"
            ) as resp:
                if resp.status != 200:
                    return False

                data = await resp.json()
                connections = data.get('Connections', data.get('connections', []))

                self.metascalp_connections.clear()

                for conn in connections:
                    exchange_name = conn['Exchange'].lower()
                    market_type = conn['MarketType']
                    conn_id = conn['Id']
                    conn_state = conn['State']
                    view_mode = conn.get('ViewMode', False)

                    if conn_state != 2:
                        continue

                    if exchange_name not in self.metascalp_connections:
                        self.metascalp_connections[exchange_name] = {'view_mode': view_mode}
                    else:
                        self.metascalp_connections[exchange_name]['view_mode'] = (
                            self.metascalp_connections[exchange_name].get('view_mode', True) and view_mode
                        )

                    is_spot = market_type == 0
                    is_perp = market_type in (1, 2, 5)

                    if is_spot:
                        self.metascalp_connections[exchange_name]['spot_id'] = conn_id
                        self.metascalp_connections[exchange_name]['spot_name'] = conn['Name']
                        self.metascalp_connections[exchange_name]['spot_view_mode'] = view_mode
                        if not view_mode:
                            self.logger.info(f"   📗 {exchange_name.upper()} SPOT: ID={conn_id}")
                    elif is_perp:
                        self.metascalp_connections[exchange_name]['perp_id'] = conn_id
                        self.metascalp_connections[exchange_name]['perp_name'] = conn['Name']
                        self.metascalp_connections[exchange_name]['perp_view_mode'] = view_mode
                        if not view_mode:
                            self.logger.info(f"   📕 {exchange_name.upper()} PERP: ID={conn_id}")

                if not self.metascalp_connections:
                    self.logger.warning("Не найдено активных подключений")
                    return False

                return True

        except Exception as e:
            self.logger.error(f"❌ Ошибка получения подключений: {e}")
            return False

    def _log_metascalp_connections(self) -> None:
        self.logger.info("📡 Активные подключения MetaScalp:")
        for ex_name, conns in self.metascalp_connections.items():
            spot_id = conns.get('spot_id', '—')
            perp_id = conns.get('perp_id', '—')
            view_mode = " (ViewOnly)" if conns.get('view_mode', False) else ""
            self.logger.info(f"   • {ex_name.upper()}: Spot ID={spot_id}, Perp ID={perp_id}{view_mode}")

    async def _check_metascalp_connection(self) -> None:
        now = time.time()
        check_interval = self.config.get('metascalp_connection_check_interval', 60)

        if now - self.last_metascalp_check < check_interval:
            return

        self.last_metascalp_check = now
        await self._update_metascalp_balances()

        if self.metascalp_state == ConnectionState.CONNECTED:
            try:
                async with self.metascalp_session.get(
                    f"http://127.0.0.1:{self.metascalp_port}/ping",
                    timeout=aiohttp.ClientTimeout(total=2)
                ) as resp:
                    if resp.status != 200:
                        raise Exception("Ping failed")
            except:
                self.logger.warning("⚠️ Соединение с MetaScalp потеряно")
                self.metascalp_state = ConnectionState.DISCONNECTED
                if not self.manual_test_mode:
                    self.auto_test_mode = True
                    self.logger.warning("🔶 Включён АВТО-ТЕСТОВЫЙ режим")

        elif self.metascalp_state == ConnectionState.DISCONNECTED:
            timeout = self.config.get('metascalp_reconnect_timeout', 30)
            max_attempts = self.config.get('metascalp_max_reconnect_attempts', 10)

            if self.metascalp_reconnect_attempts < max_attempts:
                self.metascalp_reconnect_attempts += 1
                self.logger.info(f"🔄 Попытка переподключения ({self.metascalp_reconnect_attempts}/{max_attempts})...")

                if await self._connect_metascalp():
                    self.logger.info("✅ Соединение восстановлено!")
                    self.auto_test_mode = False
                    if not self.manual_test_mode:
                        self.logger.info("🔄 Режим работы: ТОРГОВЛЯ")
            else:
                self.metascalp_reconnect_attempts = 0

    async def _init_exchanges(self) -> None:
        """Инициализация ТОЛЬКО активных бирж CCXT с повторными попытками при ошибках"""
        active_exchanges = set(self.config.get('active_exchanges', []))
        
        for ex_name in self.config['enabled_exchanges']:
            if ex_name not in active_exchanges:
                self.logger.debug(f"⏭️ Биржа {ex_name} не активна, пропускаем инициализацию")
                continue
                
            success = False
            for attempt in range(3):
                try:
                    exchange_class = getattr(ccxt, ex_name)
                    exchange = exchange_class({
                        'enableRateLimit': True,
                        'timeout': 30000,
                        'options': {'defaultType': 'future' if ex_name == 'binance' else 'swap'}
                    })
                    await exchange.load_markets()
                    self.exchanges[ex_name] = exchange
                    self.exchanges_online[ex_name] = True
                    self.logger.info(f"✅ Биржа {ex_name.upper()} инициализирована")
                    success = True
                    break
                except Exception as e:
                    if attempt < 2:
                        self.logger.warning(f"⚠️ Попытка {attempt + 1} для {ex_name} не удалась, повтор через 5 сек...")
                        await asyncio.sleep(5)
                    else:
                        self.exchanges_online[ex_name] = False
                        self.logger.error(f"❌ Ошибка инициализации {ex_name}: {e}")
                    if ex_name in self.exchanges:
                        try:
                            await self.exchanges[ex_name].close()
                            del self.exchanges[ex_name]
                        except:
                            pass

    async def _check_exchanges_online(self) -> None:
        for ex_name, exchange in self.exchanges.items():
            try:
                await exchange.fetch_time()
                self.exchanges_online[ex_name] = True
            except:
                self.exchanges_online[ex_name] = False

    async def shutdown(self) -> None:
        self.logger.info("🛑 Завершение работы бота...")
        self.is_running = False
        
        self._save_open_positions()

        for ex in self.exchanges.values():
            await ex.close()

        if self.metascalp_session:
            await self.metascalp_session.close()

        self.logger.info("✅ Бот остановлен")

    # ========================================================================
    # Белый список и Fallback
    # ========================================================================

    def _load_whitelist(self) -> Set[str]:
        whitelist_file = self.config.get('whitelist_file', 'whitelist.txt')
        whitelist = set()

        try:
            path = Path(whitelist_file)
            if path.exists():
                mtime = path.stat().st_mtime

                if mtime != self.whitelist_mtime:
                    with open(path, 'r') as f:
                        for line in f:
                            symbol = line.strip()
                            if symbol:
                                whitelist.add(symbol)

                    self.whitelist_mtime = mtime
                    self.logger.info(f"📋 Загружен белый список: {len(whitelist)} инструментов")

                    age_hours = (time.time() - mtime) / 3600
                    if age_hours > 25:
                        self.logger.warning(f"⚠️ Белый список устарел ({age_hours:.1f} часов)")

                    return whitelist
        except Exception as e:
            self.logger.error(f"❌ Ошибка загрузки белого списка: {e}")

        return whitelist

    async def _get_fallback_symbols(self) -> Set[str]:
        symbols = set()
        active = set(self.config.get('active_exchanges', []))
        
        if len(active) < 1:
            self.logger.warning("⚠️ Fallback: нет активных бирж в конфиге")
            return symbols

        fallback_priority = self.config.get('fallback_priority', [])
        
        selected_ex = None
        
        for ex in fallback_priority:
            if ex in active and ex in self.exchanges:
                if hasattr(self.exchanges[ex], 'markets') and self.exchanges[ex].markets:
                    selected_ex = ex
                    self.logger.debug(f"📋 Fallback: выбрана приоритетная биржа {ex}")
                    break
        
        if not selected_ex:
            for ex in active:
                if ex in self.exchanges:
                    if hasattr(self.exchanges[ex], 'markets') and self.exchanges[ex].markets:
                        selected_ex = ex
                        self.logger.debug(f"📋 Fallback: приоритетные биржи недоступны, выбрана {ex}")
                        break
        
        if not selected_ex:
            self.logger.warning("⚠️ Fallback: нет доступных бирж с загруженными рынками")
            self.logger.info(f"   Активные биржи: {list(active)}")
            self.logger.info(f"   Инициализированные: {list(self.exchanges.keys())}")
            return symbols

        try:
            count = 0
            for symbol, market in self.exchanges[selected_ex].markets.items():
                if symbol.endswith('/USDT') and market.get('active', False):
                    base = symbol.split('/')[0]
                    symbols.add(base)
                    count += 1
            
            full_symbols = {f"{s}/USDT:USDT" for s in symbols}
            
            if self.scan_count % 10 == 0 or self.scan_count == 1:
                self.logger.info(f"📋 Fallback: биржа {selected_ex} → {len(full_symbols)} инструментов")
            else:
                self.logger.debug(f"📋 Fallback: биржа {selected_ex} → {len(full_symbols)} инструментов")
            
            if len(full_symbols) == 0:
                self.logger.warning(f"⚠️ Fallback: биржа {selected_ex} не вернула ни одной активной USDT-пары!")
                
            return full_symbols
            
        except Exception as e:
            self.logger.error(f"❌ Fallback: ошибка получения рынков с {selected_ex}: {e}")
            return symbols

    # ========================================================================
    # Комиссии и ликвидность
    # ========================================================================

    async def _get_trading_fees(self, exchange_name: str, symbol: str, is_spot: bool) -> Optional[float]:
        cache = self.spot_fees_cache if is_spot else self.futures_fees_cache
        if exchange_name in cache and symbol in cache[exchange_name]:
            return cache[exchange_name][symbol]

        exchange = self.exchanges.get(exchange_name)
        if not exchange:
            return None

        fee = None
        if exchange.has.get('fetchTradingFees'):
            try:
                fees = await exchange.fetch_trading_fees()
                if symbol in fees:
                    fee = fees[symbol].get('taker') or fees[symbol].get('maker')
            except:
                pass

        if fee is None:
            try:
                market = exchange.market(symbol)
                fee = market.get('taker') or market.get('maker')
            except:
                pass

        if fee is not None:
            if exchange_name not in cache:
                cache[exchange_name] = {}
            cache[exchange_name][symbol] = fee
            return fee

        return self.manual_spot_fee_pct / 100.0 if is_spot else self.manual_futures_fee_pct / 100.0

    async def _check_liquidity_filters(
        self, 
        spot_exchange: str, 
        perp_exchange: str, 
        symbol: str
    ) -> Tuple[bool, float, float, float, float]:
        spot_ex = self.exchanges.get(spot_exchange)
        perp_ex = self.exchanges.get(perp_exchange)

        if not spot_ex or not perp_ex:
            return False, 0, 0, 0, 0

        try:
            ex_symbol = symbol
            if spot_exchange == 'binance' and not symbol.endswith('USDT'):
                ex_symbol = f"{symbol}/USDT:USDT"

            spot_ticker_task = spot_ex.fetch_ticker(ex_symbol.replace(':USDT', ''))
            perp_ticker_task = perp_ex.fetch_ticker(ex_symbol)

            spot_ticker, perp_ticker = await asyncio.gather(spot_ticker_task, perp_ticker_task)

            spot_price = spot_ticker.get('last', 0)
            perp_price = perp_ticker.get('last', 0)
            volume_24h = spot_ticker.get('quoteVolume', 0) or 0

            if volume_24h < self.min_volume_24h_usdt:
                self.filtered_by_volume += 1
                return False, volume_24h, 0, spot_price, perp_price

            if spot_price > 0 and perp_price > 0:
                spread_pct = abs(perp_price - spot_price) / spot_price * 100
                if spread_pct > self.max_slippage_pct:
                    self.filtered_by_spread += 1
                    return False, volume_24h, spread_pct, spot_price, perp_price
            else:
                spread_pct = 0

            return True, volume_24h, spread_pct, spot_price, perp_price

        except:
            return False, 0, 0, 0, 0

    # ========================================================================
    # Сканирование
    # ========================================================================

    async def _fetch_funding_rate(self, exchange_name: str, symbol: str) -> Optional[Tuple[float, float]]:
        exchange = self.exchanges.get(exchange_name)
        if not exchange:
            return None

        try:
            ex_symbol = symbol
            if exchange_name == 'binance' and not symbol.endswith('USDT'):
                ex_symbol = f"{symbol}/USDT:USDT"

            ticker = await exchange.fetch_funding_rate(ex_symbol)
            rate = ticker.get('fundingRate', 0.0)
            next_time = ticker.get('fundingTimestamp', 0) / 1000

            return (rate, next_time)
        except:
            return None

    async def _scan_symbol(self, symbol: str, spot_ex: str, perp_ex: str) -> Optional[ArbitrageOpportunity]:
        passes, volume_24h, spread_pct, spot_price, perp_price = await self._check_liquidity_filters(
            spot_ex, perp_ex, symbol
        )
        if not passes:
            return None

        if self.config.get('check_trading_status', True):
            try:
                perp_market = self.exchanges[perp_ex].market(symbol)
                spot_market = self.exchanges[spot_ex].market(symbol.replace(':USDT', ''))
                if not perp_market.get('active', False) or not spot_market.get('active', False):
                    self.filtered_by_status += 1
                    return None
            except:
                pass

        result = await self._fetch_funding_rate(perp_ex, symbol)
        if result is None:
            return None

        funding_rate, next_funding_time = result

        if abs(funding_rate) < self.config.get('funding_rate_threshold', 0.0001):
            return None

        min_time = self.config.get('min_time_to_funding_minutes', 0)
        if min_time > 0 and next_funding_time:
            time_to_funding = next_funding_time - time.time()
            if time_to_funding < min_time * 60:
                self.filtered_by_time += 1
                self.logger.debug(f"⏰ {symbol} отфильтрован: до выплаты {time_to_funding/60:.0f} мин < {min_time} мин")
                return None

        if funding_rate > 0:
            expected_profit_bps = funding_rate * 10000
            direction = "LONG_SPOT_SHORT_PERP"
        else:
            expected_profit_bps = abs(funding_rate) * 10000
            direction = "SHORT_SPOT_LONG_PERP"

        if direction == "SHORT_SPOT_LONG_PERP" and not self.config.get('margin_enabled', False):
            self.filtered_by_margin += 1
            return None

        spot_fee_pct = 0.0
        perp_fee_pct = 0.0
        net_profit_bps = expected_profit_bps

        if self.config.get('deduct_fees_from_profit', True):
            spot_fee_rate = await self._get_trading_fees(spot_ex, symbol, is_spot=True)
            perp_fee_rate = await self._get_trading_fees(perp_ex, symbol, is_spot=False)

            if spot_fee_rate is not None and perp_fee_rate is not None:
                spot_fee_pct = spot_fee_rate * 100
                perp_fee_pct = perp_fee_rate * 100
                total_fee_percent = (spot_fee_rate + perp_fee_rate) * 2 * 100
                net_profit_bps = expected_profit_bps - (total_fee_percent * 100)

                min_profit = self.config.get('min_profit_bps', 10)
                if net_profit_bps < min_profit:
                    self.filtered_by_fees += 1
                    return None

        return ArbitrageOpportunity(
            timestamp=time.time(),
            symbol=symbol,
            spot_exchange=spot_ex,
            perp_exchange=perp_ex,
            funding_rate=funding_rate,
            expected_profit_bps=expected_profit_bps,
            spot_price=spot_price,
            perp_price=perp_price,
            direction=direction,
            next_funding_time=next_funding_time,
            volume_24h_usdt=volume_24h,
            spread_pct=spread_pct,
            spot_fee_pct=spot_fee_pct,
            perp_fee_pct=perp_fee_pct,
            net_profit_bps=net_profit_bps
        )

    async def _scan_all_opportunities(self, symbols: Set[str]) -> List[ArbitrageOpportunity]:
        tasks = []
        active_exchanges = set(self.config.get('active_exchanges', []))

        for symbol in symbols:
            for pair in self.config.get('exchange_pairs', []):
                spot_ex = pair['spot']
                perp_ex = pair['perp']

                if spot_ex not in active_exchanges or perp_ex not in active_exchanges:
                    continue

                if not self.is_test_mode:
                    if spot_ex not in self.metascalp_connections or 'spot_id' not in self.metascalp_connections[spot_ex]:
                        continue
                    if perp_ex not in self.metascalp_connections or 'perp_id' not in self.metascalp_connections[perp_ex]:
                        continue

                if spot_ex in self.exchanges and perp_ex in self.exchanges:
                    tasks.append(self._scan_symbol(symbol, spot_ex, perp_ex))

        results = await asyncio.gather(*tasks, return_exceptions=True)

        opportunities = []
        for r in results:
            if isinstance(r, ArbitrageOpportunity):
                opportunities.append(r)

        return opportunities

    # ========================================================================
    # Условия входа и выхода
    # ========================================================================

    def should_buy_spot_short_perp(self, opp: ArbitrageOpportunity) -> bool:
        is_profitable = opp.net_profit_bps >= self.config.get('min_profit_bps', 10)
        is_repeat = self.last_strategy_action == StrategyAction.BUY_SPOT_SHORT_PERP
        correct_direction = opp.funding_rate > 0
        return is_profitable and not is_repeat and correct_direction

    def should_sell_spot_long_perp(self, opp: ArbitrageOpportunity) -> bool:
        if not self.config.get('margin_enabled', False):
            return False
        is_profitable = opp.net_profit_bps >= self.config.get('min_profit_bps', 10)
        is_repeat = self.last_strategy_action == StrategyAction.SELL_SPOT_LONG_PERP
        correct_direction = opp.funding_rate < 0
        return is_profitable and not is_repeat and correct_direction

    async def can_buy_spot_short_perp(self, opp: ArbitrageOpportunity) -> bool:
        if self.is_test_mode:
            return True

        spot_conn_id = self.metascalp_connections.get(opp.spot_exchange, {}).get('spot_id')
        perp_conn_id = self.metascalp_connections.get(opp.perp_exchange, {}).get('perp_id')

        if not spot_conn_id or not perp_conn_id:
            self.logger.debug(f"❌ Нет ID подключений для {opp.spot_exchange} или {opp.perp_exchange}")
            return False

        spot_balance = self.metascalp_balances.get(spot_conn_id, 0)
        perp_balance = self.metascalp_balances.get(perp_conn_id, 0)

        required = self.base_order_amount
        
        if spot_balance < required:
            self.logger.info(f"❌ Недостаточно баланса на споте {opp.spot_exchange}: {spot_balance:.2f} < {required:.2f} USDT")
            return False
        
        if perp_balance < required * 0.1:
            self.logger.info(f"❌ Недостаточно маржи на перпе {opp.perp_exchange}: {perp_balance:.2f} < {required * 0.1:.2f} USDT")
            return False
        
        return True

    async def can_sell_spot_long_perp(self, opp: ArbitrageOpportunity) -> bool:
        if self.is_test_mode:
            return True

        spot_conn_id = self.metascalp_connections.get(opp.spot_exchange, {}).get('spot_id')
        perp_conn_id = self.metascalp_connections.get(opp.perp_exchange, {}).get('perp_id')

        if not spot_conn_id or not perp_conn_id:
            self.logger.debug(f"❌ Нет ID подключений для {opp.spot_exchange} или {opp.perp_exchange}")
            return False

        spot_balance = self.metascalp_balances.get(spot_conn_id, 0)
        perp_balance = self.metascalp_balances.get(perp_conn_id, 0)

        required = self.base_order_amount
        
        if spot_balance < required:
            self.logger.info(f"❌ Недостаточно баланса на споте {opp.spot_exchange}: {spot_balance:.2f} < {required:.2f} USDT")
            return False
        
        if perp_balance < required * 0.1:
            self.logger.info(f"❌ Недостаточно маржи на перпе {opp.perp_exchange}: {perp_balance:.2f} < {required * 0.1:.2f} USDT")
            return False
        
        return True

    async def _check_close_condition(self, pos: Position, current_rate: float) -> Tuple[bool, Optional[ExitReason]]:
        """Проверка условия закрытия с уже известной ставкой"""
        entry_rate = pos.entry_funding_rate
        if (entry_rate > 0 and current_rate < 0) or (entry_rate < 0 and current_rate > 0):
            self.logger.info(f"🔄 Ставка сменила знак для {pos.symbol}: {entry_rate*100:.4f}% → {current_rate*100:.4f}%")
            return True, ExitReason.FUNDING_RATE_SIGN_CHANGED

        max_age = self.config.get('max_position_age_hours', 24) * 3600
        position_age = self.current_timestamp - pos.entry_time
        if position_age > max_age:
            self.logger.info(f"⏱️ Достигнуто максимальное время удержания для {pos.symbol}")
            return True, ExitReason.MAX_POSITION_AGE

        return False, None

    # ========================================================================
    # Расчёт PnL
    # ========================================================================

    async def _calculate_simulated_pnl(self, pos: Position) -> float:
        result = await self._fetch_funding_rate(pos.perp_exchange, pos.symbol)

        if not result:
            return 0.0

        current_rate, _ = result

        spot_fee_rate = await self._get_trading_fees(pos.spot_exchange, pos.symbol, is_spot=True) or 0.001
        perp_fee_rate = await self._get_trading_fees(pos.perp_exchange, pos.symbol, is_spot=False) or 0.0005

        holding_hours = (self.current_timestamp - pos.entry_time) / 3600

        avg_rate = (abs(pos.entry_funding_rate) + abs(current_rate)) / 2
        funding_profit = pos.size_usdt * avg_rate * (holding_hours / 8)

        total_fee = pos.size_usdt * (spot_fee_rate + perp_fee_rate) * 2

        net_pnl = funding_profit - total_fee

        pos.spot_entry_fee = pos.size_usdt * spot_fee_rate
        pos.perp_entry_fee = pos.size_usdt * perp_fee_rate
        pos.spot_exit_fee = pos.size_usdt * spot_fee_rate
        pos.perp_exit_fee = pos.size_usdt * perp_fee_rate

        return net_pnl

    async def _get_real_fees_from_metascalp(self, connection_id: int, order_id: str) -> float:
        try:
            async with self.metascalp_session.get(
                f"http://127.0.0.1:{self.metascalp_port}/api/connections/{connection_id}/orders"
            ) as resp:
                if resp.status != 200:
                    return 0.0
                data = await resp.json()
                orders = data.get('Orders', [])
                for order in orders:
                    if order.get('ClientId') == order_id or str(order.get('Id')) == order_id:
                        return float(order.get('Fee', 0))
            return 0.0
        except:
            return 0.0

    async def _get_real_funding_payments(self, exchange: str, symbol: str, since: float) -> float:
        try:
            ex = self.exchanges.get(exchange)
            if not ex:
                return 0.0

            funding_history = await ex.fetch_funding_history(symbol, since=int(since * 1000))

            total_funding = 0.0
            for payment in funding_history:
                total_funding += payment.get('amount', 0)

            return total_funding
        except:
            result = await self._fetch_funding_rate(exchange, symbol)
            if result:
                current_rate, _ = result
                avg_rate = (abs(self.position.entry_funding_rate) + abs(current_rate)) / 2
                holding_hours = (self.current_timestamp - since) / 3600
                return self.position.size_usdt * avg_rate * (holding_hours / 8)
            return 0.0

    async def _calculate_real_pnl(self, pos: Position) -> float:
        spot_entry_fee = 0.0
        perp_entry_fee = 0.0

        if pos.spot_order_id:
            spot_conn_id = self.metascalp_connections[pos.spot_exchange]['spot_id']
            spot_entry_fee = await self._get_real_fees_from_metascalp(spot_conn_id, pos.spot_order_id)

        if pos.perp_order_id:
            perp_conn_id = self.metascalp_connections[pos.perp_exchange]['perp_id']
            perp_entry_fee = await self._get_real_fees_from_metascalp(perp_conn_id, pos.perp_order_id)

        pos.spot_entry_fee = spot_entry_fee
        pos.perp_entry_fee = perp_entry_fee

        actual_funding = await self._get_real_funding_payments(
            pos.perp_exchange,
            pos.symbol,
            pos.entry_time
        )

        total_pnl = actual_funding - spot_entry_fee - perp_entry_fee

        if hasattr(pos, 'spot_exit_fee'):
            total_pnl -= pos.spot_exit_fee
        if hasattr(pos, 'perp_exit_fee'):
            total_pnl -= pos.perp_exit_fee

        return total_pnl

    # ========================================================================
    # Исполнение сделок
    # ========================================================================

    async def execute_buy_spot_short_perp(self, opp: ArbitrageOpportunity) -> bool:
        self.logger.info(f"📈 LONG SPOT + SHORT PERP: {opp.symbol} (прибыль: {opp.net_profit_bps:.1f} bps)")

        if self.is_test_mode:
            pos = Position(
                symbol=opp.symbol,
                spot_exchange=opp.spot_exchange,
                perp_exchange=opp.perp_exchange,
                direction='BUY_SPOT_SHORT_PERP',
                entry_time=self.current_timestamp,
                entry_funding_rate=opp.funding_rate,
                size_usdt=self.base_order_amount,
                spot_filled=True,
                perp_filled=True,
                next_funding_time=opp.next_funding_time,
                leverage=self.leverage
            )
            self.positions.append(pos)
            self._save_open_positions()
            self._last_current_rates[opp.symbol] = opp.funding_rate
            self.last_strategy_action = StrategyAction.BUY_SPOT_SHORT_PERP
            self.logger.info(f"🧪 [ТЕСТ] Позиция симулирована (всего открыто: {len(self.active_positions)})")
            return True
        else:
            return await self._execute_real_buy_spot_short_perp(opp)

    async def _execute_real_buy_spot_short_perp(self, opp: ArbitrageOpportunity) -> bool:
        try:
            spot_conn_id = self.metascalp_connections[opp.spot_exchange]['spot_id']
            perp_conn_id = self.metascalp_connections[opp.perp_exchange]['perp_id']

            clean_symbol = opp.symbol.replace('/USDT:USDT', 'USDT').replace('/USDT', 'USDT')

            spot_size = self.base_order_amount / opp.spot_price if opp.spot_price > 0 else self.base_order_amount / 100
            perp_size = self.base_order_amount / opp.perp_price if opp.perp_price > 0 else self.base_order_amount / 100

            spot_payload = {"Ticker": clean_symbol, "Side": 1, "Type": 4, "Size": spot_size, "ReduceOnly": False}
            perp_payload = {"Ticker": clean_symbol, "Side": 2, "Type": 4, "Size": perp_size, "ReduceOnly": False}

            async with self.metascalp_session.post(
                f"http://127.0.0.1:{self.metascalp_port}/api/connections/{spot_conn_id}/orders",
                json=spot_payload
            ) as spot_resp:
                spot_result = await spot_resp.json()

            async with self.metascalp_session.post(
                f"http://127.0.0.1:{self.metascalp_port}/api/connections/{perp_conn_id}/orders",
                json=perp_payload
            ) as perp_resp:
                perp_result = await perp_resp.json()

            if spot_result.get('Status') == 'ok' and perp_result.get('Status') == 'ok':
                pos = Position(
                    symbol=opp.symbol,
                    spot_exchange=opp.spot_exchange,
                    perp_exchange=opp.perp_exchange,
                    direction='BUY_SPOT_SHORT_PERP',
                    entry_time=self.current_timestamp,
                    entry_funding_rate=opp.funding_rate,
                    size_usdt=self.base_order_amount,
                    spot_order_id=spot_result.get('ClientId'),
                    perp_order_id=perp_result.get('ClientId'),
                    spot_filled=False,
                    perp_filled=False,
                    next_funding_time=opp.next_funding_time,
                    leverage=self.leverage
                )
                self.positions.append(pos)
                self._save_open_positions()
                self._last_current_rates[opp.symbol] = opp.funding_rate
                self.last_strategy_action = StrategyAction.BUY_SPOT_SHORT_PERP
                self.logger.info(f"✅ Ордера отправлены в MetaScalp (всего открыто: {len(self.active_positions)})")
                return True
            else:
                self.logger.error(f"❌ Ошибка отправки ордеров")
                return False
        except Exception as e:
            self.logger.error(f"❌ Ошибка исполнения: {e}")
            return False

    async def execute_sell_spot_long_perp(self, opp: ArbitrageOpportunity) -> bool:
        self.logger.info(f"📉 SHORT SPOT + LONG PERP: {opp.symbol} (прибыль: {opp.net_profit_bps:.1f} bps)")

        if self.is_test_mode:
            pos = Position(
                symbol=opp.symbol,
                spot_exchange=opp.spot_exchange,
                perp_exchange=opp.perp_exchange,
                direction='SELL_SPOT_LONG_PERP',
                entry_time=self.current_timestamp,
                entry_funding_rate=opp.funding_rate,
                size_usdt=self.base_order_amount,
                spot_filled=True,
                perp_filled=True,
                next_funding_time=opp.next_funding_time,
                leverage=self.leverage
            )
            self.positions.append(pos)
            self._save_open_positions()
            self._last_current_rates[opp.symbol] = opp.funding_rate
            self.last_strategy_action = StrategyAction.SELL_SPOT_LONG_PERP
            self.logger.info(f"🧪 [ТЕСТ] Позиция симулирована (всего открыто: {len(self.active_positions)})")
            return True
        else:
            return await self._execute_real_sell_spot_long_perp(opp)

    async def _execute_real_sell_spot_long_perp(self, opp: ArbitrageOpportunity) -> bool:
        try:
            spot_conn_id = self.metascalp_connections[opp.spot_exchange]['spot_id']
            perp_conn_id = self.metascalp_connections[opp.perp_exchange]['perp_id']

            clean_symbol = opp.symbol.replace('/USDT:USDT', 'USDT').replace('/USDT', 'USDT')

            spot_size = self.base_order_amount / opp.spot_price if opp.spot_price > 0 else self.base_order_amount / 100
            perp_size = self.base_order_amount / opp.perp_price if opp.perp_price > 0 else self.base_order_amount / 100

            spot_payload = {"Ticker": clean_symbol, "Side": 2, "Type": 4, "Size": spot_size, "ReduceOnly": False}
            perp_payload = {"Ticker": clean_symbol, "Side": 1, "Type": 4, "Size": perp_size, "ReduceOnly": False}

            async with self.metascalp_session.post(
                f"http://127.0.0.1:{self.metascalp_port}/api/connections/{spot_conn_id}/orders",
                json=spot_payload
            ) as spot_resp:
                spot_result = await spot_resp.json()

            async with self.metascalp_session.post(
                f"http://127.0.0.1:{self.metascalp_port}/api/connections/{perp_conn_id}/orders",
                json=perp_payload
            ) as perp_resp:
                perp_result = await perp_resp.json()

            if spot_result.get('Status') == 'ok' and perp_result.get('Status') == 'ok':
                pos = Position(
                    symbol=opp.symbol,
                    spot_exchange=opp.spot_exchange,
                    perp_exchange=opp.perp_exchange,
                    direction='SELL_SPOT_LONG_PERP',
                    entry_time=self.current_timestamp,
                    entry_funding_rate=opp.funding_rate,
                    size_usdt=self.base_order_amount,
                    spot_order_id=spot_result.get('ClientId'),
                    perp_order_id=perp_result.get('ClientId'),
                    spot_filled=False,
                    perp_filled=False,
                    next_funding_time=opp.next_funding_time,
                    leverage=self.leverage
                )
                self.positions.append(pos)
                self._save_open_positions()
                self._last_current_rates[opp.symbol] = opp.funding_rate
                self.last_strategy_action = StrategyAction.SELL_SPOT_LONG_PERP
                self.logger.info(f"✅ Ордера отправлены в MetaScalp (всего открыто: {len(self.active_positions)})")
                return True
            else:
                self.logger.error(f"❌ Ошибка отправки ордеров")
                return False
        except Exception as e:
            self.logger.error(f"❌ Ошибка исполнения: {e}")
            return False

    async def execute_close_position(self, pos: Position, exit_reason: ExitReason = ExitReason.NORMAL) -> bool:
        self.logger.info(f"🔒 Закрытие позиции: {pos.symbol}, причина: {exit_reason.value}")

        if self.is_test_mode:
            simulated_pnl = await self._calculate_simulated_pnl(pos)
            pos.close_time = self.current_timestamp
            pos.pnl = simulated_pnl
            pos.spot_filled = True
            pos.perp_filled = True
            pos.exit_reason = exit_reason.value

            trade = TradeRecord(
                id=datetime.now().strftime('%Y%m%d%H%M%S'),
                symbol=pos.symbol,
                direction=pos.direction,
                entry_time=pos.entry_time,
                exit_time=pos.close_time,
                size_usdt=pos.size_usdt,
                entry_funding_rate=pos.entry_funding_rate,
                pnl=pos.pnl or 0,
                pnl_pct=(pos.pnl or 0) / pos.size_usdt * 100 if pos.size_usdt else 0,
                leverage=pos.leverage,
                exit_reason=exit_reason.value,
                spot_entry_fee=pos.spot_entry_fee,
                perp_entry_fee=pos.perp_entry_fee,
                spot_exit_fee=pos.spot_exit_fee,
                perp_exit_fee=pos.perp_exit_fee
            )
            self._add_trade_record(trade)
            
            self.positions.remove(pos)
            self._save_open_positions()

            self.logger.info(f"🧪 [ТЕСТ] Позиция закрыта, PnL: {simulated_pnl:.4f} USDT")
            return True
        else:
            success = await self._execute_real_close_position(pos, exit_reason)
            if success:
                real_pnl = await self._calculate_real_pnl(pos)
                pos.pnl = real_pnl
                self.positions.remove(pos)
                self._save_open_positions()
                self.logger.info(f"💰 Реальный PnL: {real_pnl:.4f} USDT")
            return success

    async def _execute_real_close_position(self, pos: Position, exit_reason: ExitReason) -> bool:
        try:
            spot_conn_id = self.metascalp_connections[pos.spot_exchange]['spot_id']
            perp_conn_id = self.metascalp_connections[pos.perp_exchange]['perp_id']

            clean_symbol = pos.symbol.replace('/USDT:USDT', 'USDT').replace('/USDT', 'USDT')

            if pos.direction == 'BUY_SPOT_SHORT_PERP':
                spot_side = 2
                perp_side = 1
            else:
                spot_side = 1
                perp_side = 2

            spot_size = pos.size_usdt / 100
            perp_size = pos.size_usdt / 100

            spot_payload = {"Ticker": clean_symbol, "Side": spot_side, "Type": 4, "Size": spot_size, "ReduceOnly": True}
            perp_payload = {"Ticker": clean_symbol, "Side": perp_side, "Type": 4, "Size": perp_size, "ReduceOnly": True}

            async with self.metascalp_session.post(
                f"http://127.0.0.1:{self.metascalp_port}/api/connections/{spot_conn_id}/orders",
                json=spot_payload
            ) as spot_resp:
                spot_result = await spot_resp.json()

            async with self.metascalp_session.post(
                f"http://127.0.0.1:{self.metascalp_port}/api/connections/{perp_conn_id}/orders",
                json=perp_payload
            ) as perp_resp:
                perp_result = await perp_resp.json()

            if spot_result.get('Status') == 'ok' and perp_result.get('Status') == 'ok':
                pos.close_time = self.current_timestamp
                pos.exit_reason = exit_reason.value
                pos.spot_filled = False
                pos.perp_filled = False
                self.logger.info(f"✅ Ордера на закрытие отправлены")
                return True
            else:
                self.logger.error(f"❌ Ошибка закрытия")
                return False
        except Exception as e:
            self.logger.error(f"❌ Ошибка закрытия: {e}")
            return False

    # ========================================================================
    # Основной цикл (ОПТИМИЗИРОВАН)
    # ========================================================================

    async def on_tick(self, opportunities: List[ArbitrageOpportunity]) -> None:
        # Обновляем ставки для ВСЕХ активных позиций
        for pos in self.active_positions:
            result = await self._fetch_funding_rate(pos.perp_exchange, pos.symbol)
            if result:
                current_rate, _ = result
                self._last_current_rates[pos.symbol] = current_rate
                self.logger.info(f"📊 on_tick: обновлена ставка для {pos.symbol}: {current_rate*100:.4f}%")
            else:
                self.logger.warning(f"❌ on_tick: не удалось получить ставку для {pos.symbol}")
        
        # Проверяем условия закрытия
        for pos in self.active_positions[:]:
            current_rate = self._last_current_rates.get(pos.symbol)
            self.logger.info(f"🔍 Проверка закрытия для {pos.symbol}: current_rate={current_rate}, entry_rate={pos.entry_funding_rate}")
            if current_rate is not None:
                should_close, reason = await self._check_close_condition(pos, current_rate)
                if should_close:
                    self.logger.info(f"🚨 Закрываем {pos.symbol}, причина: {reason}")
                    await self.execute_close_position(pos, reason or ExitReason.NORMAL)
            else:
                self.logger.warning(f"⚠️ Нет актуальной ставки для {pos.symbol}, пропускаем проверку закрытия")

        # Если достигнут лимит — не открываем новые
        if not self.can_open_new_position():
            return

        if self.current_timestamp < self.next_arbitrage_opening_ts:
            return

        # Ищем лучшую возможность, которая ещё не открыта
        for opp in opportunities:
            if not self.can_open_new_position():
                break

            if self.is_position_already_open(opp.symbol, opp.spot_exchange, opp.perp_exchange):
                continue

            if self.should_buy_spot_short_perp(opp):
                if await self.can_buy_spot_short_perp(opp):
                    await self.execute_buy_spot_short_perp(opp)
            elif self.should_sell_spot_long_perp(opp):
                if await self.can_sell_spot_long_perp(opp):
                    await self.execute_sell_spot_long_perp(opp)

    async def _scan_iteration(self) -> None:
        self.scan_count += 1

        if self.scan_count % 10 == 0:
            await self._check_exchanges_online()

        if self.scan_count % 720 == 0:
            self.filtered_by_volume = 0
            self.filtered_by_spread = 0
            self.filtered_by_margin = 0
            self.filtered_by_time = 0
            self.filtered_by_status = 0
            self.filtered_by_fees = 0

        await self._check_metascalp_connection()

        whitelist = self._load_whitelist()
        if not whitelist:
            whitelist = await self._get_fallback_symbols()
        else:
            self.whitelist = whitelist

        self.last_scan_time = self.current_timestamp

        opportunities = []
        if whitelist:
            opportunities = await self._scan_all_opportunities(whitelist)
            opportunities.sort(key=lambda x: x.net_profit_bps, reverse=True)

            self.current_opportunities = opportunities[:self.max_current_opportunities]

            for opp in opportunities[:self.max_recent_opportunities]:
                self.recent_opportunities.append(opp)

            if opportunities:
                self.opportunities_found += len(opportunities)

                for i, opp in enumerate(opportunities[:5]):
                    self.signal_logger.info(
                        f"#{i+1} | {opp.symbol} | {opp.spot_exchange}/{opp.perp_exchange} | "
                        f"Ставка: {opp.funding_rate*100:.4f}% | Прибыль: {opp.net_profit_bps:.1f} bps | "
                        f"Объём: {opp.volume_24h_usdt:,.0f} USDT | Направление: {opp.direction}"
                    )
        else:
            self.current_opportunities = []

        # ВАЖНО: ВСЕГДА вызываем on_tick, даже если нет новых сигналов!
        await self.on_tick(opportunities)

    async def scan_loop(self) -> None:
        while self.is_running:
            try:
                await self._scan_iteration()
            except Exception as e:
                self.logger.error(f"❌ Ошибка в цикле: {e}", exc_info=True)

            await asyncio.sleep(self.scan_interval)

    async def run(self) -> None:
        await self.initialize()
        self.scan_task = asyncio.create_task(self.scan_loop())
        self.logger.info(f"🚀 Бот запущен, интервал сканирования: {self.scan_interval} сек")


# ============================================================================
# FastAPI приложение с lifespan
# ============================================================================

@asynccontextmanager
async def lifespan(app: FastAPI):
    global bot
    bot = FundingArbitrageBot("config.yaml")
    await bot.initialize()
    asyncio.create_task(bot.scan_loop())
    print(f"🚀 {BOT_NAME} v{__version__} запущен")
    yield
    if bot:
        await bot.shutdown()

app = FastAPI(title=f"{BOT_NAME} API", version=__version__, lifespan=lifespan)
bot: Optional[FundingArbitrageBot] = None


@app.get("/", response_class=HTMLResponse)
async def get_dashboard():
    dashboard_path = Path(__file__).parent / "dashboard.html"
    if dashboard_path.exists():
        return dashboard_path.read_text(encoding='utf-8')
    return "<h1>Dashboard not found</h1>"


@app.get("/api/status")
async def get_status():
    if not bot:
        raise HTTPException(status_code=503, detail="Bot not ready")
    return bot.get_status()


@app.post("/api/config")
async def update_config(updates: Dict[str, Any]):
    if not bot:
        raise HTTPException(status_code=503, detail="Bot not ready")
    bot.update_config(updates)
    return {"status": "ok", "updated": updates}


@app.post("/api/exchanges")
async def update_active_exchanges(data: Dict[str, List[str]]):
    if not bot:
        raise HTTPException(status_code=503, detail="Bot not ready")
    exchanges = data.get('exchanges', [])
    bot.update_active_exchanges(exchanges)
    return {"status": "ok", "active_exchanges": exchanges}


@app.get("/api/opportunities")
async def get_opportunities():
    if not bot:
        raise HTTPException(status_code=503, detail="Bot not ready")
    return [o.to_dict() for o in bot.current_opportunities[:20]]


@app.get("/api/trades")
async def get_trades():
    if not bot:
        raise HTTPException(status_code=503, detail="Bot not ready")
    return [t.to_dict() for t in bot.trades_history]


@app.post("/api/force_scan")
async def force_scan():
    if not bot:
        raise HTTPException(status_code=503, detail="Bot not ready")
    await bot._scan_iteration()
    return {"status": "ok"}


@app.post("/api/positions/close")
async def close_position_manually(data: Dict[str, str]):
    if not bot:
        raise HTTPException(status_code=503, detail="Bot not ready")
    
    position_id = data.get('position_id')
    if not position_id:
        raise HTTPException(status_code=400, detail="position_id is required")
    
    pos = bot.find_position_by_id(position_id)
    if not pos:
        raise HTTPException(status_code=404, detail="Position not found")
    
    asyncio.create_task(bot.execute_close_position(pos, ExitReason.MANUAL))
    
    return {"status": "ok", "message": f"Position {pos.symbol} closing initiated"}


# ============================================================================
# Точка входа
# ============================================================================

def main():
    config = yaml.safe_load(Path("config.yaml").read_text())
    port = config.get('dashboard_port', 8000)
    host = config.get('dashboard_host', '127.0.0.1')

    print(f"🤖 {BOT_NAME} v{__version__}")
    print(f"📊 Дашборд доступен по адресу: http://{host}:{port}")

    uvicorn.run(app, host=host, port=port)


if __name__ == "__main__":
    main()