#!/usr/bin/env python3
"""
Funding Rate Arbitrage Scanner + Executor for MetaScalp
Version: 2.6.2
"""

import os
import sys
import json
import time
import logging
import asyncio
import re
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

__version__ = "2.6.2"
BOT_NAME = "Funding Arbitrage Bot"


# ============================================================================
# Конфигурация и структуры данных
# ============================================================================

class StrategyState(Enum):
    CLOSED = "closed"
    OPENING = "opening"
    OPENED = "opened"
    CLOSING = "closing"


class ConnectionState(Enum):
    DISCONNECTED = "disconnected"
    CONNECTING = "connecting"
    CONNECTED = "connected"
    RECONNECTING = "reconnecting"


class ExitReason(Enum):
    NORMAL = "normal"
    FUNDING_RATE_SIGN_CHANGED = "funding_rate_sign_changed"
    MAX_POSITION_AGE = "max_position_age"
    FIRST_FUNDING_PAID = "first_funding_paid"
    LIQUIDATION_RISK = "liquidation_risk"
    MANUAL = "manual"
    ERROR = "error"
    UNKNOWN = "unknown"

    def russian(self) -> str:
        names = {
            'normal': '✅ Штатно',
            'funding_rate_sign_changed': '🔄 Смена знака',
            'max_position_age': '⏱️ Таймаут',
            'first_funding_paid': '💰 Первая выплата',
            'liquidation_risk': '⚠️ Ликвидация',
            'manual': '👤 Вручную',
            'error': '❌ Ошибка',
            'unknown': '❓ Неизвестно',
        }
        return names.get(self.value, self.value)


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
    entry_perp_price: float = 0.0
    funding_payments_received: float = 0.0
    funding_payments_count: int = 0
    last_funding_time: Optional[float] = None
    close_in_progress: bool = False


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


@dataclass
class CachedInstrument:
    """Запись в кэше Уровня 0"""
    symbol: str
    spot_exchange: str
    perp_exchange: str
    funding_rate: float = 0.0
    preliminary_profit_bps: float = 0.0

    def to_dict(self) -> dict:
        return asdict(self)


# ============================================================================
# Главный класс бота
# ============================================================================

class FundingArbitrageBot:
    """Асинхронный бот для фандингового арбитража с поддержкой множественных позиций"""

    def __init__(self, config_path: str = "config.yaml"):
        self.config_path = config_path
        self.config = self._load_config(config_path)
        self._setup_logging()

        # === Время старта ===
        self.start_time: float = time.time()

        # === Состояние стратегии ===
        self.strategy_state = StrategyState.CLOSED
        self.positions: List[Position] = []
        self._last_current_rates: Dict[str, float] = {}
        self._last_perp_prices: Dict[str, float] = {}
        self._last_signal_log_set: Set[str] = set()
        self._opening_symbols: Set[str] = set()

        # === Тайминги ===
        self.in_flight_state_start_ts: float = 0
        self.in_flight_state_tolerance: int = self.config.get('in_flight_state_tolerance', 60)
        self.opened_state_start_ts: float = 0
        self.opened_state_tolerance: int = self.config.get('opened_state_tolerance', 7200)
        self.next_arbitrage_opening_ts: float = 0
        self.next_arbitrage_opening_delay: int = self.config.get('next_arbitrage_opening_delay', 10)
        self.max_positions_per_side: int = self.config.get('max_positions_per_side', 5)

        # === MetaScalp ===
        self.metascalp_port: Optional[int] = None
        self.metascalp_version: str = "unknown"
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
        self.trading_enabled = self.config.get('trading_enabled', True)

        # === CCXT биржи ===
        self.exchanges: Dict[str, ccxt.Exchange] = {}
        self.exchanges_online: Dict[str, bool] = {}

        # === HTTP сессия ===
        self._http_session: Optional[aiohttp.ClientSession] = None

        # === Параметры ===
        self.base_order_amount = self.config.get('base_order_amount', 100.0)
        self.min_profit_bps = self.config.get('min_profit_bps', 10)
        self.funding_rate_threshold = self.config.get('funding_rate_threshold', 0.0001)
        self.scan_interval = self.config.get('scan_interval', 5)
        self.leverage = self.config.get('leverage', 3)
        self.margin_enabled = self.config.get('margin_enabled', False)
        self.min_volume_24h_usdt = self.config.get('min_volume_24h_usdt', 10000)
        self.max_slippage_pct = self.config.get('max_slippage_pct', 1.0)
        self.max_recent_opportunities = self.config.get('max_recent_opportunities', 5)
        self.max_current_opportunities = self.config.get('max_current_opportunities', 5)
        self.max_price_change_pct = self.config.get('max_price_change_pct', 15)

        # === Фильтры ===
        self.min_time_to_funding_minutes = self.config.get('min_time_to_funding_minutes', 0)
        self.check_trading_status = self.config.get('check_trading_status', True)
        self.deduct_fees_from_profit = self.config.get('deduct_fees_from_profit', True)
        self.manual_spot_fee_pct = self.config.get('manual_spot_fee_pct', 0.1)
        self.manual_futures_fee_pct = self.config.get('manual_futures_fee_pct', 0.05)

        # === Закрытие ===
        self.max_position_age_hours = self.config.get('max_position_age_hours', 24)
        self.post_funding_close_delay = self.config.get('post_funding_close_delay_minutes', 5)

        # === Оптимизация ===
        self.max_concurrent_requests = self.config.get('max_concurrent_requests', 20)
        self.max_concurrent_cache_requests = self.config.get('max_concurrent_cache_requests', 30)
        self.cache_rebuild_interval = self.config.get('cache_rebuild_interval_minutes', 30)
        self.normalize_symbols = self.config.get('normalize_symbols', True)
        self.cache_max_instruments = self.config.get('cache_max_instruments', 500)

        # === Кэш ===
        self.instrument_cache: List[CachedInstrument] = []
        self.cache_last_updated: float = 0
        self.cache_total_futures_found: int = 0
        self.cache_filtered_by_profit: int = 0
        self.cache_filtered_by_no_spot: int = 0
        self.cache_filtered_by_status: int = 0

        # === Кэш комиссий ===
        self.spot_fees_cache: Dict[str, Dict[str, float]] = {}
        self.futures_fees_cache: Dict[str, Dict[str, float]] = {}

        # === Данные для дашборда ===
        self.current_opportunities: List[ArbitrageOpportunity] = []
        self.recent_opportunities: deque = deque(maxlen=self.max_recent_opportunities)
        self.last_scan_time: float = 0
        self.trades_history: List[TradeRecord] = []
        self._load_trades_history()

        # === Файлы ===
        self.open_positions_file = self.config.get('open_positions_file', 'logs/open_positions.json')
        self.cache_file = self.config.get('cache_file', 'logs/instrument_cache.json')

        # === Статистика ===
        self.scan_count = 0
        self.opportunities_found = 0
        self.filtered_by_volume = 0
        self.filtered_by_spread = 0
        self.filtered_by_margin = 0
        self.filtered_by_time = 0
        self.filtered_by_status = 0
        self.filtered_by_fees = 0
        self.filtered_by_rate_threshold = 0
        self.filtered_by_symbol_mismatch = 0
        self.total_pnl = 0.0
        for trade in self.trades_history:
            self.total_pnl += trade.pnl

        # === Управление циклом ===
        self.is_running = True
        self.scan_task: Optional[asyncio.Task] = None

        # === Telegram Bot ===
        self.telegram_enabled = self.config.get('telegram_enabled', False)
        self.tg_manager = None

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
            'balance_update_interval': 30, 'max_positions_per_side': 5,
            'trading_enabled': True, 'max_price_change_pct': 15,
            'signal_log_file': 'logs/signal.log', 'open_positions_file': 'logs/open_positions.json',
            'cache_file': 'logs/instrument_cache.json',
            'max_position_age_hours': 24,
            'post_funding_close_delay_minutes': 5,
            'max_concurrent_requests': 20,
            'max_concurrent_cache_requests': 30,
            'cache_rebuild_interval_minutes': 30,
            'normalize_symbols': True,
            'cache_max_instruments': 500,
            'metascalp_connection_check_interval': 60,
            'telegram_enabled': False,
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
        for lib in ['telegram', 'httpx', 'httpcore', 'telegram.ext', 'telegram.vendor', 'apscheduler', 'uvicorn.access']:
            logging.getLogger(lib).setLevel(logging.WARNING)

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
        self.logger.info(f"📈 Маржинальная торговля: {'ВКЛЮЧЕНА' if self.margin_enabled else 'ВЫКЛЮЧЕНА'}")
        self.logger.info(f"🔢 Макс. позиций на сторону: {self.max_positions_per_side}")
        self.logger.info(f"🛡️ Защита от ликвидации: {self.max_price_change_pct}%")
        self.logger.info(f"⏰ Мин. время до выплаты: {self.min_time_to_funding_minutes} мин")
        self.logger.info(f"⏱️ Макс. время удержания: {self.max_position_age_hours}ч")
        self.logger.info(f"🔄 Перестроение кэша: каждые {self.cache_rebuild_interval} мин")
        self.logger.info(f"🔤 Нормализация тикеров: {'ВКЛЮЧЕНА' if self.normalize_symbols else 'ВЫКЛЮЧЕНА'}")
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

    def can_open_long_position(self) -> bool:
        count = sum(1 for p in self.active_positions if p.direction == 'BUY_SPOT_SHORT_PERP')
        return count < self.max_positions_per_side

    def can_open_short_position(self) -> bool:
        count = sum(1 for p in self.active_positions if p.direction == 'SELL_SPOT_LONG_PERP')
        return count < self.max_positions_per_side

    def is_position_already_open(self, symbol: str, spot_ex: str, perp_ex: str) -> bool:
        for p in self.active_positions:
            if p.symbol == symbol and p.spot_exchange == spot_ex and p.perp_exchange == perp_ex:
                return True
        return False

    def find_position_by_id(self, position_id: str) -> Optional[Position]:
        for pos in self.active_positions:
            pos_id = f"{pos.symbol}_{pos.spot_exchange}_{pos.perp_exchange}_{pos.entry_time}"
            if pos_id == position_id:
                return pos
        return None

    def get_position_estimated_pnl(self, pos: Position) -> float:
        if pos.close_time:
            return pos.pnl or 0.0

        received = pos.funding_payments_received
        current_rate = self._last_current_rates.get(pos.symbol, pos.entry_funding_rate)
        last_time = pos.last_funding_time or pos.entry_time
        hours_since_last = max(0, (self.current_timestamp - last_time) / 3600)
        pending = pos.size_usdt * abs(current_rate) * (hours_since_last / 8)
        entry_fees = pos.spot_entry_fee + pos.perp_entry_fee
        exit_fees = pos.spot_exit_fee + pos.perp_exit_fee

        return received + pending - entry_fees - exit_fees

    # ========================================================================
    # MetaScalp
    # ========================================================================

    async def _connect_metascalp(self) -> bool:
        self.metascalp_state = ConnectionState.CONNECTING
        port = await self._discover_metascalp_port()
        if not port:
            self.logger.warning("⚠️ MetaScalp не найден.")
            self.metascalp_state = ConnectionState.DISCONNECTED
            if not self.manual_test_mode:
                self.auto_test_mode = True
            return False
        self.metascalp_port = port
        if self.metascalp_session:
            await self.metascalp_session.close()
        self.metascalp_session = aiohttp.ClientSession()
        if self._http_session:
            await self._http_session.close()
        self._http_session = aiohttp.ClientSession()
        success = await self._fetch_connection_ids()
        if success:
            self.metascalp_state = ConnectionState.CONNECTED
            self.metascalp_reconnect_attempts = 0
            self.auto_test_mode = False
            self._log_metascalp_connections()
            self.last_balance_update = 0
            await self._update_metascalp_balances()
            return True
        else:
            self.metascalp_state = ConnectionState.DISCONNECTED
            if not self.manual_test_mode:
                self.auto_test_mode = True
            return False

    async def _discover_metascalp_port(self) -> Optional[int]:
        for port in range(17845, 17856):
            try:
                async with aiohttp.ClientSession() as session:
                    async with session.get(f"http://127.0.0.1:{port}/ping", timeout=aiohttp.ClientTimeout(total=1)) as resp:
                        if resp.status == 200:
                            data = await resp.json()
                            app_name = (data.get("App") or data.get("app") or "").lower()
                            if app_name == "metascalp":
                                version = data.get("Version") or data.get("version") or "unknown"
                                self.metascalp_version = version
                                self.logger.info(f"✅ MetaScalp найден на порту {port}, версия {version}")
                                return port
            except:
                continue
        return None

    async def _fetch_connection_ids(self) -> bool:
        if not self.metascalp_session:
            return False
        try:
            async with self.metascalp_session.get(f"http://127.0.0.1:{self.metascalp_port}/api/connections") as resp:
                if resp.status != 200:
                    return False
                data = await resp.json()
                connections = data.get('Connections', data.get('connections', []))
                self.metascalp_connections.clear()
                for conn in connections:
                    ex_name = conn['Exchange'].lower()
                    market_type = conn['MarketType']
                    conn_id = conn['Id']
                    conn_state = conn['State']
                    view_mode = conn.get('ViewMode', False)
                    if conn_state != 2:
                        continue
                    is_spot = market_type == 0
                    is_perp = market_type in (1, 2, 5)
                    if ex_name not in self.metascalp_connections:
                        self.metascalp_connections[ex_name] = {}
                    if is_spot:
                        self.metascalp_connections[ex_name]['spot_id'] = conn_id
                        self.metascalp_connections[ex_name]['spot_view_mode'] = view_mode
                    elif is_perp:
                        self.metascalp_connections[ex_name]['perp_id'] = conn_id
                        self.metascalp_connections[ex_name]['perp_view_mode'] = view_mode
                    spot_vm = self.metascalp_connections[ex_name].get('spot_view_mode', True)
                    perp_vm = self.metascalp_connections[ex_name].get('perp_view_mode', True)
                    self.metascalp_connections[ex_name]['view_mode'] = spot_vm and perp_vm
                return bool(self.metascalp_connections)
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

    async def _update_metascalp_balances(self) -> None:
        if not self.metascalp_session or self.metascalp_state != ConnectionState.CONNECTED:
            return
        now = time.time()
        if now - self.last_balance_update < self.balance_update_interval:
            return
        self.last_balance_update = now
        updated = 0
        for ex_name, conns in self.metascalp_connections.items():
            if conns.get('view_mode', False):
                continue
            for ct, ci in [('spot_id', conns.get('spot_id')), ('perp_id', conns.get('perp_id'))]:
                if ci:
                    try:
                        async with self.metascalp_session.get(f"http://127.0.0.1:{self.metascalp_port}/api/connections/{ci}/balance") as resp:
                            if resp.status == 200:
                                data = await resp.json()
                                for b in data.get('balances', data.get('Balances', [])):
                                    if b.get('Coin') == 'USDT':
                                        self.metascalp_balances[ci] = float(b.get('Free', 0))
                                        updated += 1
                                        break
                    except:
                        pass
        if updated:
            self.logger.info(f"✅ Обновлено балансов: {updated}")

    async def fetch_balances_direct(self, connection_id: int) -> Dict[str, float]:
        """Прямой запрос баланса для конкретного подключения"""
        try:
            async with self.metascalp_session.get(
                f"http://127.0.0.1:{self.metascalp_port}/api/connections/{connection_id}/balance"
            ) as resp:
                if resp.status != 200:
                    return {}
                data = await resp.json()
                result = {}
                for b in data.get('balances', data.get('Balances', [])):
                    result[b.get('Coin', '')] = float(b.get('Free', 0))
                return result
        except:
            return {}

    async def _check_metascalp_connection(self) -> None:
        now = time.time()
        if now - self.last_metascalp_check < self.config.get('metascalp_connection_check_interval', 60):
            return
        self.last_metascalp_check = now
        await self._update_metascalp_balances()
        if self.metascalp_state == ConnectionState.CONNECTED:
            try:
                async with self.metascalp_session.get(f"http://127.0.0.1:{self.metascalp_port}/ping", timeout=aiohttp.ClientTimeout(total=2)) as resp:
                    if resp.status != 200:
                        raise Exception("Ping failed")
            except:
                self.logger.warning("⚠️ Соединение с MetaScalp потеряно")
                self.metascalp_state = ConnectionState.DISCONNECTED
                if not self.manual_test_mode:
                    self.auto_test_mode = True
        elif self.metascalp_state == ConnectionState.DISCONNECTED:
            max_att = self.config.get('metascalp_max_reconnect_attempts', 10)
            if self.metascalp_reconnect_attempts < max_att:
                self.metascalp_reconnect_attempts += 1
                self.logger.info(f"🔄 Переподключение ({self.metascalp_reconnect_attempts}/{max_att})...")
                if await self._connect_metascalp():
                    self.logger.info("✅ Соединение восстановлено!")
                    self.auto_test_mode = False
            else:
                self.metascalp_reconnect_attempts = 0

    # ========================================================================
    # CCXT
    # ========================================================================

    async def _init_exchanges(self) -> None:
        active = set(self.config.get('active_exchanges', []))
        for ex_name in self.config['enabled_exchanges']:
            if ex_name not in active:
                continue
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
                    break
                except Exception as e:
                    if attempt < 2:
                        self.logger.warning(f"⚠️ Попытка {attempt+1} для {ex_name} не удалась, повтор...")
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

    async def initialize(self) -> None:
        await self._init_exchanges()
        await self._connect_metascalp()
        self._load_open_positions()
        await self._sync_positions_with_exchange()
        self._load_instrument_cache_from_file()

        if self.telegram_enabled:
            from telegram_bot import TelegramManager
            self.tg_manager = TelegramManager(self)
            if self.tg_manager.enabled:
                asyncio.create_task(self.tg_manager.start_bot())
                self.logger.info("📱 Telegram Bot запущен")

        for pos in self.positions:
            if not pos.close_time:
                result = await self._fetch_funding_rate(pos.perp_exchange, pos.symbol)
                if result:
                    self._last_current_rates[pos.symbol] = result[0]

    async def shutdown(self) -> None:
        self.logger.info("🛑 Завершение...")
        self.is_running = False
        self._save_open_positions()
        self._save_instrument_cache_to_file()
        if self.tg_manager:
            await self.tg_manager.stop_bot()
        for ex in self.exchanges.values():
            await ex.close()
        if self.metascalp_session:
            await self.metascalp_session.close()
        if self._http_session:
            await self._http_session.close()
        self.logger.info("✅ Бот остановлен")

    def _load_open_positions(self) -> None:
        try:
            path = Path(self.open_positions_file)
            if path.exists():
                with open(path, 'r') as f:
                    data = json.load(f)
                    for p in data:
                        p.setdefault('entry_perp_price', 0.0)
                        p.setdefault('funding_payments_received', 0.0)
                        p.setdefault('funding_payments_count', 0)
                        p.setdefault('last_funding_time', None)
                        p.setdefault('close_in_progress', False)
                        pos = Position(**p)
                        self.positions.append(pos)
                self.logger.info(f"📂 Загружено {len(self.positions)} открытых позиций из файла")
        except Exception as e:
            self.logger.error(f"❌ Ошибка загрузки открытых позиций: {e}")

    def _save_open_positions(self) -> None:
        try:
            path = Path(self.open_positions_file)
            path.parent.mkdir(parents=True, exist_ok=True)
            active = [asdict(p) for p in self.active_positions]
            with open(path, 'w') as f:
                json.dump(active, f, indent=2)
        except Exception as e:
            self.logger.error(f"❌ Ошибка сохранения открытых позиций: {e}")

    async def _check_perp_position_exists(self, pos: Position) -> bool:
        if pos.perp_exchange not in self.metascalp_connections:
            return False
        ci = self.metascalp_connections[pos.perp_exchange].get('perp_id')
        if not ci:
            return False
        try:
            async with self.metascalp_session.get(f"http://127.0.0.1:{self.metascalp_port}/api/connections/{ci}/positions") as resp:
                if resp.status != 200:
                    return False
                data = await resp.json()
                cs = pos.symbol.replace('/USDT:USDT', 'USDT').replace('/USDT', 'USDT')
                for rp in data.get('Positions', []):
                    if rp.get('Ticker') == cs:
                        if pos.direction == 'BUY_SPOT_SHORT_PERP' and rp.get('Side') == 2:
                            return True
                        if pos.direction == 'SELL_SPOT_LONG_PERP' and rp.get('Side') == 1:
                            return True
                return False
        except:
            return False

    async def _sync_positions_with_exchange(self) -> None:
        if self.is_test_mode:
            self.logger.info(f"🧪 Тестовый режим: {len(self.positions)} позиций")
            return
        self.logger.info("🔄 Синхронизация позиций...")
        valid = []
        for pos in self.positions:
            if await self._check_perp_position_exists(pos):
                valid.append(pos)
                self.logger.info(f"   ✅ {pos.symbol} подтверждена")
            else:
                # Не удаляем, просто предупреждаем
                self.logger.warning(f"   ⚠️ {pos.symbol} не найдена через API, но оставляем в списке")
                valid.append(pos)  # ← добавляем в valid вместо удаления
        self.positions = valid
        self._save_open_positions()

    # ========================================================================
    # Персистентность кэша
    # ========================================================================

    def _save_instrument_cache_to_file(self) -> None:
        try:
            path = Path(self.cache_file)
            path.parent.mkdir(parents=True, exist_ok=True)
            data = {
                'timestamp': self.cache_last_updated,
                'total_futures_found': self.cache_total_futures_found,
                'filtered_by_profit': self.cache_filtered_by_profit,
                'filtered_by_no_spot': self.cache_filtered_by_no_spot,
                'filtered_by_status': self.cache_filtered_by_status,
                'instruments': [item.to_dict() for item in self.instrument_cache]
            }
            with open(path, 'w') as f:
                json.dump(data, f, indent=2)
            self.logger.debug(f"💾 Кэш сохранён: {len(self.instrument_cache)} инструментов")
        except Exception as e:
            self.logger.error(f"❌ Ошибка сохранения кэша: {e}")

    def _load_instrument_cache_from_file(self) -> None:
        try:
            path = Path(self.cache_file)
            if not path.exists():
                self.logger.info("📂 Файл кэша не найден, будет перестроен")
                return
            with open(path, 'r') as f:
                data = json.load(f)
            ts = data.get('timestamp', 0)
            if ts < 1000000000:
                self.logger.info("📂 Кэш повреждён (timestamp=0), будет перестроен")
                return
            age_minutes = (time.time() - ts) / 60
            if age_minutes < self.cache_rebuild_interval:
                self.instrument_cache = [CachedInstrument(**item) for item in data['instruments']]
                self.cache_last_updated = ts
                self.cache_total_futures_found = data.get('total_futures_found', 0)
                self.cache_filtered_by_profit = data.get('filtered_by_profit', 0)
                self.cache_filtered_by_no_spot = data.get('filtered_by_no_spot', 0)
                self.cache_filtered_by_status = data.get('filtered_by_status', 0)
                self.logger.info(f"📂 Кэш загружен: {len(self.instrument_cache)} инструментов (возраст {age_minutes:.0f} мин)")
            else:
                self.logger.info(f"📂 Кэш устарел ({age_minutes:.0f} мин), будет перестроен")
        except Exception as e:
            self.logger.error(f"❌ Ошибка загрузки кэша: {e}")

    # ========================================================================
    # Прямые HTTP-запросы
    # ========================================================================

    async def _fetch_funding_rates_direct(self, ex_name: str) -> Optional[List[dict]]:
        if not self._http_session:
            self._http_session = aiohttp.ClientSession()

        endpoints = {
            'mexc': {
                'url': 'https://api.mexc.com/api/v1/contract/funding_rate',
                'result_key': 'data',
                'symbol_field': 'symbol',
                'rate_field': 'fundingRate',
                'time_field': 'nextSettleTime',
                'symbol_transform': lambda s: s.replace('_', '/') + ':USDT',
            },
            'kucoin': {
                'url': 'https://api-futures.kucoin.com/api/v1/contracts/active',
                'result_key': 'data',
                'symbol_field': 'symbol',
                'rate_field': 'fundingFeeRate',
                'time_field': 'nextFundingRateTime',
                'symbol_transform': lambda s: s,
            },
            'bitmart': {
                'url': 'https://api-cloud-v2.bitmart.com/contract/public/details',
                'result_key': 'data.symbols',
                'symbol_field': 'symbol',
                'rate_field': 'funding_rate',
                'time_field': 'funding_time',
                'symbol_transform': lambda s: s + '/USDT:USDT' if s.endswith('USDT') else s,
            },
        }

        cfg = endpoints.get(ex_name)
        if not cfg:
            return None

        try:
            async with self._http_session.get(cfg['url'], timeout=aiohttp.ClientTimeout(total=10)) as resp:
                if resp.status != 200:
                    return None
                data = await resp.json()

            items = data
            for key in cfg['result_key'].split('.'):
                if isinstance(items, dict):
                    items = items.get(key, [])
                else:
                    break

            if not isinstance(items, list):
                return None

            result = []
            for item in items:
                if not isinstance(item, dict):
                    continue
                raw_symbol = item.get(cfg['symbol_field'], '')
                if not raw_symbol:
                    continue
                symbol = cfg['symbol_transform'](raw_symbol)
                rate = item.get(cfg['rate_field'])
                if rate is None:
                    continue
                next_time = item.get(cfg['time_field'], 0)
                if next_time and next_time > 1000000000000:
                    next_time = next_time / 1000
                result.append({
                    'symbol': symbol,
                    'rate': float(rate),
                    'next_funding_time': next_time if next_time else None,
                    'exchange': ex_name,
                })
            if result:
                self.logger.info(f"📊 {ex_name}: прямой запрос → {len(result)} фьючерсов")
                return result
        except Exception as e:
            self.logger.debug(f"⚠️ {ex_name}: прямой запрос не сработал ({type(e).__name__})")
        return None

    # ========================================================================
    # Уровень 0: Построение кэша
    # ========================================================================

    async def _fetch_futures_for_exchange(self, ex_name: str) -> List[dict]:
        exchange = self.exchanges.get(ex_name)
        if not exchange:
            return []

        direct_result = await self._fetch_funding_rates_direct(ex_name)
        if direct_result:
            return direct_result

        try:
            raw_rates = await exchange.fetch_funding_rates()
            if raw_rates:
                result = []
                items = raw_rates.values() if isinstance(raw_rates, dict) else raw_rates
                for r in items:
                    if not isinstance(r, dict):
                        continue
                    symbol = r.get('symbol', '')
                    if not symbol:
                        continue
                    if ':USDT' not in symbol and ':USDC' not in symbol:
                        if '/USDT' in symbol:
                            symbol = symbol + ':USDT'
                        elif '/USDC' in symbol:
                            symbol = symbol + ':USDC'
                        else:
                            continue
                    rate_value = r.get('fundingRate')
                    if rate_value is None:
                        continue
                    result.append({
                        'symbol': symbol,
                        'rate': float(rate_value),
                        'next_funding_time': r.get('fundingTimestamp', 0) / 1000 if r.get('fundingTimestamp') else None,
                        'exchange': ex_name,
                    })
                if result:
                    self.logger.info(f"📊 {ex_name}: CCXT быстрый → {len(result)} фьючерсов")
                    return result
        except:
            pass

        self.logger.warning(f"⚠️ {ex_name}: не удалось получить фьючерсы, пропускаем")
        return []

    def _calculate_preliminary_profit(self, rate: float) -> float:
        if rate is None:
            return 0.0
        expected_bps = abs(rate) * 10000
        if self.deduct_fees_from_profit:
            min_spot_fee = self.manual_spot_fee_pct / 100.0
            min_perp_fee = self.manual_futures_fee_pct / 100.0
            total_fee_pct = (min_spot_fee + min_perp_fee) * 2 * 100
            return expected_bps - (total_fee_pct * 100)
        return expected_bps

    def _find_spot_market(self, exchange_name: str, perp_symbol: str) -> Optional[str]:
        exchange = self.exchanges.get(exchange_name)
        if not exchange:
            return None
        base = perp_symbol.split('/')[0]
        spot_symbols_to_try = [f"{base}/USDT", f"{base}/USDC"]
        if self.normalize_symbols:
            if base.startswith('1000'):
                spot_symbols_to_try.append(f"{base[4:]}/USDT")
            match = re.match(r'^(\d+)([A-Z].*)$', base)
            if match:
                spot_symbols_to_try.append(f"{match.group(2)}/USDT")
        for sym in spot_symbols_to_try:
            try:
                market = exchange.market(sym)
                if market.get('active', False) and market.get('spot', False):
                    return sym
            except:
                continue
        return None

    def _has_spot_connection(self, ex_name: str) -> bool:
        if self.is_test_mode:
            return ex_name in self.exchanges
        conns = self.metascalp_connections.get(ex_name, {})
        return 'spot_id' in conns and not conns.get('spot_view_mode', True)

    def _has_perp_connection(self, ex_name: str) -> bool:
        if self.is_test_mode:
            return ex_name in self.exchanges
        conns = self.metascalp_connections.get(ex_name, {})
        return 'perp_id' in conns and not conns.get('perp_view_mode', True)

    async def _rebuild_instrument_cache(self) -> None:
        self.logger.info("🔄 [Уровень 0] Перестроение кэша...")
        start_time = time.time()

        all_futures = []
        active_exchanges = set(self.config.get('active_exchanges', []))
        for ex_name in active_exchanges:
            if not self._has_perp_connection(ex_name):
                continue
            futures = await self._fetch_futures_for_exchange(ex_name)
            all_futures.extend(futures)

        self.cache_total_futures_found = len(all_futures)
        self.logger.info(f"📊 Всего собрано фьючерсов: {len(all_futures)}")

        profitable = []
        self.cache_filtered_by_profit = 0
        for f in all_futures:
            profit_bps = self._calculate_preliminary_profit(f['rate'])
            if profit_bps >= self.min_profit_bps:
                f['preliminary_profit_bps'] = profit_bps
                profitable.append(f)
            else:
                self.cache_filtered_by_profit += 1
        self.logger.info(f"💰 После фильтра прибыли: {len(profitable)} (отсеяно {self.cache_filtered_by_profit})")

        profitable.sort(key=lambda x: x['preliminary_profit_bps'], reverse=True)

        if self.cache_max_instruments > 0 and len(profitable) > self.cache_max_instruments:
            profitable = profitable[:self.cache_max_instruments]
            self.logger.info(f"📦 Ограничение кэша: {len(profitable)}")

        new_cache = []
        self.cache_filtered_by_no_spot = 0
        for f in profitable:
            perp_ex = f['exchange']
            spot_found = None
            if self._has_spot_connection(perp_ex):
                sm = self._find_spot_market(perp_ex, f['symbol'])
                if sm:
                    spot_found = perp_ex
            if not spot_found:
                for spot_ex in active_exchanges:
                    if spot_ex == perp_ex:
                        continue
                    if not self._has_spot_connection(spot_ex):
                        continue
                    sm = self._find_spot_market(spot_ex, f['symbol'])
                    if sm:
                        spot_found = spot_ex
                        break
            if spot_found:
                new_cache.append(CachedInstrument(
                    symbol=f['symbol'],
                    spot_exchange=spot_found,
                    perp_exchange=perp_ex,
                    funding_rate=f['rate'],
                    preliminary_profit_bps=f['preliminary_profit_bps'],
                ))
            else:
                self.cache_filtered_by_no_spot += 1

        self.logger.info(f"🔗 После поиска спота: {len(new_cache)} (отсеяно {self.cache_filtered_by_no_spot})")

        if self.check_trading_status:
            semaphore = asyncio.Semaphore(self.max_concurrent_cache_requests)
            self.cache_filtered_by_status = 0

            async def check_one(item):
                async with semaphore:
                    try:
                        pe = self.exchanges.get(item.perp_exchange)
                        se = self.exchanges.get(item.spot_exchange)
                        if not pe or not se:
                            return None
                        pm = pe.market(item.symbol)
                        ss = item.symbol.replace(':USDT', '')
                        sm = se.market(ss)
                        if pm.get('active', False) and sm.get('active', False):
                            return item
                        return None
                    except:
                        return None

            tasks = [check_one(item) for item in new_cache]
            results = await asyncio.gather(*tasks, return_exceptions=True)
            valid_count = sum(1 for r in results if isinstance(r, CachedInstrument))
            self.cache_filtered_by_status = len(new_cache) - valid_count
            new_cache = [r for r in results if isinstance(r, CachedInstrument)]
            self.logger.info(f"🔒 После статуса: {len(new_cache)} (отсеяно {self.cache_filtered_by_status})")

        self.instrument_cache = new_cache
        self.cache_last_updated = time.time()
        self._save_instrument_cache_to_file()

        elapsed = time.time() - start_time
        self.logger.info(f"✅ [Уровень 0] Кэш готов: {len(new_cache)} комбинаций за {elapsed:.1f} сек")

    # ========================================================================
    # Уровень 1
    # ========================================================================

    async def _fetch_funding_rate(self, exchange_name: str, symbol: str) -> Optional[Tuple[float, float]]:
        exchange = self.exchanges.get(exchange_name)
        if not exchange:
            return None
        try:
            ticker = await exchange.fetch_funding_rate(symbol)
            return (ticker.get('fundingRate', 0.0), ticker.get('fundingTimestamp', 0) / 1000)
        except:
            return None

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

    def _is_price_mismatch(self, spot_price: float, perp_price: float, max_ratio: float = 5.0) -> bool:
        if spot_price <= 0 or perp_price <= 0:
            return False
        ratio = max(spot_price, perp_price) / min(spot_price, perp_price)
        return ratio > max_ratio

    async def _check_liquidity_filters(self, spot_exchange: str, perp_exchange: str, symbol: str) -> Tuple[bool, float, float, float, float]:
        spot_ex = self.exchanges.get(spot_exchange)
        perp_ex = self.exchanges.get(perp_exchange)
        if not spot_ex or not perp_ex:
            return False, 0, 0, 0, 0
        try:
            spot_sym = symbol.replace(':USDT', '')
            spot_t, perp_t = await asyncio.gather(
                spot_ex.fetch_ticker(spot_sym),
                perp_ex.fetch_ticker(symbol)
            )
            sp = spot_t.get('last', 0)
            pp = perp_t.get('last', 0)
            sv = spot_t.get('quoteVolume', 0) or 0
            pv = perp_t.get('quoteVolume', 0) or 0
            if sv < self.min_volume_24h_usdt:
                self.filtered_by_volume += 1
                return False, sv, 0, sp, pp
            if pv < self.min_volume_24h_usdt:
                self.filtered_by_volume += 1
                return False, pv, 0, sp, pp
            if self._is_price_mismatch(sp, pp):
                self.filtered_by_symbol_mismatch += 1
                return False, sv, 0, sp, pp
            spread = abs(pp - sp) / sp * 100 if sp > 0 else 0
            if spread > self.max_slippage_pct:
                self.filtered_by_spread += 1
                return False, sv, spread, sp, pp
            return True, sv, spread, sp, pp
        except:
            return False, 0, 0, 0, 0

    async def _scan_symbol(self, item: CachedInstrument) -> Optional[ArbitrageOpportunity]:
        passes, volume, spread, sp, pp = await self._check_liquidity_filters(
            item.spot_exchange, item.perp_exchange, item.symbol
        )
        if not passes:
            return None
        result = await self._fetch_funding_rate(item.perp_exchange, item.symbol)
        if not result:
            return None
        rate, next_time = result
        if abs(rate) < self.funding_rate_threshold:
            self.filtered_by_rate_threshold += 1
            return None
        if self.min_time_to_funding_minutes > 0 and next_time:
            ttf = next_time - time.time()
            if ttf < self.min_time_to_funding_minutes * 60:
                self.filtered_by_time += 1
                return None
        if rate > 0:
            expected_bps = rate * 10000
            direction = "LONG_SPOT_SHORT_PERP"
        else:
            expected_bps = abs(rate) * 10000
            direction = "SHORT_SPOT_LONG_PERP"
        if direction == "SHORT_SPOT_LONG_PERP" and not self.margin_enabled:
            self.filtered_by_margin += 1
            return None
        spot_fee_pct = 0.0
        perp_fee_pct = 0.0
        net_bps = expected_bps
        if self.deduct_fees_from_profit:
            sfr = await self._get_trading_fees(item.spot_exchange, item.symbol, is_spot=True)
            pfr = await self._get_trading_fees(item.perp_exchange, item.symbol, is_spot=False)
            if sfr is not None and pfr is not None:
                spot_fee_pct = sfr * 100
                perp_fee_pct = pfr * 100
                total_fee_pct = (sfr + pfr) * 2 * 100
                net_bps = expected_bps - (total_fee_pct * 100)
                if net_bps < self.min_profit_bps:
                    self.filtered_by_fees += 1
                    return None
        return ArbitrageOpportunity(
            timestamp=time.time(), symbol=item.symbol,
            spot_exchange=item.spot_exchange, perp_exchange=item.perp_exchange,
            funding_rate=rate, expected_profit_bps=expected_bps,
            spot_price=sp, perp_price=pp, direction=direction,
            next_funding_time=next_time, volume_24h_usdt=volume,
            spread_pct=spread, spot_fee_pct=spot_fee_pct,
            perp_fee_pct=perp_fee_pct, net_profit_bps=net_bps
        )

    async def _scan_cached_opportunities(self) -> List[ArbitrageOpportunity]:
        if not self.instrument_cache:
            return []
        semaphore = asyncio.Semaphore(self.max_concurrent_requests)
        async def bounded(item):
            async with semaphore:
                return await self._scan_symbol(item)
        tasks = [bounded(item) for item in self.instrument_cache]
        results = await asyncio.gather(*tasks, return_exceptions=True)
        return [r for r in results if isinstance(r, ArbitrageOpportunity)]

    # ========================================================================
    # Условия входа и выхода
    # ========================================================================

    def should_buy_spot_short_perp(self, opp: ArbitrageOpportunity) -> bool:
        return opp.net_profit_bps >= self.min_profit_bps and opp.funding_rate > 0

    def should_sell_spot_long_perp(self, opp: ArbitrageOpportunity) -> bool:
        if not self.margin_enabled:
            return False
        return opp.net_profit_bps >= self.min_profit_bps and opp.funding_rate < 0

    async def can_buy_spot_short_perp(self, opp: ArbitrageOpportunity) -> bool:
        if self.is_test_mode:
            return True
        sc = self.metascalp_connections.get(opp.spot_exchange, {}).get('spot_id')
        pc = self.metascalp_connections.get(opp.perp_exchange, {}).get('perp_id')
        self.logger.info(f"🔍 Проверка баланса: spot_id={sc} (type={type(sc).__name__}), perp_id={pc} (type={type(pc).__name__})")
        self.logger.info(f"🔍 Доступные балансы: {list(self.metascalp_balances.keys())[:5]}")
        self.logger.info(f"🔍 spot_bal={self.metascalp_balances.get(sc, 'N/A')}, perp_bal={self.metascalp_balances.get(pc, 'N/A')}")
        if not sc:
            self.logger.info(f"❌ Нет spot подключения для {opp.spot_exchange}")
            return False
        if not pc:
            self.logger.info(f"❌ Нет perp подключения для {opp.perp_exchange}")
            return False
        spot_bal = self.metascalp_balances.get(sc, 0)
        perp_bal = self.metascalp_balances.get(pc, 0)
        if spot_bal < self.base_order_amount:
            self.logger.info(f"❌ Недостаточно баланса спот {opp.spot_exchange}: {spot_bal:.2f} < {self.base_order_amount} USDT")
            return False
        if perp_bal < self.base_order_amount * 0.1:
            self.logger.info(f"❌ Недостаточно баланса перп {opp.perp_exchange}: {perp_bal:.2f} < {self.base_order_amount * 0.1:.2f} USDT")
            return False
        return True

    async def can_sell_spot_long_perp(self, opp: ArbitrageOpportunity) -> bool:
        if self.is_test_mode:
            return True
        sc = self.metascalp_connections.get(opp.spot_exchange, {}).get('spot_id')
        pc = self.metascalp_connections.get(opp.perp_exchange, {}).get('perp_id')
        if not sc:
            self.logger.info(f"❌ Нет spot подключения для {opp.spot_exchange}")
            return False
        if not pc:
            self.logger.info(f"❌ Нет perp подключения для {opp.perp_exchange}")
            return False
        spot_bal = self.metascalp_balances.get(sc, 0)
        perp_bal = self.metascalp_balances.get(pc, 0)
        if spot_bal < self.base_order_amount:
            self.logger.info(f"❌ Недостаточно баланса спот {opp.spot_exchange}: {spot_bal:.2f} < {self.base_order_amount} USDT")
            return False
        if perp_bal < self.base_order_amount * 0.1:
            self.logger.info(f"❌ Недостаточно баланса перп {opp.perp_exchange}: {perp_bal:.2f} < {self.base_order_amount * 0.1:.2f} USDT")
            return False
        return True

    def _check_liquidation_risk(self, pos: Position) -> bool:
        if not pos.entry_perp_price or pos.entry_perp_price <= 0:
            return False
        current_price = self._last_perp_prices.get(pos.symbol, 0)
        if current_price <= 0:
            return False
        change_pct = (current_price - pos.entry_perp_price) / pos.entry_perp_price * 100
        if pos.direction == 'BUY_SPOT_SHORT_PERP' and change_pct >= self.max_price_change_pct:
            return True
        if pos.direction == 'SELL_SPOT_LONG_PERP' and change_pct <= -self.max_price_change_pct:
            return True
        return False

    async def _check_close_condition(self, pos: Position, current_rate: float) -> Tuple[bool, Optional[ExitReason]]:
        er = pos.entry_funding_rate
        if (er > 0 and current_rate < 0) or (er < 0 and current_rate > 0):
            return True, ExitReason.FUNDING_RATE_SIGN_CHANGED
        if self.max_position_age_hours == 0 and pos.next_funding_time:
            if self.current_timestamp >= pos.next_funding_time + self.post_funding_close_delay * 60:
                return True, ExitReason.FIRST_FUNDING_PAID
        if self._check_liquidation_risk(pos):
            change_pct = abs(self._last_perp_prices.get(pos.symbol, 0) - pos.entry_perp_price) / pos.entry_perp_price * 100
            self.logger.warning(f"⚠️ Риск ликвидации для {pos.symbol}: цена изменилась на {change_pct:.1f}%")
            if self.tg_manager:
                await self.tg_manager.notify(
                    f"⚠️ Риск ликвидации! {pos.symbol}: цена изменилась на {change_pct:.1f}%\n"
                    f"Позиция будет закрыта."
                )
            return True, ExitReason.LIQUIDATION_RISK
        max_age = self.max_position_age_hours * 3600
        if max_age > 0 and self.current_timestamp - pos.entry_time > max_age:
            return True, ExitReason.MAX_POSITION_AGE
        return False, None

    # ========================================================================
    # Расчёт PnL
    # ========================================================================

    async def _get_real_funding_payments(self, pos: Position) -> float:
        """Получает реальные выплаты фондирования через CCXT (для Binance/Bybit)"""
        if self.is_test_mode:
            return 0.0
        try:
            exchange = self.exchanges.get(pos.perp_exchange)
            if not exchange or not exchange.has.get('fetchFundingHistory'):
                return 0.0
            since_ms = int(pos.entry_time * 1000)
            history = await exchange.fetch_funding_history(pos.symbol, since=since_ms)
            total = 0.0
            for payment in history:
                total += payment.get('amount', 0.0)
            return total
        except:
            return 0.0

    async def _calculate_simulated_pnl(self, pos: Position) -> float:
        # 1. Уже зафиксированные выплаты
        received = pos.funding_payments_received

        # 2. В реальном режиме — получаем реальные выплаты
        if not self.is_test_mode:
            real_payments = await self._get_real_funding_payments(pos)
            if real_payments != 0.0:
                received = real_payments

        # 3. Доход с последней выплаты до сейчас
        current_rate = self._last_current_rates.get(pos.symbol, pos.entry_funding_rate)
        last_time = pos.last_funding_time or pos.entry_time
        hours_since_last = max(0, (self.current_timestamp - last_time) / 3600)
        pending = abs(current_rate) * pos.size_usdt * (hours_since_last / 8)

        # 4. Комиссии
        sfr = await self._get_trading_fees(pos.spot_exchange, pos.symbol, True) or 0.001
        pfr = await self._get_trading_fees(pos.perp_exchange, pos.symbol, False) or 0.0005

        pos.spot_entry_fee = pos.size_usdt * sfr
        pos.perp_entry_fee = pos.size_usdt * pfr
        pos.spot_exit_fee = pos.size_usdt * sfr
        pos.perp_exit_fee = pos.size_usdt * pfr

        tf = pos.size_usdt * (sfr + pfr) * 2

        return received + pending - tf

    # ========================================================================
    # Форматирование тикеров и размеров
    # ========================================================================

    def _format_ticker_for_exchange(self, symbol: str, exchange: str) -> str:
        """Форматирует тикер в зависимости от биржи"""
        slash_exchanges = {'gate', 'kucoin', 'hyperliquid', 'lighter'}
        underscore_exchanges = {'mexc', 'bitmart', 'lbank', 'xt'}
        
        if exchange in slash_exchanges:
            return symbol.replace(':USDT', '')
        elif exchange in underscore_exchanges:
            return symbol.replace('/USDT:USDT', '_USDT')
        else:
            return symbol.replace('/USDT:USDT', 'USDT').replace('/USDT', 'USDT')

    def _round_size_for_exchange(self, size: float, exchange: str, price: float) -> float:
        """Округляет размер ордера согласно требованиям биржи"""
        # Gate spot — целое число, min 1
        if exchange == 'gate' and price > 1:
            size = float(int(size))
            if size < 1:
                size = 1.0
            return size
        
        # Gate perp — кратно 100
        if exchange == 'gate':
            size = float(int(size / 100) * 100)
            if size < 100:
                size = 100.0
            return size
        
        # Binance spot — 4 знака
        if exchange == 'binance' and price > 1:
            return round(size, 4)
        
        # Binance perp — целое
        if exchange == 'binance':
            size = float(int(size))
            if size < 1:
                size = 1.0
            return size
        
        # По умолчанию
        if size < 1:
            return round(size, 6)
        return float(int(size))

    # ========================================================================
    # Исполнение сделок
    # ========================================================================

    async def execute_buy_spot_short_perp(self, opp: ArbitrageOpportunity) -> bool:
        self.logger.info(f"📈 LONG SPOT + SHORT PERP: {opp.symbol} ({opp.net_profit_bps:.1f} bps)")
        if self.is_test_mode:
            sfr = await self._get_trading_fees(opp.spot_exchange, opp.symbol, is_spot=True) or (self.manual_spot_fee_pct / 100.0)
            pfr = await self._get_trading_fees(opp.perp_exchange, opp.symbol, is_spot=False) or (self.manual_futures_fee_pct / 100.0)
            pos = Position(symbol=opp.symbol, spot_exchange=opp.spot_exchange, perp_exchange=opp.perp_exchange,
                          direction='BUY_SPOT_SHORT_PERP', entry_time=self.current_timestamp,
                          entry_funding_rate=opp.funding_rate, size_usdt=self.base_order_amount,
                          spot_filled=True, perp_filled=True, next_funding_time=opp.next_funding_time,
                          leverage=self.leverage, entry_perp_price=opp.perp_price,
                          spot_entry_fee=self.base_order_amount * sfr,
                          perp_entry_fee=self.base_order_amount * pfr,
                          spot_exit_fee=self.base_order_amount * sfr,
                          perp_exit_fee=self.base_order_amount * pfr)
            self.positions.append(pos)
            self._save_open_positions()
            self._last_current_rates[opp.symbol] = opp.funding_rate
            self._last_perp_prices[opp.symbol] = opp.perp_price
            self.logger.info(f"🧪 [ТЕСТ] Позиция открыта (всего: {len(self.active_positions)})")
            if self.tg_manager:
                await self.tg_manager.notify(
                    f"📈 Открыта BUY позиция: {pos.symbol} ({pos.spot_exchange}/{pos.perp_exchange})\n"
                    f"Ставка: {pos.entry_funding_rate*100:.4f}% | Прибыль: {opp.net_profit_bps:.1f} bps"
                )
            return True
        return await self._execute_real_buy_spot_short_perp(opp)

    async def _execute_real_buy_spot_short_perp(self, opp: ArbitrageOpportunity) -> bool:
        sym_key = f"{opp.symbol}|{opp.spot_exchange}|{opp.perp_exchange}"
        if sym_key in self._opening_symbols:
            self.logger.warning(f"⚠️ {opp.symbol} уже в процессе открытия, пропускаем")
            return False
        self._opening_symbols.add(sym_key)
        
        try:
            sc = self.metascalp_connections[opp.spot_exchange]['spot_id']
            pc = self.metascalp_connections[opp.perp_exchange]['perp_id']
            
            cs_spot = self._format_ticker_for_exchange(opp.symbol, opp.spot_exchange)
            cs_perp = self._format_ticker_for_exchange(opp.symbol, opp.perp_exchange)
            
            spot_price = opp.spot_price if opp.spot_price > 0 else 1.0
            perp_price = opp.perp_price if opp.perp_price > 0 else 1.0
            
            # Размер фьючерса в токенах
            ps = self.base_order_amount / perp_price
            ps = self._round_size_for_exchange(ps, opp.perp_exchange, perp_price)
            
            # Размер спота в USDT (MetaScalp spot принимает Size в USDT!)
            spot_size_usdt = ps * spot_price
            ss_send = round(spot_size_usdt + spot_price, 2)  # +1 токен запаса
            
            for attempt in range(3):
                self.logger.info(f"🔍 Попытка {attempt+1}: spot={cs_spot} size={ss_send} USDT, perp={cs_perp} size={ps}")
                
                # Шаг 1: Открываем фьючерс ПЕРВЫМ
                async with self.metascalp_session.post(
                    f"http://127.0.0.1:{self.metascalp_port}/api/connections/{pc}/orders",
                    json={"Ticker": cs_perp, "Side": 2, "Type": 4, "Size": ps}
                ) as pr:
                    pres = await pr.json()
                self.logger.info(f"🔍 Ответ perp: {pres}")
                
                perp_status = pres.get('Status') or pres.get('status', '')
                if perp_status != 'ok':
                    self.logger.warning(f"⚠️ Фьючерс не открылся: {pres}")
                    await asyncio.sleep(1)
                    continue
                
                # Шаг 2: Фьючерс открыт — открываем спот (размер в USDT!)
                async with self.metascalp_session.post(
                    f"http://127.0.0.1:{self.metascalp_port}/api/connections/{sc}/orders",
                    json={"Ticker": cs_spot, "Side": 1, "Type": 4, "Size": ss_send}
                ) as sr:
                    sres = await sr.json()
                self.logger.info(f"🔍 Ответ spot: {sres}")
                
                spot_status = sres.get('Status') or sres.get('status', '')
                if spot_status == 'ok':
                    pos = Position(symbol=opp.symbol, spot_exchange=opp.spot_exchange, perp_exchange=opp.perp_exchange,
                                direction='BUY_SPOT_SHORT_PERP', entry_time=self.current_timestamp,
                                entry_funding_rate=opp.funding_rate, size_usdt=self.base_order_amount,
                                spot_order_id=sres.get('ClientId') or sres.get('clientId'),
                                perp_order_id=pres.get('ClientId') or pres.get('clientId'),
                                next_funding_time=opp.next_funding_time, leverage=self.leverage,
                                entry_perp_price=opp.perp_price)
                    self.positions.append(pos)
                    self._save_open_positions()
                    self._last_current_rates[opp.symbol] = opp.funding_rate
                    self._last_perp_prices[opp.symbol] = opp.perp_price
                    self.logger.info(f"✅ Позиция открыта: spot={ss_send} USDT, perp={ps}")
                    if self.tg_manager:
                        await self.tg_manager.notify(
                            f"📈 Открыта BUY: {opp.symbol} ({opp.spot_exchange}/{opp.perp_exchange})\n"
                            f"Ставка: {opp.funding_rate*100:.4f}% | Прибыль: {opp.net_profit_bps:.1f} bps"
                        )
                    return True
                
                # Спот не открылся — откатываем фьючерс
                self.logger.error(f"❌ Спот не открылся: {sres}, закрываем фьючерс")
                async with self.metascalp_session.post(
                    f"http://127.0.0.1:{self.metascalp_port}/api/connections/{pc}/orders",
                    json={"Ticker": cs_perp, "Side": 1, "Type": 4, "Size": ps}
                ) as cr:
                    cres = await cr.json()
                self.logger.info(f"🔧 Откат perp: {cres}")
                
                if self.tg_manager:
                    await self.tg_manager.notify(f"❌ Откат {opp.symbol}: спот не открылся, фьючерс закрыт")
                return False
            
            self.logger.error(f"❌ Не удалось открыть {opp.symbol} после 3 попыток")
            if self.tg_manager:
                await self.tg_manager.notify(f"❌ Не удалось открыть {opp.symbol} после 3 попыток")
            return False
        except Exception as e:
            self.logger.error(f"❌ Ошибка: {e}")
            return False
        finally:
            self._opening_symbols.discard(sym_key)

    async def execute_sell_spot_long_perp(self, opp: ArbitrageOpportunity) -> bool:
        self.logger.info(f"📉 SHORT SPOT + LONG PERP: {opp.symbol} ({opp.net_profit_bps:.1f} bps)")
        if self.is_test_mode:
            sfr = await self._get_trading_fees(opp.spot_exchange, opp.symbol, is_spot=True) or (self.manual_spot_fee_pct / 100.0)
            pfr = await self._get_trading_fees(opp.perp_exchange, opp.symbol, is_spot=False) or (self.manual_futures_fee_pct / 100.0)
            pos = Position(symbol=opp.symbol, spot_exchange=opp.spot_exchange, perp_exchange=opp.perp_exchange,
                          direction='SELL_SPOT_LONG_PERP', entry_time=self.current_timestamp,
                          entry_funding_rate=opp.funding_rate, size_usdt=self.base_order_amount,
                          spot_filled=True, perp_filled=True, next_funding_time=opp.next_funding_time,
                          leverage=self.leverage, entry_perp_price=opp.perp_price,
                          spot_entry_fee=self.base_order_amount * sfr,
                          perp_entry_fee=self.base_order_amount * pfr,
                          spot_exit_fee=self.base_order_amount * sfr,
                          perp_exit_fee=self.base_order_amount * pfr)
            self.positions.append(pos)
            self._save_open_positions()
            self._last_current_rates[opp.symbol] = opp.funding_rate
            self._last_perp_prices[opp.symbol] = opp.perp_price
            self.logger.info(f"🧪 [ТЕСТ] Позиция открыта (всего: {len(self.active_positions)})")
            if self.tg_manager:
                await self.tg_manager.notify(
                    f"📉 Открыта SELL позиция: {pos.symbol} ({pos.spot_exchange}/{pos.perp_exchange})\n"
                    f"Ставка: {pos.entry_funding_rate*100:.4f}% | Прибыль: {opp.net_profit_bps:.1f} bps"
                )
            return True
        return await self._execute_real_sell_spot_long_perp(opp)

    async def _execute_real_sell_spot_long_perp(self, opp: ArbitrageOpportunity) -> bool:
        sym_key = f"{opp.symbol}|{opp.spot_exchange}|{opp.perp_exchange}"
        if sym_key in self._opening_symbols:
            self.logger.warning(f"⚠️ {opp.symbol} уже в процессе открытия, пропускаем")
            return False
        self._opening_symbols.add(sym_key)
        
        try:
            sc = self.metascalp_connections[opp.spot_exchange]['spot_id']
            pc = self.metascalp_connections[opp.perp_exchange]['perp_id']
            
            cs_spot = self._format_ticker_for_exchange(opp.symbol, opp.spot_exchange)
            cs_perp = self._format_ticker_for_exchange(opp.symbol, opp.perp_exchange)
            
            spot_price = opp.spot_price if opp.spot_price > 0 else 1.0
            perp_price = opp.perp_price if opp.perp_price > 0 else 1.0
            
            # Размер фьючерса в токенах
            ps = self.base_order_amount / perp_price
            ps = self._round_size_for_exchange(ps, opp.perp_exchange, perp_price)
            
            # Размер спота в USDT (MetaScalp spot принимает Size в USDT!)
            spot_size_usdt = ps * spot_price
            ss_send = round(spot_size_usdt + spot_price, 2)  # +1 токен запаса
            
            for attempt in range(3):
                self.logger.info(f"🔍 Попытка {attempt+1}: spot={cs_spot} size={ss_send} USDT, perp={cs_perp} size={ps}")
                
                # Шаг 1: Открываем фьючерс ПЕРВЫМ
                async with self.metascalp_session.post(
                    f"http://127.0.0.1:{self.metascalp_port}/api/connections/{pc}/orders",
                    json={"Ticker": cs_perp, "Side": 1, "Type": 4, "Size": ps}
                ) as pr:
                    pres = await pr.json()
                self.logger.info(f"🔍 Ответ perp: {pres}")
                
                perp_status = pres.get('Status') or pres.get('status', '')
                if perp_status != 'ok':
                    self.logger.warning(f"⚠️ Фьючерс не открылся: {pres}")
                    await asyncio.sleep(1)
                    continue
                
                # Шаг 2: Фьючерс открыт — открываем спот (размер в USDT!)
                async with self.metascalp_session.post(
                    f"http://127.0.0.1:{self.metascalp_port}/api/connections/{sc}/orders",
                    json={"Ticker": cs_spot, "Side": 2, "Type": 4, "Size": ss_send}
                ) as sr:
                    sres = await sr.json()
                self.logger.info(f"🔍 Ответ spot: {sres}")
                
                spot_status = sres.get('Status') or sres.get('status', '')
                if spot_status == 'ok':
                    pos = Position(symbol=opp.symbol, spot_exchange=opp.spot_exchange, perp_exchange=opp.perp_exchange,
                                direction='SELL_SPOT_LONG_PERP', entry_time=self.current_timestamp,
                                entry_funding_rate=opp.funding_rate, size_usdt=self.base_order_amount,
                                spot_order_id=sres.get('ClientId') or sres.get('clientId'),
                                perp_order_id=pres.get('ClientId') or pres.get('clientId'),
                                next_funding_time=opp.next_funding_time, leverage=self.leverage,
                                entry_perp_price=opp.perp_price)
                    self.positions.append(pos)
                    self._save_open_positions()
                    self._last_current_rates[opp.symbol] = opp.funding_rate
                    self._last_perp_prices[opp.symbol] = opp.perp_price
                    self.logger.info(f"✅ Позиция открыта: spot={ss_send} USDT, perp={ps}")
                    if self.tg_manager:
                        await self.tg_manager.notify(
                            f"📉 Открыта SELL: {opp.symbol} ({opp.spot_exchange}/{opp.perp_exchange})\n"
                            f"Ставка: {opp.funding_rate*100:.4f}% | Прибыль: {opp.net_profit_bps:.1f} bps"
                        )
                    return True
                
                # Спот не открылся — откатываем фьючерс
                self.logger.error(f"❌ Спот не открылся: {sres}, закрываем фьючерс")
                async with self.metascalp_session.post(
                    f"http://127.0.0.1:{self.metascalp_port}/api/connections/{pc}/orders",
                    json={"Ticker": cs_perp, "Side": 2, "Type": 4, "Size": ps}
                ) as cr:
                    cres = await cr.json()
                self.logger.info(f"🔧 Откат perp: {cres}")
                
                if self.tg_manager:
                    await self.tg_manager.notify(f"❌ Откат {opp.symbol}: спот не открылся, фьючерс закрыт")
                return False
            
            self.logger.error(f"❌ Не удалось открыть {opp.symbol} после 3 попыток")
            if self.tg_manager:
                await self.tg_manager.notify(f"❌ Не удалось открыть {opp.symbol} после 3 попыток")
            return False
        except Exception as e:
            self.logger.error(f"❌ Ошибка: {e}")
            return False
        finally:
            self._opening_symbols.discard(sym_key)

    async def execute_close_position(self, pos: Position, exit_reason: ExitReason = ExitReason.NORMAL) -> bool:
        if pos.close_time is not None:
            self.logger.warning(f"⚠️ Позиция {pos.symbol} уже закрыта")
            return False
        if pos not in self.positions:
            self.logger.warning(f"⚠️ Позиция {pos.symbol} не найдена")
            return False
        if pos.close_in_progress:
            self.logger.warning(f"⚠️ Закрытие {pos.symbol} уже в процессе")
            return False

        pos.close_in_progress = True
        self.logger.info(f"🔒 Закрытие: {pos.symbol}, причина: {exit_reason.russian()}")

        if self.is_test_mode:
            pnl = await self._calculate_simulated_pnl(pos)
            pos.close_time = self.current_timestamp
            pos.pnl = pnl
            pos.spot_filled = True
            pos.perp_filled = True
            pos.exit_reason = exit_reason.value
            trade = TradeRecord(id=datetime.now().strftime('%Y%m%d%H%M%S'), symbol=pos.symbol, direction=pos.direction,
                               entry_time=pos.entry_time, exit_time=pos.close_time, size_usdt=pos.size_usdt,
                               entry_funding_rate=pos.entry_funding_rate, pnl=pnl,
                               pnl_pct=pnl/pos.size_usdt*100 if pos.size_usdt else 0,
                               leverage=pos.leverage, exit_reason=exit_reason.value,
                               spot_entry_fee=pos.spot_entry_fee, perp_entry_fee=pos.perp_entry_fee,
                               spot_exit_fee=pos.spot_exit_fee, perp_exit_fee=pos.perp_exit_fee)
            self._add_trade_record(trade)
            if pos in self.positions:
                self.positions.remove(pos)
                self._save_open_positions()
                self.logger.info(f"🧪 [ТЕСТ] Закрыта, PnL: {pnl:.4f} USDT")
            if self.tg_manager:
                await self.tg_manager.notify(
                    f"🔒 Закрыта позиция: {pos.symbol}\n"
                    f"PnL: {pnl:.4f} USDT | Причина: {exit_reason.russian()}"
                )
            return True
        else:
            success = await self._execute_real_close_position(pos, exit_reason)
            pos.close_in_progress = False
            if success:
                if pos in self.positions:
                    self.positions.remove(pos)
                    self._save_open_positions()
            return success

    async def _execute_real_close_position(self, pos: Position, exit_reason: ExitReason) -> bool:
        try:
            sc = self.metascalp_connections[pos.spot_exchange]['spot_id']
            pc = self.metascalp_connections[pos.perp_exchange]['perp_id']
            
            cs_spot = self._format_ticker_for_exchange(pos.symbol, pos.spot_exchange)
            cs_perp = self._format_ticker_for_exchange(pos.symbol, pos.perp_exchange)

            if pos.direction == 'BUY_SPOT_SHORT_PERP':
                spot_side, perp_side = 2, 1  # Sell spot, Buy perp
            else:
                spot_side, perp_side = 1, 2  # Buy spot, Sell perp

            # Размер фьючерса в токенах (как был при открытии)
            perp_size = self.base_order_amount / (self._last_perp_prices.get(pos.symbol, 1.0) or 1.0)
            perp_size = self._round_size_for_exchange(perp_size, pos.perp_exchange, 1.0)
            
            # Размер спота в USDT (MetaScalp spot принимает Size в USDT!)
            spot_price = self._last_perp_prices.get(pos.symbol, 1.0) or 1.0
            spot_size_usdt = perp_size * spot_price
            spot_size = round(spot_size_usdt, 2)

            async def send_close_order(conn_id, ticker, side, size, is_spot=False):
                payload = {"Ticker": ticker, "Side": side, "Type": 4, "Size": size, "ReduceOnly": True}
                async with self.metascalp_session.post(
                    f"http://127.0.0.1:{self.metascalp_port}/api/connections/{conn_id}/orders",
                    json=payload
                ) as resp:
                    result = await resp.json()
                self.logger.info(f"🔍 Закрытие {ticker}: {result}")
                return result

            for attempt in range(4):
                self.logger.info(f"🔍 Попытка закрытия {attempt+1}: spot={cs_spot} size={spot_size} USDT, perp={cs_perp} size={perp_size}")
                
                spot_result, perp_result = await asyncio.gather(
                    send_close_order(sc, cs_spot, spot_side, spot_size),
                    send_close_order(pc, cs_perp, perp_side, perp_size)
                )
                
                spot_status = spot_result.get('Status') or spot_result.get('status', '')
                perp_status = perp_result.get('Status') or perp_result.get('status', '')
                
                if spot_status == 'ok' and perp_status == 'ok':
                    pos.close_time = self.current_timestamp
                    pos.exit_reason = exit_reason.value
                    self.logger.info(f"✅ Позиция закрыта")
                    if self.tg_manager:
                        await self.tg_manager.notify(
                            f"🔒 Закрыта: {pos.symbol}\nПричина: {exit_reason.russian()}"
                        )
                    return True
                
                self.logger.warning(f"⚠️ Попытка {attempt+1}: spot={spot_status}, perp={perp_status}")
                await asyncio.sleep(2)
            
            self.logger.error(f"❌ Не удалось закрыть {pos.symbol} после 4 попыток")
            if self.tg_manager:
                await self.tg_manager.notify(
                    f"🚨 Не удалось закрыть {pos.symbol} после 4 попыток!\nТребуется ручное вмешательство!"
                )
            return False
        except Exception as e:
            self.logger.error(f"❌ Ошибка закрытия: {e}")
            if self.tg_manager:
                await self.tg_manager.notify(f"❌ Ошибка при закрытии {pos.symbol}: {e}")
            return False

    # ========================================================================
    # Основной цикл
    # ========================================================================

    async def on_tick(self, opportunities: List[ArbitrageOpportunity]) -> None:
        for pos in self.active_positions:
            result = await self._fetch_funding_rate(pos.perp_exchange, pos.symbol)
            if result:
                rate, next_time = result
                self._last_current_rates[pos.symbol] = rate
                self.logger.info(f"📊 Ставка {pos.symbol}: {rate*100:.4f}%")
                if pos.next_funding_time and self.current_timestamp >= pos.next_funding_time:
                    if pos.last_funding_time is None or pos.next_funding_time > pos.last_funding_time:
                        current_rate = self._last_current_rates.get(pos.symbol, pos.entry_funding_rate)
                        funding_amount = abs(current_rate) * pos.size_usdt
                        pos.funding_payments_received += funding_amount
                        pos.funding_payments_count += 1
                        pos.last_funding_time = pos.next_funding_time
                        self.logger.info(f"💰 Выплата #{pos.funding_payments_count} для {pos.symbol}: {funding_amount:.4f} USDT (ставка {current_rate*100:.4f}%)")
                        self._save_open_positions()
                if next_time and (not pos.next_funding_time or next_time > pos.next_funding_time):
                    pos.next_funding_time = next_time
            ticker = await self._fetch_perp_price(pos.perp_exchange, pos.symbol)
            if ticker:
                self._last_perp_prices[pos.symbol] = ticker

        for pos in self.active_positions[:]:
            if pos.close_in_progress:
                continue
            cr = self._last_current_rates.get(pos.symbol)
            if cr is not None:
                should_close, reason = await self._check_close_condition(pos, cr)
                if should_close:
                    await self.execute_close_position(pos, reason or ExitReason.NORMAL)

        if not self.trading_enabled:
            return
        if self.current_timestamp < self.next_arbitrage_opening_ts:
            return

        for opp in opportunities:
            sym_key = f"{opp.symbol}|{opp.spot_exchange}|{opp.perp_exchange}"
            if sym_key in self._opening_symbols:
                continue  # уже пытаемся открыть
            if self.is_position_already_open(opp.symbol, opp.spot_exchange, opp.perp_exchange):
                continue
            if self.should_buy_spot_short_perp(opp) and self.can_open_long_position() and await self.can_buy_spot_short_perp(opp):
                await self.execute_buy_spot_short_perp(opp)
            elif self.should_sell_spot_long_perp(opp) and self.can_open_short_position() and await self.can_sell_spot_long_perp(opp):
                await self.execute_sell_spot_long_perp(opp)

    async def _fetch_perp_price(self, exchange_name: str, symbol: str) -> Optional[float]:
        exchange = self.exchanges.get(exchange_name)
        if not exchange:
            return None
        try:
            ticker = await exchange.fetch_ticker(symbol)
            return ticker.get('last', 0)
        except:
            return None

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
            self.filtered_by_rate_threshold = 0
            self.filtered_by_symbol_mismatch = 0
        await self._check_metascalp_connection()

        now = time.time()
        cache_age = (now - self.cache_last_updated) / 60 if self.cache_last_updated > 0 else 999
        if cache_age >= self.cache_rebuild_interval or not self.instrument_cache:
            await self._rebuild_instrument_cache()

        self.filtered_by_volume = 0
        self.filtered_by_spread = 0
        self.filtered_by_margin = 0
        self.filtered_by_time = 0
        self.filtered_by_fees = 0
        self.filtered_by_rate_threshold = 0
        self.filtered_by_symbol_mismatch = 0

        self.last_scan_time = self.current_timestamp
        opportunities = await self._scan_cached_opportunities()
        opportunities.sort(key=lambda x: x.net_profit_bps, reverse=True)
        self.current_opportunities = opportunities[:self.max_current_opportunities]
        for opp in opportunities[:self.max_recent_opportunities]:
            self.recent_opportunities.append(opp)
        if opportunities:
            self.opportunities_found += len(opportunities)
            current_signal_keys = set()
            for i, opp in enumerate(opportunities[:5]):
                key = f"{opp.symbol}|{opp.spot_exchange}|{opp.perp_exchange}"
                current_signal_keys.add(key)
                if key not in self._last_signal_log_set:
                    self.signal_logger.info(
                        f"#{i+1} | {opp.symbol} | {opp.spot_exchange}/{opp.perp_exchange} | "
                        f"Ставка: {opp.funding_rate*100:.4f}% | Прибыль: {opp.net_profit_bps:.1f} bps"
                    )
            self._last_signal_log_set = current_signal_keys
        await self.on_tick(opportunities)

    async def scan_loop(self) -> None:
        while self.is_running:
            try:
                await self._scan_iteration()
            except Exception as e:
                self.logger.error(f"❌ Ошибка цикла: {e}", exc_info=True)
            await asyncio.sleep(self.scan_interval)

    # ========================================================================
    # Конфигурация через дашборд
    # ========================================================================

    def update_config(self, updates: Dict[str, Any]) -> None:
        old_min_profit = self.config.get('min_profit_bps', 10)
        old_check = self.config.get('check_trading_status', True)
        old_active = set(self.config.get('active_exchanges', []))
        old_deduct = self.config.get('deduct_fees_from_profit', True)

        for key, value in updates.items():
            if key in self.config:
                old_val = self.config[key]
                self.config[key] = value
                if old_val != value:
                    self.logger.info(f"📝 Конфиг обновлён: {key} = {value}")

        self.scan_interval = self.config.get('scan_interval', 5)
        self.base_order_amount = self.config.get('base_order_amount', 100.0)
        self.min_profit_bps = self.config.get('min_profit_bps', 10)
        self.manual_test_mode = self.config.get('test_mode', True)
        self.leverage = self.config.get('leverage', 3)
        self.margin_enabled = self.config.get('margin_enabled', False)
        self.min_volume_24h_usdt = self.config.get('min_volume_24h_usdt', 10000)
        self.max_slippage_pct = self.config.get('max_slippage_pct', 1.0)
        self.min_time_to_funding_minutes = self.config.get('min_time_to_funding_minutes', 0)
        self.check_trading_status = self.config.get('check_trading_status', True)
        self.deduct_fees_from_profit = self.config.get('deduct_fees_from_profit', True)
        self.manual_spot_fee_pct = self.config.get('manual_spot_fee_pct', 0.1)
        self.manual_futures_fee_pct = self.config.get('manual_futures_fee_pct', 0.05)
        self.max_positions_per_side = self.config.get('max_positions_per_side', 5)
        self.max_position_age_hours = self.config.get('max_position_age_hours', 24)
        self.post_funding_close_delay = self.config.get('post_funding_close_delay_minutes', 5)
        self.max_concurrent_requests = self.config.get('max_concurrent_requests', 20)
        self.max_concurrent_cache_requests = self.config.get('max_concurrent_cache_requests', 30)
        self.cache_rebuild_interval = self.config.get('cache_rebuild_interval_minutes', 30)
        self.normalize_symbols = self.config.get('normalize_symbols', True)
        self.cache_max_instruments = self.config.get('cache_max_instruments', 500)
        self.trading_enabled = self.config.get('trading_enabled', True)
        self.max_price_change_pct = self.config.get('max_price_change_pct', 15)

        if old_deduct and not self.deduct_fees_from_profit:
            self.spot_fees_cache.clear()
            self.futures_fees_cache.clear()

        new_min_profit = self.config.get('min_profit_bps', 10)
        new_check = self.config.get('check_trading_status', True)
        new_active = set(self.config.get('active_exchanges', []))
        if old_min_profit != new_min_profit or old_check != new_check or old_active != new_active:
            self.instrument_cache.clear()
            self.cache_last_updated = 0
            self.logger.info("🔄 Кэш сброшен из-за изменения критичных фильтров")

        self._save_config()

    def update_active_exchanges(self, exchanges: List[str]) -> None:
        valid = [e for e in exchanges if e in self.config['enabled_exchanges']]
        self.config['active_exchanges'] = valid
        self.instrument_cache.clear()
        self.cache_last_updated = 0
        self._save_config()
        self.logger.info(f"📝 Активные биржи обновлены: {', '.join(valid)}")

    def get_status(self) -> dict:
        active_positions = self.active_positions
        fp = active_positions[0] if active_positions else None
        positions_with_id = []
        for p in active_positions:
            pd = asdict(p)
            pd['position_id'] = f"{p.symbol}_{p.spot_exchange}_{p.perp_exchange}_{p.entry_time}"
            pd['estimated_pnl'] = self.get_position_estimated_pnl(p)
            if p.next_funding_time:
                ttf = p.next_funding_time - self.current_timestamp
                pd['funding_time_str'] = f"{int(ttf//3600)}ч {int((ttf%3600)//60)}м" if ttf > 0 else "выплата идёт"
            else:
                pd['funding_time_str'] = "—"
            positions_with_id.append(pd)

        next_funding_str = positions_with_id[0]['funding_time_str'] if positions_with_id else None
        current_rates = {pos.symbol: self._last_current_rates.get(pos.symbol) for pos in active_positions if self._last_current_rates.get(pos.symbol) is not None}

        long_count = sum(1 for p in active_positions if p.direction == 'BUY_SPOT_SHORT_PERP')
        short_count = sum(1 for p in active_positions if p.direction == 'SELL_SPOT_LONG_PERP')
        next_update_in = max(0, int(self.cache_rebuild_interval * 60 - (time.time() - self.cache_last_updated))) if self.cache_last_updated > 0 else 0
        uptime_seconds = int(self.current_timestamp - self.start_time)

        return {
            'version': __version__,
            'bot_name': BOT_NAME,
            'timestamp': self.current_timestamp,
            'datetime': datetime.now().isoformat(),
            'uptime_seconds': uptime_seconds,
            'strategy_state': self.strategy_state.value,
            'connection_state': self.metascalp_state.value,
            'exchange_status': self.exchange_status,
            'test_mode': self.is_test_mode,
            'auto_test_mode': self.auto_test_mode,
            'trading_enabled': self.trading_enabled,
            'metascalp_port': self.metascalp_port,
            'metascalp_version': self.metascalp_version,
            'metascalp_connections': self.metascalp_connections,
            'metascalp_balances': self.metascalp_balances,
            'positions': positions_with_id,
            'position': asdict(fp) if fp else None,
            'active_positions_count': len(active_positions),
            'long_positions_count': long_count,
            'short_positions_count': short_count,
            'current_funding_rate': current_rates.get(fp.symbol) if fp else None,
            'current_funding_rates': current_rates,
            'next_funding_time_str': next_funding_str,
            'scan_count': self.scan_count,
            'opportunities_found': self.opportunities_found,
            'total_pnl': self.total_pnl,
            'trades_count': len(self.trades_history),
            'current_opportunities': [o.to_dict() for o in self.current_opportunities],
            'recent_opportunities': [o.to_dict() for o in self.recent_opportunities],
            'last_scan_time': self.last_scan_time,
            'cache_info': {
                'total_futures_found': self.cache_total_futures_found,
                'filtered_by_profit': self.cache_filtered_by_profit,
                'filtered_by_no_spot': self.cache_filtered_by_no_spot,
                'filtered_by_status': self.cache_filtered_by_status,
                'instruments_in_cache': len(self.instrument_cache),
                'last_updated': self.cache_last_updated,
                'next_update_in_seconds': next_update_in,
            },
            'level1_stats': {
                'checked': len(self.instrument_cache),
                'signals_found': len(self.current_opportunities),
                'filtered_by_volume': self.filtered_by_volume,
                'filtered_by_spread': self.filtered_by_spread,
                'filtered_by_margin': self.filtered_by_margin,
                'filtered_by_time': self.filtered_by_time,
                'filtered_by_rate_threshold': self.filtered_by_rate_threshold,
                'filtered_by_fees': self.filtered_by_fees,
                'filtered_by_symbol_mismatch': self.filtered_by_symbol_mismatch,
            },
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
                'min_time_to_funding_minutes': self.min_time_to_funding_minutes,
                'check_trading_status': self.check_trading_status,
                'deduct_fees_from_profit': self.deduct_fees_from_profit,
                'manual_spot_fee_pct': self.manual_spot_fee_pct,
                'manual_futures_fee_pct': self.manual_futures_fee_pct,
                'max_positions_per_side': self.max_positions_per_side,
                'max_position_age_hours': self.max_position_age_hours,
                'post_funding_close_delay_minutes': self.config.get('post_funding_close_delay_minutes', 5),
                'cache_rebuild_interval_minutes': self.cache_rebuild_interval,
                'normalize_symbols': self.normalize_symbols,
                'trading_enabled': self.trading_enabled,
                'max_price_change_pct': self.max_price_change_pct,
            },
            'trades_history': [t.to_dict() for t in self.trades_history[-10:]]
        }


# ============================================================================
# FastAPI
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
    dp = Path(__file__).parent / "dashboard.html"
    return dp.read_text(encoding='utf-8') if dp.exists() else "<h1>Dashboard not found</h1>"

@app.get("/api/status")
async def get_status():
    if not bot: raise HTTPException(503, "Bot not ready")
    return bot.get_status()

@app.post("/api/config")
async def update_config(updates: Dict[str, Any]):
    if not bot: raise HTTPException(503, "Bot not ready")
    bot.update_config(updates)
    return {"status": "ok"}

@app.post("/api/exchanges")
async def update_active_exchanges(data: Dict[str, List[str]]):
    if not bot: raise HTTPException(503, "Bot not ready")
    bot.update_active_exchanges(data.get('exchanges', []))
    return {"status": "ok"}

@app.get("/api/opportunities")
async def get_opportunities():
    if not bot: raise HTTPException(503, "Bot not ready")
    return [o.to_dict() for o in bot.current_opportunities[:20]]

@app.get("/api/trades")
async def get_trades():
    if not bot: raise HTTPException(503, "Bot not ready")
    return [t.to_dict() for t in bot.trades_history]

@app.post("/api/force_scan")
async def force_scan():
    if not bot: raise HTTPException(503, "Bot not ready")
    await bot._scan_iteration()
    return {"status": "ok"}

@app.post("/api/positions/close")
async def close_position_manually(data: Dict[str, str]):
    if not bot: raise HTTPException(503, "Bot not ready")
    pid = data.get('position_id')
    if not pid: raise HTTPException(400, "position_id required")
    pos = bot.find_position_by_id(pid)
    if not pos: raise HTTPException(404, "Position not found")
    asyncio.create_task(bot.execute_close_position(pos, ExitReason.MANUAL))
    return {"status": "ok"}


def main():
    config = yaml.safe_load(Path("config.yaml").read_text())
    port = config.get('dashboard_port', 8000)
    host = config.get('dashboard_host', '127.0.0.1')
    print(f"🤖 {BOT_NAME} v{__version__}")
    print(f"📊 Дашборд: http://{host}:{port}")
    uvicorn.run(app, host=host, port=port)

if __name__ == "__main__":
    main()