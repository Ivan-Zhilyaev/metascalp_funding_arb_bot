#!/usr/bin/env python3
"""
Telegram Bot для управления Funding Arbitrage Bot
Версия: 1.1.0
"""

import os
import sys
import asyncio
import logging
from pathlib import Path
from typing import Optional, Dict, Any

from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup, ReplyKeyboardMarkup, KeyboardButton
from telegram.ext import Application, CommandHandler, CallbackQueryHandler, ContextTypes, MessageHandler, filters

sys.path.insert(0, str(Path(__file__).parent))


class TelegramManager:
    def __init__(self, bot_instance):
        self.bot = bot_instance
        self.logger = logging.getLogger('telegram_bot')
        self._app: Optional[Application] = None

        env_path = Path(__file__).parent / '.env'
        if env_path.exists():
            with open(env_path, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith('#') and '=' in line:
                        key, value = line.split('=', 1)
                        key = key.strip()
                        value = value.strip().strip('"').strip("'")
                        os.environ[key] = value

        self.token = os.environ.get('TELEGRAM_BOT_TOKEN')
        self.chat_id = os.environ.get('TELEGRAM_CHAT_ID')

        if not self.token or not self.chat_id:
            self.logger.warning("⚠️ TELEGRAM_BOT_TOKEN или TELEGRAM_CHAT_ID не найдены в .env")
            self.enabled = False
        else:
            self.enabled = True

    # ========================================================================
    # Запуск
    # ========================================================================

    async def start_bot(self):
        if not self.enabled:
            return

        self._app = (
            Application.builder()
            .token(self.token)
            .connect_timeout(30)
            .read_timeout(30)
            .write_timeout(30)
            .build()
        )

        self._app.add_handler(CommandHandler("start", self.cmd_start))
        self._app.add_handler(CommandHandler("status", self.cmd_status))
        self._app.add_handler(CommandHandler("positions", self.cmd_positions))
        self._app.add_handler(CommandHandler("signals", self.cmd_signals))
        self._app.add_handler(CommandHandler("balance", self.cmd_balance))
        self._app.add_handler(CommandHandler("config", self.cmd_config))
        self._app.add_handler(CommandHandler("trading", self.cmd_trading))
        self._app.add_handler(CommandHandler("mode", self.cmd_mode))
        self._app.add_handler(CommandHandler("margin", self.cmd_margin))
        self._app.add_handler(CommandHandler("close", self.cmd_close))
        self._app.add_handler(CallbackQueryHandler(self.handle_callback))
        self._app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, self.handle_menu_button))
        self._app.add_error_handler(self._error_handler)

        max_attempts = 3
        for attempt in range(max_attempts):
            try:
                await self._app.initialize()
                await self._app.start()
                await self._app.updater.start_polling(
                    allowed_updates=Update.ALL_TYPES,
                    poll_interval=0.5,
                )
                self.logger.info("✅ Telegram Bot запущен")

                # Устанавливаем Reply-кнопку меню
                menu_button = ReplyKeyboardMarkup(
                    [[KeyboardButton("📊 Меню бота")]],
                    resize_keyboard=True,
                    one_time_keyboard=False,
                    input_field_placeholder="Нажмите для меню"
                )
                await self.send_message("🚀 Бот запущен и готов к работе!", reply_markup=menu_button)
                return
            except Exception as e:
                self.logger.warning(f"⚠️ Попытка {attempt+1} подключения к Telegram не удалась: {e}")
                if attempt < max_attempts - 1:
                    await asyncio.sleep(5)
                else:
                    self.logger.error("❌ Не удалось подключиться к Telegram после 3 попыток")
                    self.enabled = False

    async def _error_handler(self, update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
        self.logger.error(f"❌ Ошибка Telegram: {context.error}")
        try:
            if update and hasattr(update, 'callback_query') and update.callback_query:
                await update.callback_query.answer("⚠️ Произошла ошибка, попробуйте позже", show_alert=True)
        except:
            pass

    async def stop_bot(self):
        if self._app:
            try:
                await self._app.updater.stop()
                await self._app.stop()
                await self._app.shutdown()
            except:
                pass

    # ========================================================================
    # Обработчик Reply-кнопки
    # ========================================================================

    async def handle_menu_button(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        if update.message and update.message.text == "📊 Меню бота":
            await self.cmd_start(update, context)

    # ========================================================================
    # Отправка сообщений
    # ========================================================================

    async def send_message(self, text: str, reply_markup=None):
        if not self.enabled or not self._app:
            return
        try:
            await self._app.bot.send_message(
                chat_id=self.chat_id,
                text=text,
                reply_markup=reply_markup,
                parse_mode='HTML'
            )
        except Exception as e:
            self.logger.error(f"❌ Ошибка отправки сообщения: {e}")

    async def notify(self, text: str):
        await self.send_message(f"🔔 {text}")

    # ========================================================================
    # Клавиатуры
    # ========================================================================

    def main_keyboard(self):
        return InlineKeyboardMarkup([
            [
                InlineKeyboardButton("🔄 Обновить", callback_data="refresh"),
                InlineKeyboardButton("📊 Позиции", callback_data="positions"),
            ],
            [
                InlineKeyboardButton("🎯 Сигналы", callback_data="signals"),
                InlineKeyboardButton("💰 Баланс", callback_data="balance"),
            ],
            [
                InlineKeyboardButton("📈 Торговля: " + ("🟢" if self.bot.trading_enabled else "🔴"), callback_data="toggle_trading"),
                InlineKeyboardButton("🧪 Режим: " + ("ТЕСТ" if self.bot.is_test_mode else "РЕАЛ"), callback_data="toggle_mode"),
            ],
            [
                InlineKeyboardButton("⚙️ Конфиг", callback_data="config"),
                InlineKeyboardButton("🔙 Скрыть", callback_data="delete"),
            ],
        ])

    def positions_keyboard(self):
        buttons = []
        for pos in self.bot.active_positions:
            pos_id = f"{pos.symbol}_{pos.spot_exchange}_{pos.perp_exchange}_{pos.entry_time}"
            label = f"🔒 {pos.symbol} ({pos.spot_exchange}/{pos.perp_exchange})"
            buttons.append([InlineKeyboardButton(label, callback_data=f"close_{pos_id}")])
        buttons.append([
            InlineKeyboardButton("🔄 Обновить", callback_data="positions"),
            InlineKeyboardButton("🔙 Назад", callback_data="refresh"),
        ])
        return InlineKeyboardMarkup(buttons)

    def back_keyboard(self):
        return InlineKeyboardMarkup([
            [InlineKeyboardButton("🔙 Назад", callback_data="refresh")]
        ])

    # ========================================================================
    # Команды
    # ========================================================================

    async def cmd_start(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        status = self.bot.get_status()
        text = (
            f"🤖 <b>{status['bot_name']} v{status['version']}</b>\n\n"
            f"📊 Статус:\n"
            f"• Режим: {'ТЕСТОВЫЙ' if status['test_mode'] else 'ТОРГОВЛЯ'}\n"
            f"• Торговля: {'🟢 ВКЛЮЧЕНА' if status['trading_enabled'] else '🔴 ВЫКЛЮЧЕНА'}\n"
            f"• Биржи: {status['exchange_status']}\n"
            f"• MetaScalp: {'ПОДКЛЮЧЕН' if status['connection_state'] == 'connected' else 'ОТКЛЮЧЕН'}\n"
            f"• Позиций: {status['active_positions_count']} "
            f"(BUY: {status['long_positions_count']} | SELL: {status['short_positions_count']})\n"
            f"• Общий PnL: {status['total_pnl']:.4f} USDT\n"
            f"• Аптайм: {status['uptime_seconds'] // 3600}ч {(status['uptime_seconds'] % 3600) // 60}м\n"
            f"• Кэш: {status['cache_info']['instruments_in_cache']} инструментов"
        )
        if update.message:
            await update.message.reply_text(text, reply_markup=self.main_keyboard(), parse_mode='HTML')
        elif update.callback_query:
            await update.callback_query.message.reply_text(text, reply_markup=self.main_keyboard(), parse_mode='HTML')

    async def cmd_status(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        status = self.bot.get_status()
        text = (
            f"📊 <b>Статус</b>\n\n"
            f"• Режим: {'ТЕСТОВЫЙ' if status['test_mode'] else 'ТОРГОВЛЯ'}\n"
            f"• Торговля: {'🟢 ВКЛЮЧЕНА' if status['trading_enabled'] else '🔴 ВЫКЛЮЧЕНА'}\n"
            f"• Биржи: {status['exchange_status']}\n"
            f"• Позиций: {status['active_positions_count']} (BUY: {status['long_positions_count']} | SELL: {status['short_positions_count']})\n"
            f"• Общий PnL: {status['total_pnl']:.4f} USDT\n"
            f"• Аптайм: {status['uptime_seconds'] // 3600}ч {(status['uptime_seconds'] % 3600) // 60}м\n"
            f"• Сигналов: {status['level1_stats']['signals_found']}\n"
            f"• Кэш: {status['cache_info']['instruments_in_cache']} инструментов\n"
            f"• Сканирований: {status['scan_count']}"
        )
        await update.message.reply_text(text, reply_markup=self.main_keyboard(), parse_mode='HTML')

    async def cmd_positions(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        status = self.bot.get_status()
        positions = status['positions']

        if not positions:
            text = "📊 <b>Открытые позиции</b>\n\nНет открытых позиций."
        else:
            lines = [f"📊 <b>Открытые позиции ({len(positions)})</b>\n"]
            for p in positions:
                direction = "🟢 BUY" if p['direction'] == 'BUY_SPOT_SHORT_PERP' else "🔴 SELL"
                pnl = p.get('estimated_pnl', 0)
                pnl_str = f"+{pnl:.4f}" if pnl >= 0 else f"{pnl:.4f}"
                lines.append(
                    f"{direction} <b>{p['symbol']}</b> ({p['spot_exchange']}/{p['perp_exchange']})\n"
                    f"   PnL: {pnl_str} USDT\n"
                    f"   Ставка: {(p['entry_funding_rate']*100):.4f}%\n"
                    f"   Выплат: {p.get('funding_payments_count', 0)} "
                    f"({(p.get('funding_payments_received', 0)):.4f} USDT)\n"
                    f"   След. выплата: {p.get('funding_time_str', '—')}"
                )
            text = "\n".join(lines)

        await update.message.reply_text(text, reply_markup=self.positions_keyboard(), parse_mode='HTML')

    async def cmd_signals(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        status = self.bot.get_status()
        signals = status['current_opportunities']

        if not signals:
            text = "🎯 <b>Актуальные сигналы</b>\n\nНет сигналов."
        else:
            lines = [f"🎯 <b>Актуальные сигналы ({len(signals)})</b>\n"]
            for i, s in enumerate(signals[:10], 1):
                direction = "📈" if s['direction'] == 'LONG_SPOT_SHORT_PERP' else "📉"
                lines.append(
                    f"#{i} {direction} <b>{s['symbol']}</b>\n"
                    f"   {s['spot_exchange']}/{s['perp_exchange']}\n"
                    f"   Ставка: {(s['funding_rate']*100):.4f}%\n"
                    f"   Прибыль: {s['net_profit_bps']:.1f} bps"
                )
            text = "\n".join(lines)

        await update.message.reply_text(text, reply_markup=self.back_keyboard(), parse_mode='HTML')

    async def cmd_balance(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        lines = ["💰 <b>Балансы MetaScalp</b>\n"]
        has_data = False

        for ex_name, conns in self.bot.metascalp_connections.items():
            spot_id = conns.get('spot_id')
            perp_id = conns.get('perp_id')

            spot_bal = "—"
            perp_bal = "—"

            if spot_id:
                try:
                    data = await self.bot.fetch_balances_direct(spot_id)
                    spot_bal = f"{data.get('USDT', 0):.4f}"
                    has_data = True
                except:
                    pass

            if perp_id:
                try:
                    data = await self.bot.fetch_balances_direct(perp_id)
                    perp_bal = f"{data.get('USDT', 0):.4f}"
                    has_data = True
                except:
                    pass

            lines.append(f"• <b>{ex_name.upper()}</b>: S={spot_bal} / P={perp_bal}")

        if not has_data:
            text = "💰 <b>Балансы</b>\n\nНет данных о балансах."
        else:
            text = "\n".join(lines)

        if update.message:
            await update.message.reply_text(text, reply_markup=self.back_keyboard(), parse_mode='HTML')
        elif update.callback_query:
            await update.callback_query.edit_message_text(text, reply_markup=self.back_keyboard(), parse_mode='HTML')

    async def cmd_config(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        cfg = self.bot.config
        text = (
            f"⚙️ <b>Настройки</b>\n\n"
            f"• scan_interval: {cfg.get('scan_interval', 5)} сек\n"
            f"• base_order_amount: {cfg.get('base_order_amount', 100)} USDT\n"
            f"• min_profit_bps: {cfg.get('min_profit_bps', 10)}\n"
            f"• leverage: {cfg.get('leverage', 3)}x\n"
            f"• margin_enabled: {'Да' if cfg.get('margin_enabled') else 'Нет'}\n"
            f"• max_positions_per_side: {cfg.get('max_positions_per_side', 5)}\n"
            f"• max_position_age_hours: {cfg.get('max_position_age_hours', 24)}ч\n"
            f"• max_price_change_pct: {cfg.get('max_price_change_pct', 15)}%\n"
            f"• cache_rebuild_interval: {cfg.get('cache_rebuild_interval_minutes', 30)} мин\n"
            f"• check_trading_status: {'Да' if cfg.get('check_trading_status') else 'Нет'}\n"
            f"• normalize_symbols: {'Да' if cfg.get('normalize_symbols') else 'Нет'}"
        )
        await update.message.reply_text(text, reply_markup=self.back_keyboard(), parse_mode='HTML')

    async def cmd_trading(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        args = context.args
        if args and args[0].lower() in ('on', 'вкл', '1', 'true'):
            self.bot.update_config({'trading_enabled': True})
            await update.message.reply_text("✅ Торговля ВКЛЮЧЕНА", reply_markup=self.main_keyboard())
        elif args and args[0].lower() in ('off', 'выкл', '0', 'false'):
            self.bot.update_config({'trading_enabled': False})
            await update.message.reply_text("🔴 Торговля ВЫКЛЮЧЕНА", reply_markup=self.main_keyboard())
        else:
            state = "🟢 ВКЛЮЧЕНА" if self.bot.trading_enabled else "🔴 ВЫКЛЮЧЕНА"
            await update.message.reply_text(
                f"📈 Торговля: {state}\nИспользуйте: /trading on или /trading off",
                reply_markup=self.main_keyboard()
            )

    async def cmd_mode(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        args = context.args
        if args and args[0].lower() in ('test', 'тест'):
            self.bot.update_config({'test_mode': True})
            await update.message.reply_text("🧪 Режим: ТЕСТОВЫЙ", reply_markup=self.main_keyboard())
        elif args and args[0].lower() in ('real', 'реал', 'trade', 'торговля'):
            self.bot.update_config({'test_mode': False})
            await update.message.reply_text("💹 Режим: ТОРГОВЛЯ", reply_markup=self.main_keyboard())
        else:
            state = "ТЕСТОВЫЙ" if self.bot.is_test_mode else "ТОРГОВЛЯ"
            await update.message.reply_text(
                f"🧪 Режим: {state}\nИспользуйте: /mode test или /mode real",
                reply_markup=self.main_keyboard()
            )

    async def cmd_margin(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        args = context.args
        if args and args[0].lower() in ('on', 'вкл', '1', 'true'):
            self.bot.update_config({'margin_enabled': True})
            await update.message.reply_text("📈 Маржинальная торговля ВКЛЮЧЕНА", reply_markup=self.main_keyboard())
        elif args and args[0].lower() in ('off', 'выкл', '0', 'false'):
            self.bot.update_config({'margin_enabled': False})
            await update.message.reply_text("📉 Маржинальная торговля ВЫКЛЮЧЕНА", reply_markup=self.main_keyboard())
        else:
            state = "ВКЛЮЧЕНА" if self.bot.margin_enabled else "ВЫКЛЮЧЕНА"
            await update.message.reply_text(
                f"📈 Маржинальная торговля: {state}\nИспользуйте: /margin on или /margin off",
                reply_markup=self.main_keyboard()
            )

    async def cmd_close(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        args = context.args
        if not args:
            await update.message.reply_text(
                "Укажите символ позиции. Например: /close GUA/USDT:USDT",
                reply_markup=self.positions_keyboard()
            )
            return

        symbol = args[0]
        found = False
        for pos in self.bot.active_positions:
            if pos.symbol.upper().startswith(symbol.upper()):
                from scanner import ExitReason
                asyncio.create_task(self.bot.execute_close_position(pos, ExitReason.MANUAL))
                await update.message.reply_text(
                    f"🔒 Закрываю {pos.symbol}...",
                    reply_markup=self.positions_keyboard()
                )
                found = True
                break

        if not found:
            await update.message.reply_text(
                f"❌ Позиция с символом '{symbol}' не найдена.",
                reply_markup=self.positions_keyboard()
            )

    # ========================================================================
    # Callback-обработчик
    # ========================================================================

    async def handle_callback(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        query = update.callback_query

        if query.data != "delete":
            await query.answer()
        else:
            await query.answer()

        try:
            if query.data == "refresh":
                await self.cmd_start_via_callback(query)
            elif query.data == "positions":
                await self.cmd_positions_via_callback(query)
            elif query.data == "signals":
                await self.cmd_signals_via_callback(query)
            elif query.data == "balance":
                await self.cmd_balance_via_callback(query)
            elif query.data == "config":
                await self.cmd_config_via_callback(query)
            elif query.data == "toggle_trading":
                new_val = not self.bot.trading_enabled
                self.bot.update_config({'trading_enabled': new_val})
                await self.cmd_start_via_callback(query)
            elif query.data == "toggle_mode":
                new_val = not self.bot.is_test_mode
                self.bot.update_config({'test_mode': new_val})
                await self.cmd_start_via_callback(query)
            elif query.data == "delete":
                await query.delete_message()
            elif query.data.startswith("close_"):
                pos_id = query.data[6:]
                pos = self.bot.find_position_by_id(pos_id)
                if pos:
                    from scanner import ExitReason
                    asyncio.create_task(self.bot.execute_close_position(pos, ExitReason.MANUAL))
                    await query.edit_message_text(
                        f"🔒 Закрываю {pos.symbol}...",
                        reply_markup=self.positions_keyboard()
                    )
                else:
                    await query.answer("Позиция уже закрыта", show_alert=True)
        except Exception as e:
            self.logger.error(f"❌ Ошибка в callback: {e}")
            try:
                await query.answer("⚠️ Ошибка. Попробуйте /start", show_alert=True)
            except:
                pass

    # ========================================================================
    # Callback-версии команд
    # ========================================================================

    async def cmd_start_via_callback(self, query):
        status = self.bot.get_status()
        text = (
            f"🤖 <b>{status['bot_name']} v{status['version']}</b>\n\n"
            f"📊 Статус:\n"
            f"• Режим: {'ТЕСТОВЫЙ' if status['test_mode'] else 'ТОРГОВЛЯ'}\n"
            f"• Торговля: {'🟢 ВКЛЮЧЕНА' if status['trading_enabled'] else '🔴 ВЫКЛЮЧЕНА'}\n"
            f"• Биржи: {status['exchange_status']}\n"
            f"• Позиций: {status['active_positions_count']} "
            f"(BUY: {status['long_positions_count']} | SELL: {status['short_positions_count']})\n"
            f"• Общий PnL: {status['total_pnl']:.4f} USDT\n"
            f"• Аптайм: {status['uptime_seconds'] // 3600}ч {(status['uptime_seconds'] % 3600) // 60}м"
        )
        await query.edit_message_text(text, reply_markup=self.main_keyboard(), parse_mode='HTML')

    async def cmd_positions_via_callback(self, query):
        try:
            status = self.bot.get_status()
            positions = status['positions']
            if not positions:
                text = "📊 <b>Открытые позиции</b>\n\nНет открытых позиций."
            else:
                lines = [f"📊 <b>Открытые позиции ({len(positions)})</b>\n"]
                for p in positions:
                    direction = "🟢 BUY" if p['direction'] == 'BUY_SPOT_SHORT_PERP' else "🔴 SELL"
                    pnl = p.get('estimated_pnl', 0)
                    pnl_str = f"+{pnl:.4f}" if pnl >= 0 else f"{pnl:.4f}"
                    lines.append(
                        f"{direction} <b>{p['symbol']}</b> ({p['spot_exchange']}/{p['perp_exchange']})\n"
                        f"   PnL: {pnl_str} USDT | Ставка: {(p['entry_funding_rate']*100):.4f}%\n"
                        f"   Выплат: {p.get('funding_payments_count', 0)} "
                        f"({(p.get('funding_payments_received', 0)):.4f} USDT)\n"
                        f"   След. выплата: {p.get('funding_time_str', '—')}"
                    )
                text = "\n".join(lines)
            await query.edit_message_text(text, reply_markup=self.positions_keyboard(), parse_mode='HTML')
        except Exception as e:
            self.logger.error(f"❌ Ошибка в cmd_positions_via_callback: {e}")
            await query.answer("Ошибка загрузки позиций", show_alert=True)

    async def cmd_signals_via_callback(self, query):
        status = self.bot.get_status()
        signals = status['current_opportunities']
        if not signals:
            text = "🎯 <b>Актуальные сигналы</b>\n\nНет сигналов."
        else:
            lines = [f"🎯 <b>Актуальные сигналы ({len(signals)})</b>\n"]
            for i, s in enumerate(signals[:10], 1):
                direction = "📈" if s['direction'] == 'LONG_SPOT_SHORT_PERP' else "📉"
                lines.append(
                    f"#{i} {direction} <b>{s['symbol']}</b>\n"
                    f"   {s['spot_exchange']}/{s['perp_exchange']}\n"
                    f"   Ставка: {(s['funding_rate']*100):.4f}% | Прибыль: {s['net_profit_bps']:.1f} bps"
                )
            text = "\n".join(lines)
        await query.edit_message_text(text, reply_markup=self.back_keyboard(), parse_mode='HTML')

    async def cmd_balance_via_callback(self, query):
        lines = ["💰 <b>Балансы MetaScalp</b>\n"]
        has_data = False
        for ex_name, conns in self.bot.metascalp_connections.items():
            spot_id = conns.get('spot_id')
            perp_id = conns.get('perp_id')
            spot_bal = "—"
            perp_bal = "—"
            if spot_id:
                try:
                    data = await self.bot.fetch_balances_direct(spot_id)
                    spot_bal = f"{data.get('USDT', 0):.4f}"
                    has_data = True
                except:
                    pass
            if perp_id:
                try:
                    data = await self.bot.fetch_balances_direct(perp_id)
                    perp_bal = f"{data.get('USDT', 0):.4f}"
                    has_data = True
                except:
                    pass
            lines.append(f"• <b>{ex_name.upper()}</b>: S={spot_bal} / P={perp_bal}")
        if not has_data:
            text = "💰 <b>Балансы</b>\n\nНет данных о балансах."
        else:
            text = "\n".join(lines)
        await query.edit_message_text(text, reply_markup=self.back_keyboard(), parse_mode='HTML')

    async def cmd_config_via_callback(self, query):
        cfg = self.bot.config
        text = (
            f"⚙️ <b>Настройки</b>\n\n"
            f"• scan_interval: {cfg.get('scan_interval', 5)} сек\n"
            f"• base_order_amount: {cfg.get('base_order_amount', 100)} USDT\n"
            f"• min_profit_bps: {cfg.get('min_profit_bps', 10)}\n"
            f"• leverage: {cfg.get('leverage', 3)}x\n"
            f"• max_positions_per_side: {cfg.get('max_positions_per_side', 5)}\n"
            f"• max_position_age_hours: {cfg.get('max_position_age_hours', 24)}ч\n"
            f"• max_price_change_pct: {cfg.get('max_price_change_pct', 15)}%\n"
            f"• cache_rebuild_interval: {cfg.get('cache_rebuild_interval_minutes', 30)} мин"
        )
        await query.edit_message_text(text, reply_markup=self.back_keyboard(), parse_mode='HTML')


if __name__ == "__main__":
    print("Этот файл должен запускаться из scanner.py")
    print("Используйте: python scanner.py")