"""Compound POS pilot. Python 3.11+, standard library only."""
import argparse
import copy
import hashlib
import hmac
import json
import os
import re
from pathlib import Path
import secrets
import sqlite3
import threading
import time
import uuid
from datetime import datetime, timezone, timedelta
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parent
PUBLIC_URL = os.environ.get('PUBLIC_URL', '').rstrip('/')
BUILD = '2026-10-30_2-v0.4.1'
DEPARTMENTS = ['Bar 1', 'Bar 2', 'Restaurant']
METHODS = ['Cash', 'Bank', 'Mobile Money 1', 'Mobile Money 2']
MANAGER = {'manager'}
STOCK = {'manager', 'stockkeeper'}
SELL = {'manager', 'cashier'}
ROLES = {'product': MANAGER, 'customer': SELL, 'receive': STOCK,
         'request': SELL | STOCK, 'issue': STOCK, 'waste': STOCK,
         'sale': SELL, 'credit': MANAGER, 'payment': SELL, 'delivery': SELL,
         'expense': SELL, 'expense_void': MANAGER, 'asset': MANAGER,
         'asset_update': MANAGER, 'stock_count': STOCK, 'stock_adjust': MANAGER,
         'catalog_seed': MANAGER, 'product_price': MANAGER}

def now():
    return datetime.now(timezone.utc).isoformat()

def require(ok, message):
    if not ok:
        raise ValueError(message)

def integer(value, label, minimum=0):
    require(type(value) is int and minimum <= value <= 10**12, f'{label} is invalid.')
    return value

def label(value, name, limit=160):
    require(isinstance(value, str) and 0 < len(value.strip()) <= limit, f'Enter {name}.')
    return value.strip()

def initial():
    return {'products': {}, 'customers': {'unidentified': {'id': 'unidentified', 'name': 'Unidentified unpaid bills', 'phone': ''}},
            'stock': {'Central': {}, **{d: {} for d in DEPARTMENTS}}, 'requests': {}, 'sales': {}, 'movements': [], 'payments': [], 'receipts': [], 'expenses': {}, 'assets': {}, 'stockCounts': {}, 'stockAdjustments': {}}

def balance(state, sale_id):
    sale = state['sales'][sale_id]
    return sale['total'] - sum(p['amount'] for p in state['payments'] if p['sale'] == sale_id)

def customer_balance(state, customer):
    return sum(balance(state, sid) for sid, sale in state['sales'].items() if sale.get('customer') == customer)

def ensure_credit_person(state, payload):
    """Inline name capture is part of the sale/correction event and sync replay."""
    if not payload.get('customerName'):
        return
    name = label(payload['customerName'], 'the person receiving credit')
    cid = payload.get('customer')
    require(isinstance(cid, str) and 0 < len(cid) <= 100, 'Invalid customer reference.')
    if cid in state['customers']:
        require(state['customers'][cid]['name'] == name, 'Customer name changed. Select the person again.')
    else:
        state['customers'][cid] = {'id': cid, 'name': name, 'phone': '', 'email': '', 'notify': 'None'}

def credit_snapshot(state, customer, charge, stamp):
    previous = customer_balance(state, customer)
    return {'previous': previous, 'charge': charge, 'cumulative': previous + charge, 'at': stamp,
            'earlierBills': [{'id': sid, 'balance': balance(state, sid)} for sid, sale in state['sales'].items()
                             if sale.get('customer') == customer and balance(state, sid) > 0]}

def mwk(amount):
    return f'MWK {amount / 100:,.2f}'

def email_recipients(value):
    addresses = value if isinstance(value, list) else re.split(r'[,;\n]+', str(value))
    result, seen = [], set()
    for raw in addresses:
        require(isinstance(raw, str), 'Enter valid email recipients.')
        address = raw.strip()
        if not address:
            continue
        require(len(address) <= 254 and re.fullmatch(r'[^@\s,;<>]+@[^@\s,;<>]+\.[^@\s,;<>]+', address), 'Invalid recipient email: ' + address)
        if address.lower() not in seen:
            result.append(address)
            seen.add(address.lower())
    require(len(result) <= 30, 'Use at most 30 daily-report recipients.')
    return result

def daily_report(state, day):
    __import__('datetime').date.fromisoformat(day)
    local_zone = timezone(timedelta(hours=2))
    selected = [s for s in state['sales'].values() if datetime.fromisoformat(s['at']).astimezone(local_zone).date().isoformat() == day]
    lines = [f'The 18th Cave — daily sales — {day} (Malawi time)', '']
    for dep in DEPARTMENTS + ['All departments']:
        group = [s for s in selected if dep == 'All departments' or s['department'] == dep]
        lines.append(dep)
        for method in METHODS + ['Credit']:
            lines.append(f"  {method} sales: {mwk(sum(s['total'] for s in group if s['method'] == method))}")
        lines.append(f"  Total sales: {mwk(sum(s['total'] for s in group))}")
    lines += ['', 'Credit sales are not cash received. Later bill payments are excluded from these sales figures.',
              'Includes records synchronized to the central computer when this report was prepared. Late syncs or corrections may change totals.']
    return '\n'.join(lines)

def apply(state, event):
    """Validate and mutate a private state copy; caller commits atomically."""
    kind, p = event['kind'], event['payload']
    state.setdefault('receipts', [])
    state.setdefault('expenses', {})
    state.setdefault('assets', {})
    state.setdefault('stockCounts', {})
    state.setdefault('stockAdjustments', {})
    require(kind in ROLES and event['actor']['role'] in ROLES[kind], 'This action requires a different staff role.')
    eid = event['id']
    def department():
        require(p.get('department') in DEPARTMENTS, 'Choose a department.')
        return p['department']
    def product():
        require(p.get('product') in state['products'], 'Product not found.')
        return p['product']
    def movement(location, product_id, qty, reason):
        stock = state['stock'][location]
        stock[product_id] = stock.get(product_id, 0) + qty
        state['movements'].append({'event': eid, 'at': event['at'], 'location': location, 'product': product_id, 'quantity': qty, 'reason': reason, 'actor': event['actor']['name']})
    def sale_version():
        require(p.get('sale') in state['sales'], 'Sale not found.')
        sale = state['sales'][p['sale']]
        require(p.get('version') == sale['version'], 'This bill changed on another till. Refresh and review it before retrying.')
        return sale
    def payment(sale_id, amount, method, reason):
        require(method in METHODS, 'Choose a payment method.')
        state['payments'].append({'id': eid, 'sale': sale_id, 'amount': amount, 'method': method, 'reason': reason,
                                  'at': event['at'], 'actor': event['actor']['name'], 'till': event['till'], 'department': state['sales'][sale_id]['department']})
    if kind == 'catalog_seed':
        require(not state['products'], 'Catalog initialization requires an empty product list.')
        for item in p['products']:
            state['products'][item['id']] = dict(item)
            for location in state['stock']:
                movement(location, item['id'], 100, 'Temporary trial opening stock')
    elif kind == 'product':
        require(p['id'] not in state['products'], 'Product already exists.')
        name = label(p.get('name'), 'a product name')
        barcode = str(p.get('barcode', '')).strip()[:100]
        require(not barcode or not any(x['barcode'] == barcode for x in state['products'].values()), 'That barcode is already in use.')
        state['products'][p['id']] = {'id': p['id'], 'name': name, 'barcode': barcode, 'category': label(p.get('category', 'Other'), 'a category'),
                                    'price': integer(p['price'], 'Price'), 'low': integer(p.get('low', 5), 'Low-stock threshold'), 'unit': label(p.get('unit', 'each'), 'a unit')}
    elif kind == 'product_price':
        pid = product()
        item = state['products'][pid]
        require(p.get('previousPrice') == item['price'], 'Selling price changed. Refresh and review before saving.')
        label(p.get('reason'), 'a reason for the price change')
        item['price'] = integer(p.get('price'), 'Selling price')
    elif kind == 'customer':
        require(p['id'] not in state['customers'], 'Customer already exists.')
        email = str(p.get('email', '')).strip()
        require(not email or ('@' in email and '.' in email.rsplit('@', 1)[-1] and '\n' not in email and '\r' not in email), 'Enter a valid email address.')
        notify = p.get('notify', 'Unselected')
        require(notify in ['Unselected', 'None', 'Email', 'SMS', 'Both'], 'Choose a valid alert preference.')
        state['customers'][p['id']] = {'id': p['id'], 'name': label(p.get('name'), 'a customer name'), 'phone': str(p.get('phone', ''))[:60], 'email': email[:254], 'notify': notify}
    elif kind == 'receive':
        pid, qty = product(), integer(p['quantity'], 'Quantity', 1)
        cost = integer(p['unitCost'], 'Cost per base unit') if 'unitCost' in p else None
        total_cost = integer(qty * cost, 'Total purchase cost') if cost is not None else None
        movement('Central', pid, qty, 'Purchase receipt: ' + label(p.get('reference'), 'a supplier or reference'))
        state['receipts'].append({'id': eid, 'product': pid, 'quantity': qty, 'unitCost': cost, 'totalCost': total_cost, 'reference': p['reference'], 'at': event['at'], 'actor': event['actor']['name']})
    elif kind == 'expense':
        require(p['id'] not in state['expenses'], 'Expense already exists.')
        require(p.get('department') in DEPARTMENTS + ['Shared / compound'], 'Choose an expense department.')
        require(p.get('method') in METHODS, 'Choose a payment method.')
        date_value = label(p.get('date'), 'an expense date')
        require(len(date_value) == 10 and __import__('datetime').date.fromisoformat(date_value), 'Invalid expense date.')
        state['expenses'][p['id']] = {'id': p['id'], 'date': date_value, 'department': p['department'],
            'category': label(p.get('category'), 'an expense category'), 'description': label(p.get('description'), 'an expense description', 500),
            'payee': label(p.get('payee'), 'a payee'), 'reference': str(p.get('reference', ''))[:160],
            'amount': integer(p['amount'], 'Expense amount', 1), 'method': p['method'], 'at': event['at'],
            'actor': event['actor']['name'], 'till': event['till'], 'status': 'Recorded', 'version': 1}
    elif kind == 'expense_void':
        require(p.get('expense') in state['expenses'], 'Expense not found.')
        expense = state['expenses'][p['expense']]
        require(expense['status'] == 'Recorded' and p.get('version') == expense['version'], 'Expense already changed. Refresh and review.')
        expense.update(status='Voided', version=expense['version'] + 1, voidReason=label(p.get('reason'), 'a reason'), voidAt=event['at'], voidBy=event['actor']['name'])
    elif kind == 'asset':
        require(p['id'] not in state['assets'], 'Asset already exists.')
        require(p.get('status') in ['In service', 'Under repair', 'Disposed'], 'Choose an asset status.')
        qty = integer(p.get('quantity', 1), 'Quantity', 1)
        state['assets'][p['id']] = {'id': p['id'], 'name': label(p.get('name'), 'an asset name'),
            'category': label(p.get('category', 'Equipment'), 'an asset category'), 'quantity': qty,
            'location': label(p.get('location', 'Shared / compound'), 'a location'),
            'condition': label(p.get('condition', 'Good'), 'a condition'), 'status': p['status'],
            'serial': str(p.get('serial', ''))[:120], 'assignedTo': str(p.get('assignedTo', ''))[:120],
            'notes': str(p.get('notes', ''))[:500], 'version': 1, 'at': event['at'], 'actor': event['actor']['name']}
    elif kind == 'asset_update':
        require(p.get('asset') in state['assets'], 'Asset not found.')
        asset = state['assets'][p['asset']]
        require(p.get('version') == asset['version'], 'This asset changed elsewhere. Refresh and review.')
        if 'quantity' in p: asset['quantity'] = integer(p['quantity'], 'Quantity', 0)
        for key in ['location', 'condition', 'status', 'assignedTo', 'notes']:
            if key in p: asset[key] = label(p[key], key) if key not in ['assignedTo','notes'] or p[key] else ''
        asset['version'] += 1; asset['updatedAt'] = event['at']; asset['updatedBy'] = event['actor']['name']
    elif kind == 'stock_count':
        loc, pid = p.get('location'), product()
        require(loc in DEPARTMENTS + ['Central'], 'Choose a stock location.')
        counted = integer(p.get('counted'), 'Physical count', 0)
        expected = state['stock'][loc].get(pid, 0)
        cid = p['id']; require(cid not in state['stockCounts'], 'Stock count already exists.')
        state['stockCounts'][cid] = {'id': cid, 'location': loc, 'product': pid,
            'expected': expected, 'counted': counted, 'variance': counted - expected,
            'date': label(p.get('date'), 'a count date'), 'notes': str(p.get('notes', ''))[:500],
            'status': 'Pending review', 'version': 1, 'at': event['at'], 'actor': event['actor']['name']}
    elif kind == 'stock_adjust':
        require(p.get('count') in state['stockCounts'], 'Stock count not found.')
        count = state['stockCounts'][p['count']]
        require(count['status'] == 'Pending review' and p.get('version') == count['version'], 'Stock count already reviewed.')
        require(p.get('approve') is True, 'Manager approval is required.')
        delta = count['variance']
        if delta:
            movement(count['location'], count['product'], delta, 'Approved physical stock count ' + count['id'])
        count.update(status='Approved and applied', version=count['version'] + 1, approvedAt=event['at'], approvedBy=event['actor']['name'])
    elif kind == 'request':
        product(); department(); integer(p['quantity'], 'Quantity', 1)
        require(p['id'] not in state['requests'], 'Request already exists.')
        state['requests'][p['id']] = {**p, 'issued': 0, 'at': event['at'], 'actor': event['actor']['name']}
    elif kind == 'issue':
        require(p.get('request') in state['requests'], 'Request not found.')
        r = state['requests'][p['request']]
        qty = integer(p['quantity'], 'Quantity', 1)
        require(qty <= r['quantity'] - r['issued'], 'Quantity exceeds the unissued request balance.')
        require(qty <= state['stock']['Central'].get(r['product'], 0), 'Not enough central stock to issue this quantity.')
        movement('Central', r['product'], -qty, 'Issue to ' + r['department'])
        movement(r['department'], r['product'], qty, 'Issue from Central')
        r['issued'] += qty
    elif kind == 'waste':
        loc, pid, qty = department(), product(), integer(p['quantity'], 'Quantity', 1)
        require(qty <= state['stock'][loc].get(pid, 0), 'Wastage exceeds available stock.')
        movement(loc, pid, -qty, 'Wastage: ' + label(p.get('reason'), 'a reason'))
    elif kind == 'sale':
        if p.get('method') == 'Credit':
            ensure_credit_person(state, p)
        department()
        require(p['id'] not in state['sales'], 'Sale already exists.')
        require(isinstance(p.get('lines'), list) and 0 < len(p['lines']) <= 200, 'Add products to the sale.')
        total, lines = 0, []
        seen = set()
        for line in p['lines']:
            pid = line['product']
            require(pid in state['products'] and pid not in seen, 'Invalid or repeated product.')
            seen.add(pid)
            qty, price = integer(line['quantity'], 'Quantity', 1), integer(line['price'], 'Price')
            total += qty * price
            lines.append({'product': pid, 'name': state['products'][pid]['name'], 'quantity': qty, 'price': price})
        fee = integer(p.get('fee', 0), 'Delivery fee')
        total += fee
        integer(total, 'Sale total', 0)
        mode = p.get('mode', 'Counter')
        require(mode in ['Counter', 'Table / tab', 'Delivery'], 'Invalid order type.')
        require(mode == 'Delivery' or fee == 0, 'Delivery fees only apply to delivery orders.')
        if mode == 'Delivery':
            label(p.get('address'), 'a delivery address', 500)
            label(p.get('contact'), 'a delivery contact')
        if mode == 'Table / tab':
            label(p.get('table'), 'a table or tab reference')
        customer = p.get('customer', '')
        require(not customer or customer in state['customers'], 'Customer not found.')
        method = p['method']
        require(method in METHODS + ['Credit'], 'Invalid payment method.')
        require(method != 'Credit' or customer, 'Select a customer for a credit sale.')
        due = str(p.get('due', ''))
        require(not due or (len(due) == 10 and __import__('datetime').date.fromisoformat(due)), 'Invalid due date.')
        sale = {**p, 'lines': lines, 'fee': fee, 'total': total, 'version': 1, 'at': event['at'], 'actor': event['actor']['name'], 'actorId': event['actor'].get('id', event['actor']['name']), 'till': event['till'], 'deliveryStatus': 'Preparing' if mode == 'Delivery' else '', 'originalMethod': method, 'creditPostedAt': event['at'] if method == 'Credit' else ''}
        state['sales'][p['id']] = sale
        for line in lines:
            movement(p['department'], line['product'], -line['quantity'], 'Sale ' + p['id'])
        if method != 'Credit':
            payment(p['id'], total, method, 'Checkout')
    elif kind == 'credit':
        ensure_credit_person(state, p)
        sale = sale_version()
        require(sale['method'] == 'Cash' and balance(state, p['sale']) == 0, 'Only a fully paid cash sale can be corrected to credit.')
        require(p.get('customer') in state['customers'], 'Select a customer.')
        reason = label(p.get('reason'), 'a reason')
        sale.update({'method': 'Credit', 'customer': p['customer'], 'version': sale['version'] + 1, 'creditReason': reason, 'creditSnapshot': p.get('creditSnapshot'), 'creditPostedAt': event['at']})
        payment(p['sale'], -sale['total'], 'Cash', 'Cash entry reversed: ' + reason)
    elif kind == 'payment':
        sale = sale_version()
        amount = integer(p['amount'], 'Payment amount', 1)
        require(amount <= balance(state, p['sale']), 'Payment exceeds the outstanding balance.')
        payment(p['sale'], amount, p['method'], 'Customer bill payment')
        sale['version'] += 1
    elif kind == 'delivery':
        sale = sale_version()
        require(sale['mode'] == 'Delivery' and p['status'] in ['Preparing', 'Out for delivery', 'Delivered'], 'Invalid delivery update.')
        sale['deliveryStatus'] = p['status']
        sale['version'] += 1
    return state

def password_hash(password, salt):
    return hashlib.scrypt(password.encode(), salt=bytes.fromhex(salt), n=16384, r=8, p=1).hex()

class ClosingConnection(sqlite3.Connection):
    def __exit__(self, *args):
        try:
            return super().__exit__(*args)
        finally:
            self.close()

class Store:
    def __init__(self, path):
        self.path = str(path)
        Path(path).parent.mkdir(parents=True, exist_ok=True)
        self.lock = threading.RLock()
        with self.connect() as db:
            db.executescript('''CREATE TABLE IF NOT EXISTS config(key TEXT PRIMARY KEY,value TEXT NOT NULL);
                CREATE TABLE IF NOT EXISTS events(id TEXT PRIMARY KEY,event TEXT NOT NULL,status TEXT NOT NULL,seq INTEGER,error TEXT NOT NULL DEFAULT '');
                CREATE UNIQUE INDEX IF NOT EXISTS sequence ON events(seq) WHERE seq IS NOT NULL;
                CREATE TABLE IF NOT EXISTS users(id TEXT PRIMARY KEY,name TEXT NOT NULL,role TEXT NOT NULL,salt TEXT NOT NULL,hash TEXT NOT NULL);
                CREATE TABLE IF NOT EXISTS drafts(id TEXT PRIMARY KEY,data TEXT NOT NULL);
                CREATE TABLE IF NOT EXISTS alerts(id TEXT PRIMARY KEY,kind TEXT NOT NULL,channel TEXT NOT NULL,destination TEXT NOT NULL,body TEXT NOT NULL,status TEXT NOT NULL,created TEXT NOT NULL);
                CREATE TABLE IF NOT EXISTS sessions(token TEXT PRIMARY KEY,user TEXT NOT NULL,expires REAL NOT NULL);
                CREATE TABLE IF NOT EXISTS projection(id INTEGER PRIMARY KEY CHECK(id=1),data TEXT NOT NULL);''')
            for key, value in {'node': str(uuid.uuid4()), 'name': 'Till 1', 'department': 'Bar 1', 'mode': 'hub', 'hub': '', 'syncKey': secrets.token_urlsafe(32), 'lastSync': '', 'syncError': ''}.items():
                db.execute('INSERT OR IGNORE INTO config VALUES(?,?)', (key, value))
            db.execute('INSERT OR IGNORE INTO projection VALUES(1,?)', (json.dumps(initial()),))
            if os.environ.get('COMPOUND_POS_SEED_CATALOG') == '1':
                catalog = ROOT / 'initial_catalog.json'; row = db.execute('SELECT data FROM projection WHERE id=1').fetchone()
                if row and catalog.exists():
                    current = json.loads(row[0])
                    if not current.get('products'):
                        products = []
                        for item in json.loads(catalog.read_text(encoding='utf-8')).get('products', []):
                            pid = 'catalog-' + hashlib.sha1(item['name'].encode('utf-8')).hexdigest()[:12]
                            products.append({'id': pid, 'name': item['name'], 'barcode': item.get('barcode',''), 'category': item.get('category','Other'), 'price': 0, 'low': 5, 'unit': item.get('unit','each')})
                        event = {'id': str(uuid.uuid4()), 'kind': 'catalog_seed', 'payload': {'products': products}, 'actor': {'id': 'catalog-import', 'name': 'Initial trial catalog', 'role': 'manager'}, 'at': now(), 'node': self.config(db)['node'], 'till': self.config(db)['name']}
                        apply(current, event)
                        seq = db.execute('SELECT COALESCE(MAX(seq),0)+1 FROM events').fetchone()[0]
                        db.execute('INSERT INTO events VALUES(?,?,?,?,?)', (event['id'], json.dumps(event), 'accepted', seq, ''))
                        db.execute('UPDATE projection SET data=?', (json.dumps(current),))
            for key, value in {'dailyEnabled': 'false', 'dailyTime': '23:59', 'reportChannel': 'Email', 'reportEmail': '', 'reportPhone': '', 'alertsEnabledAt': ''}.items():
                db.execute('INSERT OR IGNORE INTO config VALUES(?,?)', (key, value))
            legacy_email = self.config(db).get('reportEmail', '')
            db.execute('INSERT OR IGNORE INTO config VALUES(?,?)', ('reportRecipients', json.dumps(email_recipients(legacy_email))))
    def connect(self):
        db = sqlite3.connect(self.path, timeout=30, factory=ClosingConnection)
        db.row_factory = sqlite3.Row
        db.execute('PRAGMA journal_mode=WAL')
        return db
    def config(self, db):
        return dict(db.execute('SELECT key,value FROM config').fetchall())
    def state(self, db):
        state = json.loads(db.execute('SELECT data FROM projection WHERE id=1').fetchone()[0])
        state.setdefault('receipts', [])
        state.setdefault('expenses', {})
        return state
    def save_state(self, db, state):
        db.execute('UPDATE projection SET data=? WHERE id=1', (json.dumps(state),))
    def user(self, token):
        with self.connect() as db:
            row = db.execute('SELECT u.id,u.name,u.role FROM sessions s JOIN users u ON u.id=s.user WHERE s.token=? AND s.expires>?', (token, time.time())).fetchone()
            return dict(row) if row else None
    def submit(self, kind, payload, actor, eid):
        require(kind in ROLES, 'Unknown action.')
        require(isinstance(eid, str) and len(eid) == 36, 'Invalid action identifier.')
        with self.lock, self.connect() as db:
            prior = db.execute('SELECT event,status,error FROM events WHERE id=?', (eid,)).fetchone()
            if prior:
                require(prior['status'] != 'conflict', prior['error'])
                original = json.loads(prior['event'])
                old_payload, new_payload = copy.deepcopy(original['payload']), copy.deepcopy(payload)
                old_payload.pop('creditSnapshot', None)
                new_payload.pop('creditSnapshot', None)
                if kind == 'sale':
                    for body in [old_payload, new_payload]:
                        for line in body.get('lines', []):
                            line.pop('price', None)
                require(original['kind'] == kind and old_payload == new_payload, 'This action was already saved with different details. Refresh and review the original record.')
                return original
            config = self.config(db)
            # Prices are resolved on the till, never accepted from a browser.
            state = self.state(db)
            p = copy.deepcopy(payload)
            if kind == 'receive':
                require('unitCost' in p, 'Enter the purchase cost per base unit (MWK).')
            # A browser cannot provide the frozen acknowledgment balance.
            p.pop('creditSnapshot', None)
            if kind == 'sale':
                for line in p.get('lines', []):
                    require(line['product'] in state['products'], 'Product not found.')
                    line['price'] = state['products'][line['product']]['price']
            stamp = now()
            if (kind == 'sale' and p.get('method') == 'Credit') or kind == 'credit':
                ensure_credit_person(state, p)
                customer = p.get('customer')
                require(customer in state['customers'], 'Select a registered customer.')
                if kind == 'sale':
                    require(customer != 'unidentified', 'New credit sales must be charged to a registered customer.')
                    charge = sum(integer(l['quantity'], 'Quantity', 1) * l['price'] for l in p.get('lines', [])) + integer(p.get('fee', 0), 'Delivery fee')
                else:
                    require(p.get('sale') in state['sales'], 'Sale not found.')
                    charge = state['sales'][p['sale']]['total']
                if 'creditExpected' in p:
                    require(p['creditExpected'] == customer_balance(state, customer), 'This customer balance has changed. Review the updated balance before posting the bill.')
                p['creditSnapshot'] = credit_snapshot(state, customer, charge, stamp)
            event = {'id': eid, 'kind': kind, 'payload': p, 'actor': actor, 'at': stamp, 'node': config['node'], 'till': config['name']}
            apply(state, event)
            seq = db.execute('SELECT COALESCE(MAX(seq),0)+1 FROM events').fetchone()[0] if config['mode'] == 'hub' else None
            db.execute('INSERT INTO events VALUES(?,?,?,?,?)', (eid, json.dumps(event), 'accepted' if seq else 'pending', seq, ''))
            self.save_state(db, state)
            if seq:
                self.queue_credit_alerts(db, event, state)
            if kind == 'sale' and p.get('draftId'):
                db.execute('DELETE FROM drafts WHERE id=?', (p['draftId'],))
            return event
    def replicate(self, incoming):
        require(isinstance(incoming, list) and len(incoming) <= 500, 'Sync batch is too large.')
        with self.lock, self.connect() as db:
            require(self.config(db)['mode'] == 'hub', 'This computer is not the central server.')
            state = self.state(db)
            seq = db.execute('SELECT COALESCE(MAX(seq),0) FROM events').fetchone()[0]
            rejected = {}
            for event in incoming:
                eid = label(event.get('id'), 'an event identifier', 100)
                existing = db.execute('SELECT event FROM events WHERE id=?', (eid,)).fetchone()
                if existing:
                    require(json.loads(existing[0]) == event, 'Event identifier collision.')
                    continue
                try:
                    candidate = copy.deepcopy(state)
                    apply(candidate, event)
                    seq += 1
                    db.execute('INSERT INTO events VALUES(?,?,?,?,?)', (eid, json.dumps(event), 'accepted', seq, ''))
                    state = candidate
                    self.queue_credit_alerts(db, event, state)
                except (ValueError, KeyError, TypeError) as exc:
                    rejected[eid] = str(exc)
            self.save_state(db, state)
            events = [{'seq': r['seq'], 'event': json.loads(r['event'])} for r in db.execute("SELECT seq,event FROM events WHERE status='accepted' ORDER BY seq")]
            return {'events': events, 'rejected': rejected}

    def queue_credit_alerts(self, db, event, state):
        p, kind = event['payload'], event['kind']
        if not (kind == 'credit' or (kind == 'sale' and p.get('method') == 'Credit')):
            return
        sale = state['sales'][p['sale'] if kind == 'credit' else p['id']]
        customer = state['customers'][sale['customer']]
        choice = customer.get('notify', 'Unselected')
        if choice == 'None':
            return
        channels = ['Email', 'SMS'] if choice == 'Both' else [choice]
        snapshot = sale.get('creditSnapshot')
        body = f"The 18th Cave\nHello {customer['name']}, a credit bill of {mwk(sale['total'])} was posted to your account.\nReceipt: {sale['id']}\nDepartment: {sale['department']}\n"
        if snapshot:
            body += f"Earlier balance shown on bill: {mwk(snapshot['previous'])}\nCumulative balance shown on bill: {mwk(snapshot['cumulative'])}\n"
        body += f"Current balance from centrally received records: {mwk(customer_balance(state, sale['customer']))}\nOther disconnected tills may have records not yet received. Please contact us if you do not recognize this bill."
        for channel in channels:
            destination = customer.get('email' if channel == 'Email' else 'phone', '') if channel in ['Email', 'SMS'] else ''
            status = 'Awaiting sender connection' if destination else 'Missing contact or channel'
            db.execute('INSERT OR IGNORE INTO alerts VALUES(?,?,?,?,?,?,?)', (event['id'] + ':' + channel, 'Credit bill', channel, destination, body, status, now()))

    def prepare_daily_alert(self, stamp=None):
        # Preparation only: no external service is called, and no alert is marked sent.
        local = (stamp or datetime.now(timezone.utc)).astimezone(timezone(timedelta(hours=2)))
        with self.lock, self.connect() as db:
            cfg = self.config(db)
            if cfg['mode'] != 'hub' or cfg['dailyEnabled'] != 'true':
                return
            day = local.date() if local.strftime('%H:%M') >= cfg['dailyTime'] else local.date() - timedelta(days=1)
            if cfg['alertsEnabledAt'] and day.isoformat() < cfg['alertsEnabledAt'][:10]:
                return
            body = daily_report(self.state(db), day.isoformat())
            channels = ['Email', 'SMS'] if cfg['reportChannel'] == 'Both' else [cfg['reportChannel']]
            for channel in channels:
                destinations = email_recipients(json.loads(cfg['reportRecipients'])) or email_recipients(cfg['reportEmail']) if channel == 'Email' else [cfg['reportPhone']]
                for destination in destinations or ['']:
                    status = 'Awaiting sender connection' if destination else 'Missing recipient'
                    recipient_key = hashlib.sha256(destination.lower().encode()).hexdigest()[:16]
                    db.execute('INSERT INTO alerts VALUES(?,?,?,?,?,?,?) ON CONFLICT(id) DO UPDATE SET destination=excluded.destination,body=excluded.body,status=excluded.status',
                               ('daily:' + day.isoformat() + ':' + channel + ':' + recipient_key, 'Daily sales', channel, destination, body, status, now()))
    def integrate(self, response):
        with self.lock, self.connect() as db:
            incoming_ids = {item['event']['id'] for item in response['events']}
            known_ids = {row[0] for row in db.execute("SELECT id FROM events WHERE status='accepted'")}
            require(known_ids <= incoming_ids, 'Central history is older or incomplete. Local records were preserved; administrator review is required.')
            state = initial()
            for item in response['events']:
                event = item['event']
                apply(state, event)
                db.execute('INSERT INTO events VALUES(?,?,?,?,?) ON CONFLICT(id) DO UPDATE SET status=excluded.status,seq=excluded.seq,error=excluded.error', (event['id'], json.dumps(event), 'accepted', item['seq'], ''))
            for eid, reason in response.get('rejected', {}).items():
                db.execute("UPDATE events SET status='conflict',error=? WHERE id=? AND status='pending'", (reason, eid))
            pending = db.execute("SELECT id,event FROM events WHERE status='pending' ORDER BY rowid").fetchall()
            for row in pending:
                try:
                    candidate = copy.deepcopy(state)
                    apply(candidate, json.loads(row['event']))
                    state = candidate
                except (ValueError, KeyError, TypeError) as exc:
                    db.execute("UPDATE events SET status='conflict',error=? WHERE id=?", (str(exc), row['id']))
            self.save_state(db, state)
            db.execute("UPDATE config SET value=? WHERE key='lastSync'", (now(),))
            db.execute("UPDATE config SET value='' WHERE key='syncError'")
    def sync(self):
        # Hold the local lock throughout sync so actions cannot race the rebase.
        with self.lock:
            with self.connect() as db:
                config = self.config(db)
                if config['mode'] == 'hub':
                    return
                require(config['hub'], 'Set the central server address in Settings.')
                pending = [json.loads(r[0]) for r in db.execute("SELECT event FROM events WHERE status='pending' ORDER BY rowid LIMIT 500")]
            try:
                req = Request(config['hub'].rstrip('/') + '/replicate', data=json.dumps({'events': pending}).encode(), headers={'Content-Type': 'application/json', 'Authorization': 'Bearer ' + config['syncKey']}, method='POST')
                with urlopen(req, timeout=8) as response:
                    data = response.read(50_000_001)
                    require(len(data) <= 50_000_000, 'Pilot sync capacity reached. Contact the administrator.')
                    result = json.loads(data)
                self.integrate(result)
            except Exception as exc:
                with self.connect() as db:
                    db.execute("UPDATE config SET value=? WHERE key='syncError'", (str(exc)[:300],))
                raise ValueError('Central computer unavailable. Local work is saved; sync will retry.') from exc

class Handler(BaseHTTPRequestHandler):
    server_version = 'CompoundPOS/0.1'
    def log_message(self, fmt, *args):
        if args and str(args[0]).startswith('POST /replicate'):
            return
        super().log_message(fmt, *args)
    @property
    def store(self):
        return self.server.store
    def send(self, data, status=200, content='application/json', headers=None):
        if not isinstance(data, bytes):
            data = json.dumps(data).encode()
        self.send_response(status)
        self.send_header('Content-Type', content)
        self.send_header('Content-Length', str(len(data)))
        self.send_header('Cache-Control', 'no-store')
        self.send_header('X-Content-Type-Options', 'nosniff')
        self.send_header('Content-Security-Policy', "default-src 'self'; style-src 'self'; script-src 'self'; img-src 'self' data:; frame-ancestors 'none'; base-uri 'self'; form-action 'self'")
        for k, v in (headers or {}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(data)
    def local(self):
        return bool(PUBLIC_URL) or self.client_address[0] in ['127.0.0.1', '::1']
    def auth(self):
        token = next((part.strip()[4:] for part in self.headers.get('Cookie', '').split(';') if part.strip().startswith('pos=')), '')
        user = self.store.user(token)
        require(user is not None, 'Sign in to continue.')
        return user
    def do_GET(self):
        try:
            require(self.local(), 'Open the app on this computer using localhost. Remote access is sync-only.')
            path = urlparse(self.path).path
            if path == '/health':
                return self.send({'ok': True, 'build': BUILD})
            if path in ['/', '/app.js', '/style.css', '/brand.jpg']:
                filename, mime = {'/': ('index.html', 'text/html; charset=utf-8'), '/app.js': ('app.js', 'text/javascript; charset=utf-8'), '/style.css': ('style.css', 'text/css; charset=utf-8'), '/brand.jpg': ('brand.jpg', 'image/jpeg')}[path]
                return self.send((ROOT / 'web' / filename).read_bytes(), content=mime)
            if path == '/api/bootstrap':
                with self.store.connect() as db:
                    users = [dict(r) for r in db.execute('SELECT id,name,role FROM users')]
                    return self.send({'users': users, 'setup': not users, 'hosted': bool(PUBLIC_URL), 'build': BUILD})
            user = self.auth()
            if path == '/api/state':
                with self.store.lock, self.store.connect() as db:
                    config = self.store.config(db)
                    if user['role'] != 'manager':
                        config.pop('syncKey', None)
                        config.pop('reportEmail', None)
                        config.pop('reportRecipients', None)
                        config.pop('reportPhone', None)
                    state = self.store.state(db)
                    events = [dict(r) for r in db.execute("SELECT id,event,status,error,seq FROM events WHERE status='conflict' OR rowid IN (SELECT rowid FROM events ORDER BY rowid DESC LIMIT 200) ORDER BY rowid DESC")]
                    counts = dict(db.execute('SELECT status,COUNT(*) FROM events GROUP BY status').fetchall())
                    return self.send({'state': state, 'config': config, 'user': user, 'counts': counts, 'events': events,
                                      'drafts': [json.loads(r[0]) for r in db.execute('SELECT data FROM drafts')],
                                      'users': [dict(r) for r in db.execute('SELECT id,name,role FROM users')] if user['role'] == 'manager' else [],
                                      'alerts': [dict(r) for r in db.execute('SELECT * FROM alerts ORDER BY created DESC LIMIT 100')] if user['role'] == 'manager' else []})
            if path == '/api/backup':
                require(user['role'] == 'manager', 'Manager access required.')
                with self.store.lock, self.store.connect() as source:
                    target = sqlite3.connect(':memory:')
                    try:
                        source.backup(target)
                        data = target.serialize()
                    finally:
                        target.close()
                return self.send(data, content='application/octet-stream', headers={'Content-Disposition': 'attachment; filename="compound-pos-backup.sqlite"'})
            self.send({'error': 'Not found'}, 404)
        except ValueError as exc:
            self.send({'error': str(exc)}, 403)
        except Exception:
            self.send({'error': 'Unable to complete the request. Check the server window.'}, 500)
            __import__('traceback').print_exc()
    def do_POST(self):
        try:
            path = urlparse(self.path).path
            length = int(self.headers.get('Content-Length', '0'))
            require(0 < length <= 5_000_000, 'Request is too large or empty.')
            raw = self.rfile.read(length)
            if path == '/replicate':
                with self.store.connect() as db:
                    config = self.store.config(db)
                require(hmac.compare_digest(self.headers.get('Authorization', ''), 'Bearer ' + config['syncKey']), 'Invalid pairing key.')
                require(not self.headers.get('Origin'), 'Browser sync requests are not allowed.')
                data = json.loads(raw)
                return self.send(self.store.replicate(data['events']))
            require(self.local(), 'Remote access is sync-only.')
            host = self.headers.get('Host', '')
            if PUBLIC_URL:
                require(self.headers.get('Origin') == PUBLIC_URL, 'Invalid request origin.')
            else:
                require(host.split(':')[0] in ['localhost', '127.0.0.1'], 'Use localhost to open the app.')
                require(self.headers.get('Origin') == 'http://' + host, 'Invalid request origin.')
            data = json.loads(raw)
            if path in ['/api/setup', '/api/login']:
                if PUBLIC_URL:
                    with self.store.lock:
                        attempts = getattr(self.server, 'login_attempts', {})
                        bucket = str(data.get('id', 'setup'))[:100]
                        recent = [t for t in attempts.get(bucket, []) if time.time() - t < 300]
                        require(len(recent) < 20, 'Too many sign-in attempts. Wait five minutes and try again.')
                        attempts[bucket] = recent + [time.time()]
                        if len(attempts) > 1000:
                            attempts = {bucket: attempts[bucket]}
                        self.server.login_attempts = attempts
                with self.store.lock, self.store.connect() as db:
                    if path == '/api/setup':
                        if PUBLIC_URL:
                            secret = os.environ.get('SETUP_KEY', '')
                            require(len(secret) >= 24 and hmac.compare_digest(str(data.get('setupKey', '')), secret), 'Enter the setup key configured on Render.')
                        require(db.execute('SELECT COUNT(*) FROM users').fetchone()[0] == 0, 'Setup is already complete.')
                        name = label(data.get('name'), 'your name')
                        password = label(data.get('password'), 'a password', 200)
                        require(len(password) >= 8, 'Use at least 8 characters for the password.')
                        salt, uid = secrets.token_hex(16), str(uuid.uuid4())
                        db.execute('INSERT INTO users VALUES(?,?,?,?,?)', (uid, name, 'manager', salt, password_hash(password, salt)))
                    else:
                        row = db.execute('SELECT * FROM users WHERE id=?', (data.get('id'),)).fetchone()
                        require(row and hmac.compare_digest(row['hash'], password_hash(str(data.get('password', '')), row['salt'])), 'Incorrect name or password.')
                        uid = row['id']
                    token = secrets.token_urlsafe(32)
                    db.execute('DELETE FROM sessions WHERE expires<?', (time.time(),))
                    db.execute('INSERT INTO sessions VALUES(?,?,?)', (token, uid, time.time() + 12 * 3600))
                return self.send({'ok': True}, headers={'Set-Cookie': 'pos=' + token + '; HttpOnly; SameSite=Strict; Path=/; Max-Age=43200' + ('; Secure' if PUBLIC_URL else '')})
            user = self.auth()
            if path == '/api/logout':
                with self.store.connect() as db:
                    db.execute('DELETE FROM sessions WHERE user=?', (user['id'],))
                return self.send({'ok': True}, headers={'Set-Cookie': 'pos=; HttpOnly; SameSite=Strict; Path=/; Max-Age=0'})
            if path == '/api/action':
                event = self.store.submit(data['kind'], data['payload'], user, data['id'])
                return self.send({'ok': True, 'event': event})
            if path == '/api/sync':
                self.store.sync()
                return self.send({'ok': True})
            if path == '/api/draft':
                require(user['role'] in SELL, 'Cashier access required.')
                with self.store.lock, self.store.connect() as db:
                    if data.get('remove'):
                        db.execute('DELETE FROM drafts WHERE id=?', (data['id'],))
                    else:
                        require(len(json.dumps(data)) < 100_000, 'Draft is too large.')
                        db.execute('INSERT OR REPLACE INTO drafts VALUES(?,?)', (data['id'], json.dumps(data)))
                return self.send({'ok': True})
            require(user['role'] == 'manager', 'Manager access required.')
            if path == '/api/daily-preview':
                with self.store.connect() as db:
                    return self.send({'body': daily_report(self.store.state(db), data['date'])})
            if path == '/api/alert-settings':
                with self.store.lock, self.store.connect() as db:
                    cfg = self.store.config(db)
                    require(cfg['mode'] == 'hub', 'Configure daily alerts on the central computer.')
                    require(data.get('dailyEnabled') in ['true', 'false'], 'Choose a daily report setting.')
                    require(data.get('reportChannel') in ['Email', 'SMS', 'Both'], 'Choose an alert channel.')
                    __import__('datetime').time.fromisoformat(data.get('dailyTime', ''))
                    require(len(data['dailyTime']) == 5, 'Use a time in HH:MM format.')
                    recipients = email_recipients(data.get('reportRecipients', data.get('reportEmail', '')))
                    db.execute("UPDATE config SET value=? WHERE key='reportRecipients'", (json.dumps(recipients),))
                    # Legacy field is kept empty so removing the final recipient really removes it.
                    data['reportEmail'] = ''
                    for key in ['dailyEnabled', 'dailyTime', 'reportChannel', 'reportEmail', 'reportPhone']:
                        value = str(data.get(key, '')).strip()
                        require(len(value) <= 254 and '\n' not in value and '\r' not in value, 'Invalid alert setting.')
                        db.execute('UPDATE config SET value=? WHERE key=?', (value, key))
                    for queued in db.execute("SELECT id,destination FROM alerts WHERE kind='Daily sales' AND channel='Email'").fetchall():
                        if queued['destination'].lower() not in {r.lower() for r in recipients}:
                            db.execute("UPDATE alerts SET status='Recipient removed — not sent' WHERE id=?", (queued['id'],))
                    if data['dailyEnabled'] == 'true' and not cfg['alertsEnabledAt']:
                        db.execute("UPDATE config SET value=? WHERE key='alertsEnabledAt'", (datetime.now(timezone(timedelta(hours=2))).isoformat(),))
                return self.send({'ok': True, 'sending': False})
            if path == '/api/settings':
                with self.store.lock, self.store.connect() as db:
                    config = self.store.config(db)
                    mode = data.get('mode', config['mode'])
                    require(mode in ['hub', 'till'], 'Invalid operating mode.')
                    changed_pair = mode != config['mode'] or (mode == 'till' and (data.get('hub', '') != config['hub'] or data.get('syncKey', '') != config['syncKey']))
                    require(not changed_pair or db.execute('SELECT COUNT(*) FROM events').fetchone()[0] == 0, 'Pair this till before entering transactions. Existing records cannot be moved to another central database.')
                    require(data.get('department') in DEPARTMENTS, 'Choose a department.')
                    label(data.get('name'), 'a till name')
                    if mode == 'till':
                        url = urlparse(data.get('hub', ''))
                        require(url.scheme in ['http', 'https'] and url.hostname and url.path in ['', '/'] and not url.username and not url.query and not url.fragment, 'Enter the central server address, for example http://192.168.1.10:8765')
                        require(len(data.get('syncKey', '')) >= 32, 'Enter the central pairing key.')
                    for key in ['name', 'department', 'mode', 'hub']:
                        db.execute('UPDATE config SET value=? WHERE key=?', (str(data.get(key, '')), key))
                    if mode == 'till':
                        db.execute("UPDATE config SET value=? WHERE key='syncKey'", (data['syncKey'],))
                return self.send({'ok': True})
            if path == '/api/user':
                require(data.get('role') in ['manager', 'cashier', 'stockkeeper'], 'Invalid role.')
                password = label(data.get('password'), 'a password', 200)
                require(len(password) >= 8, 'Use at least 8 characters for the password.')
                salt = secrets.token_hex(16)
                with self.store.lock, self.store.connect() as db:
                    db.execute('INSERT INTO users VALUES(?,?,?,?,?)', (str(uuid.uuid4()), label(data.get('name'), 'a name'), data['role'], salt, password_hash(password, salt)))
                return self.send({'ok': True})
            self.send({'error': 'Not found'}, 404)
        except (ValueError, KeyError, TypeError) as exc:
            self.send({'error': str(exc)}, 400)
        except Exception:
            self.send({'error': 'Unable to save. Your current form has been kept; check the server window.'}, 500)
            __import__('traceback').print_exc()

def run():
    parser = argparse.ArgumentParser()
    parser.add_argument('--data', default=os.environ.get('DATA_PATH', str(ROOT / 'data' / 'pos.sqlite')))
    parser.add_argument('--port', type=int, default=int(os.environ.get('PORT', '8765')))
    parser.add_argument('--hub', action='store_true', help='Allow other tills to reach the sync endpoint on the local network.')
    parser.add_argument('--open', action='store_true')
    args = parser.parse_args()
    if PUBLIC_URL:
        require(urlparse(PUBLIC_URL).scheme == 'https' and urlparse(PUBLIC_URL).netloc and not urlparse(PUBLIC_URL).path, 'PUBLIC_URL must be your HTTPS site origin, with no path.')
        require(len(os.environ.get('SETUP_KEY', '')) >= 24, 'Set SETUP_KEY to at least 24 characters for hosted setup.')
    store = Store(args.data)
    server = ThreadingHTTPServer(('0.0.0.0' if args.hub or PUBLIC_URL else '127.0.0.1', args.port), Handler)
    server.store = store
    def background():
        while True:
            time.sleep(20)
            try:
                store.sync()
            except Exception:
                pass
            try:
                store.prepare_daily_alert()
            except Exception:
                __import__('traceback').print_exc()
    threading.Thread(target=background, daemon=True).start()
    url = f'http://localhost:{args.port}'
    print(f'Compound POS is running at {url}\nKeep this window open. Press Ctrl+C to stop.', flush=True)
    if args.open:
        import webbrowser
        webbrowser.open(url)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        server.server_close()

if __name__ == '__main__':
    run()
