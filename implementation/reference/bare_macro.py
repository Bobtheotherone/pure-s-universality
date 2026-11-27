"""Bare boundary evaluator. Each recorded site is passed to the native occurrence rule."""
from verify_selected_s import S, contract_at
from detector import observe as head

def app(t):
    return t is not S

def unary(t):
    return app(t) and t[0] is S

def paired(t):
    return app(t) and unary(t[0])

def boxed(t):
    return paired(t) and t[0][1] is S

def redex(t):
    return app(t) and app(t[0]) and unary(t[0][0])

def opened(a):
    return app(a) and unary(a[0])

def frame(t):
    return app(t) and app(t[0]) and boxed(t[0][0])

def root(t):
    return paired(t) and boxed(t[0][1])

def cells(t):
    rail, address = t[1], "1"
    while frame(rail):
        li, loc = rail[0][0][1], address + "001"
        while paired(li):
            yield li[0][1], loc + "01"
            li, loc = li[1], loc + "1"
        rail, address = rail[1], address + "1"

def frontier(t):
    rail, addr = t[1], "1"
    while frame(rail):
        rail, addr = rail[1], addr + "1"
    return addr if redex(rail) else None

def word_roots(t):
    yield t[0][1][1], "011"
    for slot, loc in cells(t):
        if paired(slot):
            arm = slot[1]
            if opened(arm) and boxed(arm[0][1]):
                yield arm[0][1][1], loc + "1011"

def pop_address(t):
    if not root(t):
        return None
    for word, path in word_roots(t):
        while app(word):
            if boxed(word[0]):
                return path
            if not unary(word[0]):
                break
            word, path = word[0][1], path + "01"
    return None

def fire_address(t, symbol):
    for slot, loc in cells(t):
        if not paired(slot):
            continue
        left, right = slot[0][1], slot[1]
        if opened(left) or opened(right):
            continue
        arm = right if symbol else left
        if redex(arm):
            return loc + ("1" if symbol else "01")
    return None

def action(t):
    """Return (addresses, successor), or None if the bounded action fails."""
    symbol = head(t)
    if symbol is None:
        return None
    address = pop_address(t)
    if address is None:
        return None
    addresses = [address]
    current = contract_at(t, address)
    for attempt in range(3):
        fire = fire_address(current, symbol)
        if fire is not None:
            addresses.append(fire)
            return addresses, contract_at(current, fire)
        if attempt == 2:
            return None
        allocate = frontier(current)
        if allocate is None:
            return None
        addresses.append(allocate)
        current = contract_at(current, allocate)
    raise AssertionError("unreachable")
