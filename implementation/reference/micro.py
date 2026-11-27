"""The eight-mode primitive evaluator. Terms are immutable ground S trees."""
from enum import Enum
from detector import observe

from verify_selected_s import contract_at
from verify_root_walk import Cursor, fallback
from bare_macro import root, pop_address, frontier, fire_address


class Mode(Enum):
    BOUNDARY = (0, None)
    FIRST_ZERO = (1, 0)
    FIRST_ONE = (1, 1)
    SECOND_ZERO = (2, 0)
    SECOND_ONE = (2, 1)
    THIRD_ZERO = (3, 0)
    THIRD_ONE = (3, 1)
    DONE = (4, None)


def accepting(mode, term):
    return mode is Mode.BOUNDARY and observe(term) is None


def step(mode, term):
    """One actual contraction, or None precisely on a normal tree."""
    site = None
    next_mode = Mode.DONE
    if root(term):
        if mode is Mode.BOUNDARY:
            symbol = observe(term)
            if symbol is not None:
                site = pop_address(term)
                next_mode = Mode((1, symbol))
        elif mode is not Mode.DONE:
            stage, symbol = mode.value
            site = fire_address(term, symbol)
            if site is not None:
                next_mode = Mode.BOUNDARY
            elif stage < 3:
                site = frontier(term)
                next_mode = Mode((stage + 1, symbol))
    if site is None:
        site = fallback(Cursor(term))
        if site is None:
            return None
        next_mode = Mode.DONE
    return next_mode, site, contract_at(term, site)
