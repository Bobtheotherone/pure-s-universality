"""Public binary and universal numerical entry points. Only contract_at mutates an occurrence."""
import argparse
import json
from dataclasses import dataclass, field
from pathlib import Path
import verify_root_walk as walker
import verify_selected_s as native


def binary_seed(program, word):
    if not program or any(b not in (0, 1) for w in [*program, word] for b in w):
        raise ValueError("a nonempty cyclic program of binary words is required")
    return native.cyclic_seed(tuple(map(tuple, program)), tuple(word))


def binary_read(term):
    try:
        flags = walker.sweep(walker.Cursor(term), "read")
    except walker.BadShape:
        return None
    v = native.inspect(term)
    return {"queue": tuple(v.live), "stable": flags.spent == flags.committed,
            "halt": flags.spent == flags.committed and not flags.has_live}


def binary_step(term):
    address = walker.select(term)
    return term if address is None else native.contract_at(term, address)


def bitword(text):
    if any(c not in "01" for c in text):
        raise ValueError("binary words contain only 0 and 1")
    return tuple(map(int,text))


def unary_tag(t, limit):
    n = 0
    while t is not None:
        walker.require(t[0] is None and n+1 < limit)
        n += 1
        t = t[1]
    return n


def inspect_menu(menu, depth, nstates):
    """Return the possibly fired leaf. The stack contains finite-layout cursor paths."""
    work = [(menu,0,"")]
    found = None
    while work:
        t,level,path = work.pop()
        walker.require(walker.pair_shape(t))
        if level == depth:
            walker.require(t[0][1] == (None,None))
            if walker.status(t[1]) == "fired":
                walker.require(found is None)
                qv = t[1][0][1]
                walker.require(walker.pair_shape(qv) and walker.box_shape(qv[1]))
                found = (unary_tag(qv[0][1],nstates), qv[1][1],path+"10111")
        else:
            walker.require(t[0][1] is None and walker.pair_shape(t[1]))
            work.append((t[1][1],level+1,path+"11"))
            work.append((t[1][0][1],level+1,path+"101"))
    return found


@dataclass
class NumericView:
    live: list = field(default_factory=list)
    first: str | None = None
    last: int | None = None
    pop_parity: int = 0
    fire_parity: int = 0
    state: int = 0
    free: tuple | None = None
    frontier: str = ""


def add_word(v,t,path,alphabet):
    while t is not None:
        walker.require(t[0] is not None)
        if t[0][0] == (None,None):
            v.live.append(unary_tag(t[0][1],alphabet))
            if v.first is None:
                v.first = path
            t,path = t[1],path+"1"
        else:
            walker.require(t[0][0] is None and t[1] is not None and v.first is None)
            v.last = unary_tag(t[1][0],alphabet)
            v.pop_parity ^= 1
            t,path = t[0][1],path+"01"


def numeric_read(term,nstates,alphabet):
    """Strict parser with opaque ghosts. A failed parse is returned as None."""
    try:
        walker.require(walker.pair_shape(term) and walker.box_shape(term[0][1]))
        v=NumericView()
        add_word(v,term[0][1][1],"011",alphabet)
        rail,path = term[1],"1"
        depth=(nstates*alphabet-1).bit_length()
        while walker.degree(rail)==4:
            f=rail[0][0]
            walker.require(walker.box_shape(f))
            cell=f[1]
            walker.require(walker.pair_shape(cell) and cell[1] is None)
            menu=cell[0][1]
            mp=path+"00101"
            opened=inspect_menu(menu,depth,nstates)
            if opened is None:
                if v.free is None:
                    v.free=(menu,mp)
            else:
                walker.require(v.free is None)
                v.state,word,rel=opened
                v.fire_parity ^= 1
                add_word(v,word,mp+rel,alphabet)
            rail,path=rail[1],path+"1"
        walker.require(walker.degree(rail)==3)
        v.frontier=path
        return v
    except walker.BadShape:
        return None


def numeric_output(v,halt,output_letter):
    if v is None or v.pop_parity != v.fire_parity or v.state != halt:
        return None
    return v.live.count(output_letter)


def numeric_step(term,nstates,alphabet,halt):
    v=numeric_read(term,nstates,alphabet)
    if v is None:
        addr=walker.fallback(walker.Cursor(term))
    elif v.pop_parity == v.fire_parity:
        addr=v.first if v.first is not None and v.state!=halt else v.frontier
    elif v.free is None:
        addr=v.frontier
    elif v.last is None:
        addr=walker.fallback(walker.Cursor(term))
    else:
        menu,path=v.free
        addr=path+native.menu_address(menu,v.state*alphabet+v.last)
    return term if addr is None else native.contract_at(term,addr)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("program",help="comma-separated appendants, e.g. 1, for [1,empty]")
    parser.add_argument("word")
    parser.add_argument("--limit",type=int,default=12)
    a=parser.parse_args()
    t=binary_seed([bitword(w) for w in a.program.split(",")],bitword(a.word))
    for k in range(a.limit+1):
        r=binary_read(t)
        if r and r["stable"]:
            print(json.dumps({"contractions":k,"word":"".join(map(str,r["queue"])),"halt":r["halt"]}))
            if r["halt"]:
                return
        if k<a.limit:
            t=binary_step(t)


if __name__=="__main__":
    main()
