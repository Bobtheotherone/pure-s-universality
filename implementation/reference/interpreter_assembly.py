"""Interpreter assembler from the 25 November observed manuscript, commit 134f4a7.
The script checks every assembled instruction against the frozen table.
"""
class Assembly:
    """Straight-line macro expansion into INC, DECJ, JMP, HALT."""
    def __init__(self):
        self.ins, self.labels, self.names = [], {}, []
        self.serial = 0

    def label(self, name):
        assert name not in self.labels
        self.labels[name] = len(self.ins)

    def fresh(self):
        self.serial += 1
        return f"L{self.serial}"

    def reg(self, name):
        if name not in self.names:
            self.names.append(name)
        return self.names.index(name)

    def inc(self, name):
        self.ins.append(("I", self.reg(name), None))

    def dec(self, name, zero, positive=None):
        self.ins.append(("B", self.reg(name), zero, positive))

    def jump(self, label):
        self.ins.append(("J", label))

    def ifzero(self, name, label):
        self.dec(name, label)
        self.inc(name)

    def clear(self, name):
        top, done = self.fresh(), self.fresh()
        self.label(top)
        self.dec(name, done, top)
        self.label(done)

    def transfer(self, src, dest):
        assert src != dest
        top, done = self.fresh(), self.fresh()
        self.label(top)
        self.dec(src, done)
        self.inc(dest)
        self.jump(top)
        self.label(done)

    def take(self, src, dest):
        self.clear(dest)
        self.transfer(src, dest)

    def copy(self, src, dest):
        if src == dest:
            return
        t = "_restore"
        assert t not in (src, dest)
        self.clear(dest)
        top, done = self.fresh(), self.fresh()
        self.label(top)
        self.dec(src, done)
        self.inc(dest)
        self.inc(t)
        self.jump(top)
        self.label(done)
        self.transfer(t, src)

    def double(self, var):
        top, done = self.fresh(), self.fresh()
        self.label(top)
        self.dec(var, done)
        self.inc("_twice")
        self.inc("_twice")
        self.jump(top)
        self.label(done)
        self.transfer("_twice", var)

    def cons(self, head, tail, dst):
        self.copy(head, "_h")
        self.copy(tail, "_t")
        self.double("_t")
        self.inc("_t")
        top, done = self.fresh(), self.fresh()
        self.label(top)
        self.dec("_h", done)
        self.double("_t")
        self.jump(top)
        self.label(done)
        self.take("_t", dst)

    def split(self, src, head, tail):
        """Split a positive list cell, with (0,0) for an empty list."""
        self.copy(src, "_s")
        self.clear(head)
        self.clear(tail)
        divide, pairs, even, odd, end = [self.fresh() for _ in range(5)]
        self.ifzero("_s", end)
        self.label(divide)
        self.label(pairs)
        self.dec("_s", even)
        self.dec("_s", odd)
        self.inc("_quot")
        self.jump(pairs)
        self.label(even)
        self.transfer("_quot", "_s")
        self.inc(head)
        self.jump(divide)
        self.label(odd)
        self.transfer("_quot", tail)
        self.label(end)

    def finish(self):
        result = []
        for q, ins in enumerate(self.ins):
            op = ins[0]
            count = 2 if op in ("I", "B") else 1
            result.append(ins[:count] + tuple(q+1 if lab is None else self.labels[lab]
                                                for lab in ins[count:]))
        return tuple(result)


def universal_program():
    a = Assembly()
    for name in ("E", "X", "program", "argument", "out"):
        a.reg(name)
    a.cons("argument", "zero", "regs")
    a.label("fetch")
    a.copy("program", "scan")
    a.copy("pc", "index")
    a.label("skip")
    a.ifzero("scan", "bad")
    a.dec("index", "found")
    a.split("scan", "discard", "scan")
    a.jump("skip")
    a.label("found")
    a.split("scan", "ins", "discard")
    a.ifzero("ins", "output")
    a.split("ins", "op", "args")
    a.ifzero("args", "bad")
    a.split("args", "j", "target")
    a.clear("mode")
    a.dec("op", "prepare")
    a.ifzero("target", "bad")
    a.ifzero("op", "conditional")
    a.jump("bad")
    a.label("conditional")
    a.split("target", "zero_pc", "positive_pc")
    a.inc("mode")
    a.label("prepare")
    a.copy("regs", "scan")
    a.clear("prefix")
    a.label("seek")
    a.dec("j", "update")
    a.split("scan", "v", "scan")
    a.cons("v", "prefix", "prefix")
    a.jump("seek")
    a.label("update")
    a.split("scan", "value", "tail")
    a.dec("mode", "increase")
    a.dec("value", "zero_case")
    a.copy("positive_pc", "pc")
    a.jump("rebuild")
    a.label("zero_case")
    a.copy("zero_pc", "pc")
    a.jump("rebuild")
    a.label("increase")
    a.inc("value")
    a.copy("target", "pc")
    a.label("rebuild")
    a.cons("value", "tail", "scan")
    a.label("restore")
    a.ifzero("prefix", "resume")
    a.split("prefix", "v", "prefix")
    a.cons("v", "scan", "scan")
    a.jump("restore")
    a.label("resume")
    a.take("scan", "regs")
    a.jump("fetch")
    a.label("bad")
    a.jump("bad")
    a.label("output")
    a.split("regs", "out", "discard")
    a.ins.append(("H",))
    return a.finish(), tuple(a.names)


if __name__ == "__main__":
    import json
    from pathlib import Path
    recorded = json.loads(Path(__file__).with_name("universal_register_program.json").read_text())
    code, registers = universal_program()
    assert [list(x) for x in code] == recorded["instructions"]
    assert list(registers) == recorded["registers"]
    print(f"PASS {len(code)} assembled instructions; {len(registers)} register names")
