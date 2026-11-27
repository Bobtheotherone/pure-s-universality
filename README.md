# Computational universality of the pure S-calculus under a uniform selected reduction

**Radames Mercado-Barbosa and Anthony Langdon**

This repository accompanies the paper and its symbolic supplement. It contains the native pure-S evaluator, the cyclic tag simulation, and Lean proofs of arbitrary numerical input/output for deterministic binary tape machines. The uniform scheduler realizes each nonempty tag step in two to four contextual S contractions. The decoder reads the terminal tape from bits retained in the term.

| Read or run | Entry point |
| --- | --- |
| Kernel-certified arbitrary natural output | [Numerical.lean](formal/PureS/Numerical.lean) and [NumericalPrimitive.lean](formal/PureS/NumericalPrimitive.lean) |
| Source and font notices | [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) |
| Mathematical proof | [Universal_Pure_S.pdf](paper/Universal_Pure_S.pdf) |
| Symbolic derivation and primitive instruction table | [Symbolic_Complete_Proof.pdf](paper/Symbolic_Complete_Proof.pdf) |
| Universal theorem after every primitive action | [Micro.lean](formal/PureS/Micro.lean) |
| Formal bare-term universal halting theorem | [Certified.lean](formal/PureS/Certified.lean) |
| Combined-interface separation with unbounded writable tree registers | [Separation.lean](formal/PureS/Separation.lean) |
| Chronological consumption and appendant dataflow | [Dataflow.lean](formal/PureS/Dataflow.lean) |
| All claims, statements and axiom dependencies | [theorem_ledger.json](verification/theorem_ledger.json) |
| Build, examples and validation | [REPRODUCIBILITY.md](REPRODUCIBILITY.md) |
| Statement of results | [SUBMISSION.md](SUBMISSION.md) |
| Related construction | [COMPETITIVE_COMPARISON.md](COMPETITIVE_COMPARISON.md) |

Theorem 9 is the tape-coded numerical result. Theorem 5 gives a second construction using a 446-instruction register interpreter and a literal unary output register. The verification record gives the scope of the formal proof for each convention. The downloadable review archive includes a Git bundle and checksums. In a Git checkout, verify the files with `sha256sum -c SHA256SUMS`.
