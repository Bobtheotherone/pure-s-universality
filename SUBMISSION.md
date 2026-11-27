# Computational universality of the pure S-calculus under a uniform selected reduction

**Radames Mercado-Barbosa and Anthony Langdon**

26 November 2026

We study the pure S-calculus under a uniform choice of redex. Every nonempty transition of a finite binary cyclic tag program is realized by two to four native contractions. The emitted word remains in the term and supplies input to later transitions.

The principal numerical result is Theorem 9. For every deterministic binary tape machine and every unary input, the machine halts with output y exactly when the encoded term reaches a regular halting observation with structural readout y. The statement holds at cyclic tag boundaries and after individual contractions in the eight-mode evaluator. In the latter case the control mode forms part of the observation. [Research paper](paper/Universal_Pure_S.pdf) · [Symbolic supplement](paper/Symbolic_Complete_Proof.pdf)

The two Lean declarations are `UniformS.Numerical.universal_natural_io` and `UniformS.Numerical.universal_single_natural_io`. Their foundational dependencies are `propext` and `Quot.sound`. The separate finite-menu construction of Theorem 5 has an explicit register-4 output convention and is proved in the paper. [Verification](VERIFICATION.md)

The work addresses the selected-path formulation of the Wolfram S Combinator Challenge. The selector changes the term only by contracting a native redex. The fixed halt detector acts before the numerical reader. A finite cutoff for whole-tree register replacements gives one precise restriction on what the auxiliary mechanisms can compute without the native evolution. [Challenge](https://www.combinatorprize.org/) · [Wolfram's announcement](https://writings.stephenwolfram.com/2021/06/1920-2020-and-a-20000-prize-announcing-the-s-combinator-challenge/)

For the prize form, the proposed solution is the conventional paper, `paper/Universal_Pure_S.pdf`. The symbolic derivation and executable materials accompany it in this repository. [Official submission form](https://www.wolframcloud.com/obj/forms/s-combinator-prize/submit-solution)

The archive includes the manuscripts, their LaTeX sources, the formalization, runnable examples and a Git bundle of the public research edition. [Reproducibility](REPRODUCIBILITY.md) · [Contributions](CONTRIBUTORS.md) · [Third-party notices](THIRD_PARTY_NOTICES.md)
