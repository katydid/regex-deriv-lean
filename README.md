# regex-deriv-lean

Proofs for derivatives of regular expressions in [Lean4](https://leanprover.github.io/).

![Check Proofs](https://github.com/katydid/regex-deriv-lean/workflows/Check%20Proofs/badge.svg)

This derivatives for regular expressions is used as the foundation for the katydid validation algorithm.
Understanding how derivatives work for regular expressions is important before trying to understand the katydid validation algorithm.

This repo contains:

 * [Correctness and decidability proof for the derivative algorithm](./RegexDeriv/Regex/SimpleRegex.lean)
 * [Correct by construction proof for the derivative algorithm](./RegexDeriv/Regex/IndexedRegex.lean)
 * [Proofs for simplification rules](./RegexDeriv/Regex/Language.lean)
 * [Implementation of capturing using derivatives](./RegexDeriv/Group/)
 * [Implementation of capturing using derivatives with extensions](./RegexDeriv/Capture/)
 * Lean4 [learnings](./learnings/) we had while recreating algorithms and proofs in Lean.

A lot of work was done by building on [our previous work in Coq](https://github.com/katydid/regex-deriv-coq) and our attempt at [Reproving Agda in Lean](https://github.com/katydid/regex-deriv-reproving-agda-in-lean)

## Contributing

The contributing guidelines are short and shouldn't be surprising.
Please read the [contributing guidelines](./CONTRIBUTING.md). 

### Understanding Brzozowski derivatives

Contributing to this repo requires an understanding the underlying algorithm that is the subject of the proofs in this repo:

  - [Derivatives of Regular Expressions explained](https://medium.com/@awalterschulze/how-to-take-the-derivative-of-a-regular-expression-explained-2e7cea15028d)
  - [Derivatives of Context-Free Grammars explained](https://medium.com/@awalterschulze/derivatives-of-context-free-grammars-explained-3f930c5e363b) (only the simplification rules, smart constructors and memoization are important)
  - [Derivatives of Symbolic Automata explained](https://medium.com/@awalterschulze/derivatives-of-symbolic-automata-explained-4673dee6af82)

### Understanding LeanProver

This repo also requires an understanding of proof assistants, since all the proofs in this repo are done using LeanProver:

  - Knowledge of dependent types, induction and understanding the difference between a property `True` and a boolean `true`. We recommend reading [The Little Typer](https://mitpress.mit.edu/9780262536431/the-little-typer/) to gain an understanding of the basics.
  - Experience with an Interactive Theorem Prover, like Coq or Lean, including using tactics and Inductive Predicates. If you are unfamiliar with interactive theorem provers you can watch our [talk](https://www.youtube.com/watch?v=-NHWF4ntc1I) for a taste. We recommend reading [Coq in a Hurry](https://cel.archives-ouvertes.fr/file/index/docid/459139/filename/coq-hurry.pdf) as a quick overview and [Coq Art](https://www.labri.fr/perso/casteran/CoqArt/) up to `Chapter 8: Inductive Predicates` for a proper understanding.

Optionally the following will also be helpful, but this is not required:

  - Experience with Lean4, since this project is written in Lean4. We recommend reading:
    + [Lean4 Learning Resources](https://lean-lang.org/learn/) to close the gap between Coq and Lean.
    + [Lean Manual](https://leanprover.github.io/lean4/doc/whatIsLean.html) for programming in Lean and Monads.
    + [Coq Lean Tactic Cheat Sheet](https://github.com/funexists/coq-lean-cheatsheet/)
    + [Lean Standard Libary Documentation](https://leanprover-community.github.io/mathlib4_docs/Std/Data/HashMap/Basic.html#Std.HashMap)
    + [Lean4 Meta Programming Book](https://github.com/arthurpaulino/lean4-metaprogramming-book)
    + [Lean Tactics File](https://github.com/leanprover/lean4/blob/master/src/Init/Tactics.lean)
    + [Tactic List](https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md)

Questions about Lean4 can be asked on [proofassistants.stackexchange](https://proofassistants.stackexchange.com/) by tagging questions with `lean` and `lean4` or in the [Zulip Chat](https://leanprover.zulipchat.com/).

### Setup

  - Lean4 has exceptional [instructions for installing Lean4 in VS Code](https://lean-lang.org/install/).
  - Remember to also add `lake` (the build system for lean) to your `PATH`.  You can do this on mac by adding `export PATH=~/.elan/bin/:${PATH}` to your  `~/.zshrc` file
  - Use mathlib's cache to speed up building time by running: `$ lake exe cache get`
