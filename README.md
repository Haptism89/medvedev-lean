# Lean formalization of *Medvedev Logic is Π⁰₁-Complete*

This repository contains a Lean 4 formalization of the paper

> Pawel Pawlowski, *Medvedev Logic is Not Decidable. It is Π⁰₁-complete. Who Would Have Guessed?*,
> arXiv:2609.11576 (2026). https://arxiv.org/abs/2609.11576

## Provenance

This is the author's first Lean project. The formalization was developed in cooperation with
an AI assistant (Anthropic's Claude). The assistant wrote most of the Lean code and proofs.
The proofs themselves are checked by Lean's kernel and not by a human. The formalization was
reviewed several times by Claude and also by Astra. The project builds and checks without
errors. Additionally the author checked the definitions and the formulations of the theorems
against the paper and to his knowledge did not find anything suspicious. Corrections and
issues are welcome.

The author would be glad to collaborate on similar problems and to improve his own knowledge
of Lean. He has further partial results that still need to be verified. Do not hesitate to
contact him at haptism89@gmail.com.

## What is proved

All statements below are theorems in this repository, checked by Lean 4.28.0 against
Mathlib, and depend only on Lean's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`). There is no `sorry` and no project-declared axiom.

The internal reduction of the paper (Sections 1–4). For a finite Wang system `D` given by a
positive number of tile types and two Boolean compatibility tables (`WangCode`):

```lean
Medvedev.WangCode.correct (c : WangCode) :
  TilesTorus c.system ↔ ¬ Formula.InML c.formula
```

`TilesTorus` is the existence of a finite torus tiling (Definition 1.2 of the paper),
`Formula.InML` is validity on every finite Medvedev frame under every persistent valuation
(Section 4), and `c.formula` is the recognizing formula α(P_D, 𝒟_D) with its variables coded
as natural numbers. The two halves of this equivalence are

```lean
Medvedev.tilesTorus_iff_finiteRealizable (D : Wang T) : TilesTorus D ↔ FiniteRealizable D
Medvedev.finite_recognition (D : Wang T) : FiniteRealizable D ↔ ¬ InML (alpha D)
```

(Sections 2–3, and Section 4 respectively), where `Realization` is Definition 1.4 with its
conditions (H0)–(H2) as fields.

The finite search of Proposition 5.1, as an executable checker:

```lean
Medvedev.Formula.pi01_characterization (f : Formula ℕ) : InML f ↔ ∀ n, checkFrame f n = true
```

The periodic domino theorem (Theorem 5.2 of the paper, cited there from Jeandel) is used in
the form of an explicit hypothesis in `Medvedev.nonhalting_reduction`, exactly as the paper
uses it. In addition, and beyond the paper, a version of it is *proved* here for Mathlib's
standard Turing machine model `Turing.TM0` with a finite input word, by an independent
construction (the `Medvedev/Domino/` directory):

```lean
Medvedev.Domino.TM0Problem.domino_correct (p : TM0Problem) :
  TilesTorus p.compile.domino.system ↔ p.Halts

Medvedev.Domino.TM0Problem.nonhalting_iff_valid (p : TM0Problem) :
  ¬ p.Halts ↔ Formula.InML p.formula
```

Here `p.Halts` is `(Turing.TM0.eval p.program.machine p.input).Dom`, Mathlib's own
semantics.

Section 5 (Theorem 5.3 and Corollaries 5.4–5.5) is stated in `Medvedev/Complexity.lean` as
implications whose hypotheses are the computability facts the paper takes from recursion
theory:

```lean
Medvedev.not_computablePred_inML [Primcodable (Formula ℕ)] [Primcodable Domino.TM0Problem]
  (hformula : Computable fun p : Domino.TM0Problem => p.formula)
  (hhalt : ¬ ComputablePred Domino.TM0Problem.Halts) :
  ¬ ComputablePred (Formula.InML : Formula ℕ → Prop)
```

together with `rePred_not_inML` (the complement of ML is r.e.), `not_rePred_inML` (ML is
not r.e.) and `no_computable_bound` (no computable bound on countermodel size).

## What is not proved

The following remain hypotheses or are outside the development:

- Numerical codings (`Primcodable`) of formulas and of machine problems; no instance is
  provided.
- Mathlib computability certificates for the compiled formula (`p.formula`) and for the
  finite checker (`checkFrame`). Both are executable total Lean functions; the formal
  `Computable` statements are not proved.
- Undecidability of halting for `TM0Problem`. Mathlib proves the halting problem for
  `Nat.Partrec.Code`; no reduction to `TM0` is claimed.
- The phrase "Π⁰₁-complete" as a single statement; its two halves (membership in Π⁰₁, and the
  reduction from nonhalting) are proved separately as above.
- Corollary 5.6 on inquisitive logic is not formalized.

## Building

Install [Elan](https://github.com/leanprover/elan). Then, in this directory:

```bash
lake exe cache get   # download Mathlib's precompiled files (once)
lake build           # builds and checks everything; several minutes
```

To replay every project declaration through the kernel and audit axiom dependencies:

```bash
python3 scripts/run_audit.py
```

It prints `AXIOM AUDIT PASSED: … axioms = [propext, Quot.sound, Classical.choice]` and
`KERNEL REPLAY PASSED`. The toolchain is pinned in `lean-toolchain`; Mathlib and all
dependencies are pinned in `lake-manifest.json`.

## File map

| Paper | Lean |
|---|---|
| §1 Wang systems, the Wang–Medvedev pair, admissibility | `Medvedev/Basic.lean`, `Counts.lean`, `DemandCode.lean` |
| §1 torus tilings | `Torus.lean` |
| §1 finite realizations, Lemma 1.5 | `Realization.lean` |
| Lemma 1.6, Proposition 1.7 (response test and table) | `ResponseTest.lean`, `ResponseTable.lean` |
| §2 realization ⟹ torus tiling | `Extraction.lean`, `Adjacency.lean`, `Columns.lean` |
| §3 torus tiling ⟹ realization (compressed construction) | `Compressed*.lean`, `Representatives.lean`, `Lifting.lean`, `Populated.lean`, `Separation.lean` |
| §2 + §3 combined | `Construction.lean` |
| §4 semantics, the formula, recognition | `Semantics.lean`, `Clauses.lean`, `Trace.lean`, `Recognition*.lean`, `Renaming.lean` |
| §5 finite search, the reduction, complexity | `FiniteSemantics.lean`, `UpperBound.lean`, `Reduction.lean`, `Complexity.lean` |
| Theorem 5.2 (periodic domino), proved for Mathlib TM0 | `Domino/` (endpoint: `Domino/StandardTM.lean`) |
| Kernel replay and axiom audit | `Audit.lean`, `scripts/run_audit.py` |
| Sanity checks and adversarial checks (not needed by the theorems) | `Examples.lean`, `ReviewChecks.lean`, `QuantifierChecks.lean`, `*Audit.lean`, `Domino/AdversarialChecks.lean` |

## License

Apache License 2.0. See `LICENSE`.
