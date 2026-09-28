# erdos-971-lean

Conditional Lean 4 formalization of an affirmative answer to
[Erdős Problem #971](https://www.erdosproblems.com/971):

> there are absolute constants c, C > 0 such that for every sufficiently large q,
> at least C·φ(q) reduced residue classes a mod q have least prime p(a,q) > (1+c)·φ(q)·log q.

**Status: complete modulo the four axioms below; unreviewed.**

```
#print axioms Erdos971.erdos_971
-- [propext, Classical.choice, Quot.sound,
--  Erdos971.pnt, Erdos971.mertens_product, Erdos971.bombieri_vinogradov, Erdos971.fundamental_lemma]
```
Build: `lake build` (Lean v4.29.0-rc6, mathlib `921b8d3`); check: `lake env lean Erdos971/Check.lean`.

## What is proved, and what is assumed

Everything is machine-checked except a small number of standard analytic-number-theory theorems,
which are stated as explicit `axiom`s in `Erdos971/Axioms.lean` with precise literature references
(prime number theorem, Mertens' product bound, a weak Bombieri–Vinogradov theorem for moduli ≤ x^{1/4},
and the fundamental lemma of sieve theory). `#print axioms` for the main theorem lists exactly these.

## Priority and relation to other work

The same statement was first claimed by KyungMin Han on the erdosproblems.com forum (2026-07-25,
proof claim #135), via the pointwise variance lower bound of Friedlander–Goldston (Q. J. Math. 1996,
Theorem 2). The argument formalized here (found by an AI model, reviewed step-by-step) has the same
second-moment / third-moment / occupancy structure; its second-moment step is a variant of
Friedlander–Goldston's own method (§8 of their paper), using rough numbers in place of Λ_R.

## Layout

| file | content |
|---|---|
| `Erdos971/Statement.lean` | the statement, verbatim from google-deepmind/formal-conjectures |
| `Erdos971/Axioms.lean` | the four analytic axioms (the only unproved inputs) |
| `Erdos971/Defs.lean` | objects of the proof |
| `Erdos971/Occupancy.lean` | Lemma 1: finite occupancy inequality (done, no axioms) |
| `Erdos971/Scale.lean` | scale facts: PNT/Mertens consequences (done) |
| `Erdos971/Singular.lean` | finite singular-series estimates, Lemmas 2 and 3 (done, no axioms) |
| `Erdos971/Sieve.lean` | fundamental-lemma and Bombieri–Vinogradov applications (done) |
| `Erdos971/MomentsComb.lean` | counting identities for the moments (done, no axioms) |
| `Erdos971/Moments.lean` | third moment, mixed moment (done) |
| `Erdos971/Main.lean` | assembly: `erdos_971 : Erdos971Statement` (done, modulo the modules above) |

See `BLUEPRINT.md` for the proof plan. No `sorry` anywhere.

**The main risk is in the axioms, not the proof:** if an axiom were stated more strongly than the literature
supports (or inconsistently), the conclusion would be worthless. Each axiom is intended to be implied by the cited
textbook statement; this still needs to be checked word-for-word against the sources.
