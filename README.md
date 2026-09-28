# erdos-971-lean

Lean 4 formalization of an affirmative answer to
[Erdős Problem #971](https://www.erdosproblems.com/971), conditional on **one** standard theorem:

> there are absolute constants c, C > 0 such that for every sufficiently large q,
> at least C·φ(q) reduced residue classes a mod q have least prime p(a,q) > (1+c)·φ(q)·log q.

**Status: complete modulo the fundamental lemma of sieve theory; unreviewed.**

```
#print axioms Erdos971.erdos_971
-- [propext, Classical.choice, Quot.sound, Erdos971.fundamental_lemma]
```

The statement `Erdos971Statement` is copied verbatim from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/971.lean).

## What is proved, and what is assumed

| input | status |
|---|---|
| prime number theorem, `Li y ∼ y / log y` | **proved** — from [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) (`pi_alt'`, `integral_div_log_asymptotic`) |
| Mertens' product theorem | **proved** — from PrimeNumberTheoremAnd (`Mertens.prod_one_minus_div_prime_eq`, `Mertens.E₃.abs_le`) |
| Bombieri–Vinogradov | **proved** — from [kimihiro64/bombieri-vinogradov](https://github.com/kimihiro64/bombieri-vinogradov) (`weighted_to_prime_counting`) |
| fundamental lemma of sieve theory | **axiom** `fundamental_lemma` in `Erdos971/Axioms.lean` (Iwaniec–Kowalski Cor. 6.10; stated in a weaker form) |

Everything else — the occupancy inequality, the singular-series averages, the sieve applications,
the moment bounds and the assembly — is machine-checked. The derivations of the three imported theorems
into the exact forms used here are in `Erdos971/Bridge.lean`.

**The remaining risk is the axiom statement:** if `fundamental_lemma` were stated more strongly than the
literature supports, the conclusion would be worthless. It is intended to be implied by the cited textbook
statement; this still needs a word-for-word check against the source.

## Build

Lean v4.33.1, mathlib v4.33.1 (`0df444a`), via `kimihiro64/bombieri-vinogradov @ 7a17483`.

```sh
lake update
scripts/patch_pnt.sh        # see vendor/PrimeNumberTheoremAnd-f8f58c7/README.md
lake exe cache get
lake build                  # the dependency build needs a lot of memory (~80 GB at 10 jobs)
lake env lean Erdos971/Check.lean
```

`scripts/patch_pnt.sh` works around an inconsistent pin in the dependency chain: the bombieri-vinogradov
repository pins the PrimeNumberTheoremAnd fork at `0f15a38`, but its dependency Robin1984 needs ten files
that exist only at `f8f58c7` of the same fork. Those files are vendored unmodified, with provenance and the
Apache-2.0 license, in `vendor/PrimeNumberTheoremAnd-f8f58c7/`.

## Priority and relation to other work

The same statement was first claimed by KyungMin Han on the erdosproblems.com forum (2026-07-25,
proof claim #135), via the pointwise variance lower bound of Friedlander–Goldston (Q. J. Math. 1996,
Theorem 2). The argument formalized here has the same second-moment / third-moment / occupancy structure;
its second-moment step is a variant of Friedlander–Goldston's own method (§8 of their paper), using rough
numbers in place of Λ_R.

## Layout

| file | content |
|---|---|
| `Erdos971/Statement.lean` | the statement, verbatim from formal-conjectures |
| `Erdos971/Axioms.lean` | basic definitions and the single axiom `fundamental_lemma` |
| `Erdos971/Bridge.lean` | PNT, `Li` asymptotics, Mertens, Bombieri–Vinogradov in the forms used here (proved from dependencies) |
| `Erdos971/Defs.lean` | objects of the proof |
| `Erdos971/Occupancy.lean` | Lemma 1: finite occupancy inequality (no axioms) |
| `Erdos971/Scale.lean` | scale facts (PNT/Mertens consequences) |
| `Erdos971/Singular.lean` | finite singular-series estimates: Lemmas 2 and 3, `sum_S2_le` (no axioms) |
| `Erdos971/Sieve.lean` | fundamental-lemma and Bombieri–Vinogradov applications |
| `Erdos971/MomentsComb.lean` | counting identities for the moments (no axioms) |
| `Erdos971/Moments.lean` | third moment, mixed moment |
| `Erdos971/Main.lean` | assembly: `erdos_971 : Erdos971Statement` |

See `BLUEPRINT.md` for the proof plan. No `sorry` anywhere.
