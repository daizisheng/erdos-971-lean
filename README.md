# erdos-971-lean

Conditional Lean 4 formalization of an affirmative answer to
[Erdős Problem #971](https://www.erdosproblems.com/971):

> there are absolute constants c, C > 0 such that for every sufficiently large q,
> at least C·φ(q) reduced residue classes a mod q have least prime p(a,q) > (1+c)·φ(q)·log q.

**Status: work in progress, unreviewed.**

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
| `Erdos971/Occupancy.lean` | Lemma 1: finite occupancy inequality (no axioms) |
