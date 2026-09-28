import Mathlib

/-!
# Erdős #971 — basic definitions

(Historically this file held the project's axioms. There are none left: the fundamental lemma of sieve
theory is proved in `FL/`, and PNT, Mertens and Bombieri–Vinogradov come from dependencies via
`Bridge.lean`.)
-/

open Real Finset Filter Topology

namespace Erdos971

/-- The primes `p < z`, as a finset of naturals. -/
noncomputable def primesLT (z : ℝ) : Finset ℕ :=
  (Finset.range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) < z)

/-- `P(z) = ∏_{p < z} p`. -/
noncomputable def Pz (z : ℝ) : ℕ := ∏ p ∈ primesLT z, p

/-- `V(z) = ∏_{p < z} (1 - 1/p)`. -/
noncomputable def V (z : ℝ) : ℝ := ∏ p ∈ primesLT z, (1 - 1 / (p : ℝ))

/-- `π(y; r, b)`: the number of primes `p ≤ y` with `p ≡ b (mod r)`. -/
noncomputable def piAP (y : ℝ) (r b : ℕ) : ℕ :=
  ((Finset.range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ b [MOD r])).card

/-- The logarithmic integral `Li(y) = ∫_2^y dt / log t`. -/
noncomputable def Li (y : ℝ) : ℝ := ∫ t in (2 : ℝ)..y, 1 / Real.log t


end Erdos971
