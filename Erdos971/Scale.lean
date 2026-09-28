import Erdos971.Defs

/-!
# Scale facts (BLUEPRINT §2). Uses `pnt`, `mertens_product`.
-/

open Real Finset Filter Topology

namespace Erdos971

/-- **S2** `K → ∞`. -/
theorem Kq_tendsto : Tendsto (fun q : ℕ => (Kq q : ℝ)) atTop atTop := by
  sorry

/-- **S2** eventually `q ≤ x`. -/
theorem q_le_xq : ∀ᶠ q : ℕ in atTop, (q : ℝ) ≤ xq q := by
  sorry

/-- **S2** `log q / log x → 1`. -/
theorem log_ratio : Tendsto (fun q : ℕ => Real.log q / Real.log (xq q)) atTop (𝓝 1) := by
  sorry

/-- `Qz q z(q) · φ(q)/q → 1` for fixed `u` (at most `u` prime factors of `q` are `≥ z`). -/
theorem Qz_ratio (u : ℕ) (hu : 1 ≤ u) :
    Tendsto (fun q : ℕ => Qz q (zq q u) * q.totient / q) atTop (𝓝 1) := by
  sorry

/-- **S3** `π(z)/φ(q) → 0`. -/
theorem pi_z_small (u : ℕ) (hu : 2 ≤ u) :
    Tendsto (fun q : ℕ => (Nat.primeCounting ⌊zq q u⌋₊ : ℝ) / q.totient) atTop (𝓝 0) := by
  sorry

/-- **S4** `E N → 1`. -/
theorem avgN_tendsto (u : ℕ) (hu : 2 ≤ u) :
    Tendsto (fun q : ℕ => avg q (fun a => (Nc q u a : ℝ))) atTop (𝓝 1) := by
  sorry

/-- **S5** `A_q ≤ C_M u`. -/
theorem Aq_le : ∃ CM : ℝ, 0 < CM ∧ ∀ u : ℕ, 1 ≤ u → ∀ᶠ q : ℕ in atTop, Aq q u ≤ CM * u := by
  sorry

/-- **S6** -/
theorem Li_sub_ge {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) : (b - a) / Real.log b ≤ Li b - Li a := by
  sorry

/-- **S7** `(π((1+c)x) - π(x))/φ(q) → c`. -/
theorem pi_window (c : ℝ) (hc : 0 < c) :
    Tendsto (fun q : ℕ => ((Nat.primeCounting ⌊(1 + c) * xq q⌋₊ : ℝ)
      - Nat.primeCounting ⌊xq q⌋₊) / q.totient) atTop (𝓝 c) := by
  sorry

/-- `N_a ≤ W_a` (primes `> z` are `z`-rough). -/
theorem Nc_le_Wc (q u a : ℕ) : Nc q u a ≤ Wc q u a := by
  sorry

end Erdos971
