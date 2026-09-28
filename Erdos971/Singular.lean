import Erdos971.Defs

/-!
# Finite singular-series estimates (BLUEPRINT §3). No axioms.
-/

open Real Finset Filter Topology

namespace Erdos971

theorem S2_nonneg (z : ℝ) (t : ℕ) : 0 ≤ S2 z t := by
  sorry

theorem S3_nonneg (z : ℝ) (h k : ℕ) : 0 ≤ S3 z h k := by
  sorry

/-- **SS1** (Lemma 2, finite form, lower bound), uniform in `q`, `z`, `K`. -/
theorem lemma2_finite : ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
    ∀ (q : ℕ) (z : ℝ) (K : ℕ), 1 ≤ q →
      (1 - δ K) * Qz q z * (K : ℝ) ^ 2 / 2 ≤ ∑ h ∈ Ico 1 K, ((K : ℝ) - h) * S2 z (h * q) := by
  sorry

/-- **SS2** (Lemma 3), uniform in `q`, `z`, `K`. -/
theorem lemma3 : ∃ C₃ : ℝ, ∀ (q : ℕ) (z : ℝ) (K : ℕ), 1 ≤ q →
    ∑ k ∈ Icc 1 K, ∑ h ∈ Ico 1 k, S3 z (h * q) (k * q) ≤ C₃ * (Qz q z) ^ 2 * (K : ℝ) ^ 2 := by
  sorry

end Erdos971
