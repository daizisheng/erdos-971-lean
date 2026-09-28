import Erdos971.Scale
import Erdos971.Singular
import Erdos971.Sieve

/-!
# Moments (BLUEPRINT §5).
-/

open Real Finset Filter Topology

namespace Erdos971

/-- **M1** bounded third moment, for every large fixed `u`. -/
theorem third_moment : ∃ u₀ : ℕ, ∀ u : ℕ, u₀ ≤ u → ∃ B : ℝ, 0 < B ∧
    ∀ᶠ q : ℕ in atTop, avg q (fun a => (Wc q u a : ℝ) ^ 3) ≤ B := by
  sorry

/-- **M3** the decisive mixed moment: for all sufficiently large fixed `u`. -/
theorem mixed_moment : ∃ u₀ : ℕ, ∀ u : ℕ, u₀ ≤ u →
    ∀ᶠ q : ℕ in atTop, (1 : ℝ) / 2 ≤ avg q (fun a => ((Nc q u a : ℝ) - 1) * Wc q u a) := by
  sorry

end Erdos971
