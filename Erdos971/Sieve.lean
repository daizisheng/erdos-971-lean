import Erdos971.Defs

/-!
# Sieve applications (BLUEPRINT §4). Uses `fundamental_lemma`, `mertens_product`, `bombieri_vinogradov`.
-/

open Real Finset Filter Topology

namespace Erdos971

/-- `M_+(hq) = #{p prime : z < p, p + hq ≤ x, (p + hq, P(z)) = 1}`. -/
noncomputable def Mplus (q u h : ℕ) : ℕ :=
  ((Icc 1 ⌊xq q⌋₊).filter (fun p : ℕ => p.Prime ∧ zq q u < (p : ℝ) ∧ p + h * q ≤ ⌊xq q⌋₊ ∧
    Nat.Coprime (p + h * q) (Pz (zq q u)))).card

/-- `M_-(hq) = #{p prime : hq < p ≤ x, (p - hq, P(z)) = 1}`. -/
noncomputable def Mminus (q u h : ℕ) : ℕ :=
  ((Icc 1 ⌊xq q⌋₊).filter (fun p : ℕ => p.Prime ∧ h * q < p ∧
    Nat.Coprime (p - h * q) (Pz (zq q u)))).card

/-- `#{1 ≤ n ≤ x : n(n+h)(n+k) is z-rough}` (here `h, k` already include the factor `q`). -/
noncomputable def Qtrip (q u h k : ℕ) : ℕ :=
  ((Icc 1 ⌊xq q⌋₊).filter (fun n => Nat.Coprime (n * (n + h) * (n + k)) (Pz (zq q u)))).card

/-- **SV1 + SV3**: the dimension-one sieve package, with one error function `η`. -/
theorem sieve_dim1 : ∃ η : ℝ → ℝ, Tendsto (fun s => s * η s) atTop (𝓝 0) ∧
    ∃ u₀ : ℕ, ∀ u : ℕ, u₀ ≤ u →
      (∀ᶠ q : ℕ in atTop,
        (∑ a ∈ reduced q, (Wc q u a : ℝ))
          ≤ (1 + η (u / 4)) * xq q * V (zq q u) + xq q ^ ((1 : ℝ) / 4)) ∧
      (∀ᶠ q : ℕ in atTop,
        (1 - η (u / 4)) * V (zq q u) * ∑ h ∈ Ico 1 (Kq q), S2 (zq q u) (h * q) *
            ((Li (xq q - h * q) - Li (zq q u)) + (Li (xq q) - Li (h * q)))
          - xq q / (Real.log (xq q)) ^ 2
          ≤ ∑ h ∈ Ico 1 (Kq q), ((Mplus q u h : ℝ) + Mminus q u h)) := by
  sorry

/-- **SV2**: triples, for every large fixed `u`. -/
theorem sieve_triple : ∃ u₀ : ℕ, ∀ u : ℕ, u₀ ≤ u → ∀ᶠ q : ℕ in atTop,
    ∀ h k : ℕ, 1 ≤ h → h < k → k ≤ Kq q →
      (Qtrip q u (h * q) (k * q) : ℝ)
        ≤ 2 * xq q * V (zq q u) ^ 3 * S3 (zq q u) (h * q) (k * q) + xq q ^ ((1 : ℝ) / 3) := by
  sorry

end Erdos971
