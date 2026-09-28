import Mathlib

/-!
# Erdős #971 review — Lemma 1 (finite occupancy inequality), sum form.

Uniform probability on a finite set `s` of residue classes.  If integer-valued `0 ≤ N ≤ W`,
`E[(N-1)W] ≥ α > 0` and `E[W^3] ≤ B`, then `P(N = 0) ≥ α²/B - E[N] + 1`.
Everything is multiplied through by `m = #s`.
-/

open Finset

theorem occupancy971 {ι : Type*} (s : Finset ι) (N W : ι → ℕ)
    (hNW : ∀ i ∈ s, N i ≤ W i) (α B : ℝ) (hα : 0 < α) (hB : 0 < B)
    (h1 : α * s.card ≤ ∑ i ∈ s, ((N i : ℝ) - 1) * W i)
    (h3 : ∑ i ∈ s, (W i : ℝ) ^ 3 ≤ B * s.card) :
    (α ^ 2 / B - (∑ i ∈ s, (N i : ℝ)) / s.card + 1) * s.card
      ≤ ((s.filter (fun i => N i = 0)).card : ℝ) := by
  classical
  set m : ℝ := (s.card : ℝ) with hm
  -- R = (N - 1)_+ written as N - 1 + [N = 0]
  set R : ι → ℝ := fun i => (N i : ℝ) - 1 + (if N i = 0 then 1 else 0) with hRdef
  have hR0 : ∀ i ∈ s, 0 ≤ R i := by
    intro i _
    simp only [hRdef]
    by_cases h : N i = 0
    · simp [h]
    · have : (1 : ℝ) ≤ N i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
      simp [h]; omega
  have hRW : ∀ i ∈ s, R i ≤ W i := by
    intro i hi
    have hw : (N i : ℝ) ≤ W i := by exact_mod_cast hNW i hi
    simp only [hRdef]
    by_cases h : N i = 0
    · simp [h]
    · simp [h]; linarith
  have hmix : ∀ i ∈ s, ((N i : ℝ) - 1) * W i ≤ R i * W i := by
    intro i _
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simp only [hRdef]
    split_ifs <;> linarith
  -- Cauchy–Schwarz: (Σ R W)^2 ≤ (Σ R)(Σ R W^2)
  have hCS : (∑ i ∈ s, R i * W i) ^ 2 ≤ (∑ i ∈ s, R i) * ∑ i ∈ s, R i * (W i : ℝ) ^ 2 :=
    sum_sq_le_sum_mul_sum_of_sq_eq_mul s hR0
      (fun i hi => mul_nonneg (hR0 i hi) (sq_nonneg _)) (fun i _ => by ring)
  have hRW2 : ∑ i ∈ s, R i * (W i : ℝ) ^ 2 ≤ ∑ i ∈ s, (W i : ℝ) ^ 3 := by
    apply sum_le_sum
    intro i hi
    have := mul_le_mul_of_nonneg_right (hRW i hi) (sq_nonneg (W i : ℝ))
    nlinarith
  have hlow : α * m ≤ ∑ i ∈ s, R i * W i := le_trans h1 (sum_le_sum hmix)
  have hm0 : 0 ≤ m := by positivity
  have hsq : (α * m) ^ 2 ≤ (∑ i ∈ s, R i) * (B * m) := by
    have hSR : 0 ≤ ∑ i ∈ s, R i := sum_nonneg hR0
    calc (α * m) ^ 2 ≤ (∑ i ∈ s, R i * W i) ^ 2 := by
            exact pow_le_pow_left₀ (by positivity) hlow 2
      _ ≤ (∑ i ∈ s, R i) * ∑ i ∈ s, R i * (W i : ℝ) ^ 2 := hCS
      _ ≤ (∑ i ∈ s, R i) * (B * m) := by
            apply mul_le_mul_of_nonneg_left (le_trans hRW2 h3) hSR
  -- Σ R = Σ N - m + #{N = 0}
  have hsumR : ∑ i ∈ s, R i = (∑ i ∈ s, (N i : ℝ)) - m + ((s.filter (fun i => N i = 0)).card : ℝ) := by
    simp only [hRdef, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, hm]
    rw [Finset.sum_boole]
  rcases eq_or_lt_of_le hm0 with h0 | hpos
  · rw [← h0]; simp
  · have key : α ^ 2 * m / B ≤ ∑ i ∈ s, R i := by
      rw [div_le_iff₀ hB]
      nlinarith [hsq]
    have : (α ^ 2 / B - (∑ i ∈ s, (N i : ℝ)) / m + 1) * m
        = α ^ 2 * m / B - (∑ i ∈ s, (N i : ℝ)) + m := by
      field_simp
    rw [this]
    linarith [key, hsumR]


