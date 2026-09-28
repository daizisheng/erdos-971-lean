import Mathlib

/-!
# Fundamental lemma, part A: weighted Bonferroni, Rankin bound, product perturbation

Route: logarithmically blocked Bonferroni sieve (see `attack/971/lean_fl/q1_astra.md`).
-/

open Finset

namespace Erdos971.FL

/-- `E_m(B) = Σ_{D ⊆ B, |D| = m} ∏_{p ∈ D} g p`. -/
noncomputable def Esym (g : ℕ → ℝ) (B : Finset ℕ) (m : ℕ) : ℝ :=
  ∑ D ∈ B.powersetCard m, ∏ p ∈ D, g p

/-- `V_B = ∏_{p ∈ B} (1 - g p)`. -/
noncomputable def Vp (g : ℕ → ℝ) (B : Finset ℕ) : ℝ := ∏ p ∈ B, (1 - g p)

/-- Bonferroni truncation `U_{B,k} = Σ_{ℓ ≤ k} (-1)^ℓ E_ℓ(B)`. -/
noncomputable def Utr (g : ℕ → ℝ) (B : Finset ℕ) (k : ℕ) : ℝ :=
  ∑ l ∈ range (k + 1), (-1 : ℝ) ^ l * Esym g B l

lemma esym_zero (g : ℕ → ℝ) (B : Finset ℕ) : Esym g B 0 = 1 := by
  simp [Esym]

lemma esym_empty_succ (g : ℕ → ℝ) (m : ℕ) : Esym g ∅ (m + 1) = 0 := by
  rw [Esym, powersetCard_eq_empty.2 (by simp)]; simp

lemma esym_insert (g : ℕ → ℝ) {a : ℕ} {B : Finset ℕ} (ha : a ∉ B) (m : ℕ) :
    Esym g (insert a B) (m + 1) = Esym g B (m + 1) + g a * Esym g B m := by
  unfold Esym
  rw [← Nat.succ_eq_add_one, powersetCard_succ_insert ha, sum_union, sum_image]
  · congr 1
    rw [mul_sum]
    refine sum_congr rfl fun D hD => ?_
    have : a ∉ D := fun h => ha ((mem_powersetCard.1 hD).1 h)
    rw [prod_insert this]
  · intro D1 h1 D2 h2 h
    have n1 : a ∉ D1 := fun h' => ha ((mem_powersetCard.1 h1).1 h')
    have n2 : a ∉ D2 := fun h' => ha ((mem_powersetCard.1 h2).1 h')
    have := congrArg (fun s => Finset.erase s a) h
    simpa [erase_insert n1, erase_insert n2] using this
  · rw [disjoint_left]
    intro D h1 h2
    obtain ⟨D', hD', rfl⟩ := mem_image.1 h2
    exact ha ((mem_powersetCard.1 h1).1 (mem_insert_self a D'))

lemma utr_zero (g : ℕ → ℝ) (B : Finset ℕ) : Utr g B 0 = 1 := by
  simp [Utr, esym_zero]

lemma utr_insert (g : ℕ → ℝ) {a : ℕ} {B : Finset ℕ} (ha : a ∉ B) (k : ℕ) :
    Utr g (insert a B) (k + 1) = Utr g B (k + 1) - g a * Utr g B k := by
  unfold Utr
  rw [sum_range_succ' _ (k + 1), sum_range_succ' _ (k + 1)]
  simp only [esym_insert g ha, esym_zero, pow_succ, mul_sum]
  rw [← sub_eq_zero]
  have : ∀ i ∈ range (k + 1), (-1 : ℝ) ^ i * -1 * (Esym g B (i + 1) + g a * Esym g B i)
      = (-1 : ℝ) ^ i * -1 * Esym g B (i + 1) - g a * ((-1) ^ i * Esym g B i) := by
    intro i _; ring
  rw [sum_congr rfl this, sum_sub_distrib]
  ring

lemma utr_empty (g : ℕ → ℝ) (k : ℕ) : Utr g ∅ k = 1 := by
  unfold Utr
  rw [sum_range_succ']
  simp [esym_zero, esym_empty_succ]

lemma vp_bounds (g : ℕ → ℝ) (B : Finset ℕ) (hg : ∀ p ∈ B, 0 ≤ g p ∧ g p ≤ 1) :
    0 ≤ Vp g B ∧ Vp g B ≤ 1 := by
  refine ⟨prod_nonneg fun p hp => by linarith [(hg p hp).2],
    prod_le_one (fun p hp => by linarith [(hg p hp).2]) fun p hp => by linarith [(hg p hp).1]⟩

lemma bonf_all (g : ℕ → ℝ) (B : Finset ℕ) (hg : ∀ p ∈ B, 0 ≤ g p ∧ g p ≤ 1) :
    ∀ k, 0 ≤ (-1 : ℝ) ^ k * (Utr g B k - Vp g B) ∧
      (-1 : ℝ) ^ k * (Utr g B k - Vp g B) ≤ Esym g B (k + 1) := by
  induction B using Finset.induction_on with
  | empty => intro k; simp [utr_empty, Vp, esym_empty_succ]
  | insert a B ha ih =>
    have hgB : ∀ p ∈ B, 0 ≤ g p ∧ g p ≤ 1 := fun p hp => hg p (mem_insert_of_mem hp)
    have ga := hg a (mem_insert_self a B)
    have IH := ih hgB
    have hV : Vp g (insert a B) = (1 - g a) * Vp g B := by simp [Vp, prod_insert ha]
    intro k
    cases k with
    | zero =>
      have := IH 0
      have hv := vp_bounds g B hgB
      simp only [pow_zero, one_mul, utr_zero, zero_add] at this ⊢
      rw [hV, esym_insert g ha, esym_zero]
      constructor <;> nlinarith
    | succ k =>
      have h1 := IH k
      have h2 := IH (k + 1)
      rw [hV, utr_insert g ha, esym_insert g ha]
      have e : (-1 : ℝ) ^ (k + 1) * (Utr g B (k + 1) - g a * Utr g B k - (1 - g a) * Vp g B)
          = (-1 : ℝ) ^ (k + 1) * (Utr g B (k + 1) - Vp g B)
            + g a * ((-1 : ℝ) ^ k * (Utr g B k - Vp g B)) := by ring
      rw [e]
      constructor <;> nlinarith

/-- **A1. Weighted Bonferroni.** For `0 ≤ g ≤ 1` on `B` and even `k`:
`V_B ≤ U_{B,k} ≤ V_B + E_{k+1}(B)`. (Covers indicator weights `g ∈ {0,1}`.) -/
theorem bonferroni_weighted (g : ℕ → ℝ) (B : Finset ℕ) (hg : ∀ p ∈ B, 0 ≤ g p ∧ g p ≤ 1)
    (k : ℕ) (hk : Even k) :
    Vp g B ≤ Utr g B k ∧ Utr g B k ≤ Vp g B + Esym g B (k + 1) := by
  have := bonf_all g B hg k
  rw [hk.neg_one_pow, one_mul] at this
  constructor <;> linarith [this.1, this.2]

lemma esym_nonneg (g : ℕ → ℝ) (B : Finset ℕ) (hg : ∀ p ∈ B, 0 ≤ g p) (m : ℕ) :
    0 ≤ Esym g B m :=
  sum_nonneg fun _ hD => prod_nonneg fun p hp => hg p ((mem_powersetCard.1 hD).1 hp)

lemma esym_two_pow (g : ℕ → ℝ) (B : Finset ℕ) (hg : ∀ p ∈ B, 0 ≤ g p) :
    ∀ m, 2 ^ m * Esym g B m ≤ ∏ p ∈ B, (1 + 2 * g p) := by
  induction B using Finset.induction_on with
  | empty =>
    intro m; cases m with
    | zero => simp [esym_zero]
    | succ m => simp [esym_empty_succ]
  | insert a B ha ih =>
    have hgB : ∀ p ∈ B, 0 ≤ g p := fun p hp => hg p (mem_insert_of_mem hp)
    have ga := hg a (mem_insert_self a B)
    have IH := ih hgB
    have hP : 1 ≤ ∏ p ∈ B, (1 + 2 * g p) :=
      one_le_prod fun p hp => by linarith [hgB p hp]
    intro m
    rw [prod_insert ha]
    cases m with
    | zero => rw [esym_zero]; nlinarith
    | succ m =>
      rw [esym_insert g ha]
      have h1 := IH m
      have h2 := IH (m + 1)
      rw [pow_succ] at h2 ⊢
      nlinarith

/-- **A2. Rankin bound.** For `0 ≤ g < 1` on `B`: `E_m(B) ≤ 2^{-m} V_B^{-2}` (and `V_B > 0`). -/
theorem esym_rankin (g : ℕ → ℝ) (B : Finset ℕ) (hg : ∀ p ∈ B, 0 ≤ g p ∧ g p < 1) (m : ℕ) :
    0 < Vp g B ∧ Esym g B m ≤ (1 / 2 : ℝ) ^ m * ((Vp g B)⁻¹) ^ 2 := by
  have hV : 0 < Vp g B := prod_pos fun p hp => by linarith [(hg p hp).2]
  refine ⟨hV, ?_⟩
  have h1 := esym_two_pow g B (fun p hp => (hg p hp).1) m
  have h2 : (∏ p ∈ B, (1 + 2 * g p)) * Vp g B ^ 2 ≤ 1 := by
    rw [Vp, ← prod_pow, ← prod_mul_distrib]
    refine prod_le_one (fun p hp => ?_) fun p hp => ?_
    · have := hg p hp; nlinarith
    · have := hg p hp; nlinarith [mul_nonneg this.1 this.1, mul_nonneg (mul_nonneg this.1 this.1) (sub_nonneg.2 this.2.le)]
  have hpow : (0 : ℝ) < 2 ^ m := by positivity
  have hE := esym_nonneg g B (fun p hp => (hg p hp).1) m
  have e : (1 / 2 : ℝ) ^ m * ((Vp g B)⁻¹) ^ 2 = 1 / (2 ^ m * Vp g B ^ 2) := by
    field_simp
    rw [← mul_pow]; norm_num
  rw [e, le_div_iff₀ (by positivity)]
  have hV2 : 0 ≤ Vp g B ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 hV2]

lemma prod_one_add_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (δ : ι → ℝ)
    (hδ : ∀ j ∈ s, 0 ≤ δ j) (hs : ∑ j ∈ s, δ j ≤ 1 / 2) :
    ∏ j ∈ s, (1 + δ j) ≤ 1 + 2 * ∑ j ∈ s, δ j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha] at *
    have hda := hδ a (mem_insert_self a s)
    have hδs : ∀ j ∈ s, 0 ≤ δ j := fun j hj => hδ j (mem_insert_of_mem hj)
    have hsum : 0 ≤ ∑ j ∈ s, δ j := sum_nonneg hδs
    have IH := ih hδs (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left IH hda]

/-- **A3. Product perturbation.** If `0 < V_j`, `0 ≤ D_j`, `V_j ≤ U_j ≤ V_j + D_j` and
`E = Σ D_j / V_j ≤ 1/2`, then `∏ U ≤ V (1 + 2E)` and `∏ U - Σ_j D_j ∏_{i ≠ j} U_i ≥ V (1 - 2E)`. -/
theorem perturb {ι : Type*} [DecidableEq ι] (s : Finset ι) (V U D : ι → ℝ)
    (hV : ∀ j ∈ s, 0 < V j) (hD : ∀ j ∈ s, 0 ≤ D j) (hU : ∀ j ∈ s, V j ≤ U j ∧ U j ≤ V j + D j)
    (hE : ∑ j ∈ s, D j / V j ≤ 1 / 2) :
    ∏ j ∈ s, U j ≤ (∏ j ∈ s, V j) * (1 + 2 * ∑ j ∈ s, D j / V j) ∧
      (∏ j ∈ s, V j) * (1 - 2 * ∑ j ∈ s, D j / V j)
        ≤ ∏ j ∈ s, U j - ∑ j ∈ s, D j * ∏ i ∈ s.erase j, U i := by
  set δ : ι → ℝ := fun j => D j / V j with hδdef
  have hδ : ∀ j ∈ s, 0 ≤ δ j := fun j hj => div_nonneg (hD j hj) (hV j hj).le
  have hUle : ∀ t ⊆ s, ∏ j ∈ t, U j ≤ (∏ j ∈ t, V j) * ∏ j ∈ t, (1 + δ j) := by
    intro t ht
    rw [← prod_mul_distrib]
    refine prod_le_prod (fun j hj => by linarith [hV j (ht hj), (hU j (ht hj)).1]) fun j hj => ?_
    have hv := hV j (ht hj)
    have : V j * (1 + δ j) = V j + D j := by simp only [hδdef]; field_simp
    rw [this]; exact (hU j (ht hj)).2
  have hVpos : ∀ t ⊆ s, 0 < ∏ j ∈ t, V j := fun t ht => prod_pos fun j hj => hV j (ht hj)
  have hsub : ∀ t ⊆ s, ∏ j ∈ t, (1 + δ j) ≤ 1 + 2 * ∑ j ∈ t, δ j := fun t ht =>
    prod_one_add_le t δ (fun j hj => hδ j (ht hj))
      (le_trans (sum_le_sum_of_subset_of_nonneg ht fun j hj _ => hδ j hj) hE)
  constructor
  · have h1 := hUle s subset_rfl
    have h2 := hsub s subset_rfl
    have h3 := hVpos s subset_rfl
    exact h1.trans (mul_le_mul_of_nonneg_left h2 h3.le)
  · have hlow : ∏ j ∈ s, V j ≤ ∏ j ∈ s, U j :=
      prod_le_prod (fun j hj => (hV j hj).le) fun j hj => (hU j hj).1
    have hterm : ∀ j ∈ s, D j * ∏ i ∈ s.erase j, U i ≤ 2 * (δ j * ∏ i ∈ s, V i) := by
      intro j hj
      have hes : s.erase j ⊆ s := erase_subset j s
      have a1 := hUle _ hes
      have a2 := hsub _ hes
      have a3 := hVpos _ hes
      have a4 : ∑ i ∈ s.erase j, δ i ≤ 1 / 2 :=
        le_trans (sum_le_sum_of_subset_of_nonneg hes fun i hi _ => hδ i hi) hE
      have hPe : ∏ i ∈ s.erase j, U i ≤ (∏ i ∈ s.erase j, V i) * 2 :=
        a1.trans (mul_le_mul_of_nonneg_left (by linarith) a3.le)
      have hmul : δ j * ∏ i ∈ s, V i = D j * ∏ i ∈ s.erase j, V i := by
        rw [← mul_prod_erase s V hj]
        have hv := hV j hj
        simp only [hδdef]; field_simp
      rw [hmul]
      nlinarith [mul_le_mul_of_nonneg_left hPe (hD j hj)]
    have hsumle : ∑ j ∈ s, D j * ∏ i ∈ s.erase j, U i ≤ 2 * ((∑ j ∈ s, δ j) * ∏ i ∈ s, V i) := by
      rw [sum_mul, mul_sum]; exact sum_le_sum hterm
    simp only [hδdef] at hsumle
    nlinarith

end Erdos971.FL
