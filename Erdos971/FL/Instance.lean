import Erdos971.FL.Blocks
import Erdos971.Axioms

/-!
# Fundamental lemma, part C: instantiation for the primes below `z`

Proves `fundamental_lemma_proved`, with EXACTLY the statement of the axiom `fundamental_lemma` in
`Erdos971/Axioms.lean` (so the axiom can be deleted and replaced by this theorem).
-/

open Real Finset Filter Topology

namespace Erdos971.FLC
open Erdos971 Erdos971.FL

lemma mem_primesLT' {z : ℝ} {p : ℕ} (hp : p ∈ primesLT z) : p.Prime ∧ (p : ℝ) < z := by
  simp only [primesLT, mem_filter] at hp
  exact hp.2

/-- Block index of `p`: `j` with `2^j ≤ log z / log p < 2^(j+1)`. -/
noncomputable def blkOf (z : ℝ) (p : ℕ) : ℕ := Nat.log 2 ⌊Real.log z / Real.log p⌋₊

noncomputable def Jof (z : ℝ) : ℕ := Nat.log 2 ⌊Real.log z / Real.log 2⌋₊ + 1

def rOf (n b : ℕ) (j : ℕ) : ℕ := 2 * n + 2 * b * (j + 1)

lemma rOf_even (n b j : ℕ) : Even (rOf n b j) := by
  refine ⟨n + b * (j + 1), ?_⟩
  unfold rOf; ring

lemma log_p_pos {z : ℝ} {p : ℕ} (hp : p ∈ primesLT z) : 0 < Real.log p := by
  have h2 := (mem_primesLT' hp).1.two_le
  apply Real.log_pos
  exact_mod_cast (by omega : 1 < p)

lemma blk_bounds {z : ℝ} {p : ℕ} (hp : p ∈ primesLT z) :
    (2 : ℝ) ^ blkOf z p * Real.log p ≤ Real.log z ∧
      Real.log z < (2 : ℝ) ^ (blkOf z p + 1) * Real.log p := by
  have hlp := log_p_pos hp
  have hpz := (mem_primesLT' hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_primesLT' hp).1.pos
  have hlz : Real.log p < Real.log z := Real.log_lt_log hp0 hpz
  set t := Real.log z / Real.log p with ht
  have ht1 : 1 < t := by rw [ht, one_lt_div hlp]; exact hlz
  have hm : ⌊t⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht1.le)
    omega
  have h1 := Nat.pow_log_le_self 2 hm
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊t⌋₊
  have e1 : (2 : ℝ) ^ blkOf z p ≤ t := by
    calc (2 : ℝ) ^ blkOf z p = ((2 ^ blkOf z p : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ t := Nat.floor_le (by linarith)
  have e2 : t < (2 : ℝ) ^ (blkOf z p + 1) := by
    calc t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
      _ ≤ ((2 ^ (blkOf z p + 1) : ℕ) : ℝ) := by
          have : ⌊t⌋₊ + 1 ≤ 2 ^ (blkOf z p + 1) := h2
          exact_mod_cast this
      _ = (2 : ℝ) ^ (blkOf z p + 1) := by push_cast; rfl
  constructor
  · rw [le_div_iff₀ hlp] at e1; exact e1
  · rw [div_lt_iff₀ hlp] at e2; exact e2

lemma blk_lt_J {z : ℝ} {p : ℕ} (hp : p ∈ primesLT z) : blkOf z p < Jof z := by
  have hlp := log_p_pos hp
  have hpz := (mem_primesLT' hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_primesLT' hp).1.pos
  have hlz : Real.log p < Real.log z := Real.log_lt_log hp0 hpz
  have hl2 : Real.log 2 ≤ Real.log p := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast (mem_primesLT' hp).1.two_le
  have hle : Real.log z / Real.log p ≤ Real.log z / Real.log 2 :=
    div_le_div_of_nonneg_left (by linarith) (Real.log_pos (by norm_num)) hl2
  unfold blkOf Jof
  exact Nat.lt_succ_of_le (Nat.log_mono_right (Nat.floor_mono hle))

/-- finite geometric sums -/
lemma geom_half (J : ℕ) : ∑ j ∈ range J, (1 / 2 : ℝ) ^ j = 2 - 2 * (1 / 2 : ℝ) ^ J := by
  induction J with
  | zero => simp
  | succ J ih => rw [sum_range_succ, ih, pow_succ]; ring

lemma geom_half' (J : ℕ) :
    ∑ j ∈ range J, ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ j = 4 - (2 * J + 4) * (1 / 2 : ℝ) ^ J := by
  induction J with
  | zero => simp
  | succ J ih => rw [sum_range_succ, ih, pow_succ]; push_cast; ring

lemma geom_quarter (J : ℕ) : ∑ j ∈ range J, (1 / 4 : ℝ) ^ (j + 1) ≤ 1 := by
  have : ∀ J : ℕ, ∑ j ∈ range J, (1 / 4 : ℝ) ^ (j + 1) = (1 - (1 / 4 : ℝ) ^ J) / 3 := by
    intro J
    induction J with
    | zero => simp
    | succ J ih => rw [sum_range_succ, ih, pow_succ]; ring
  rw [this]
  have : 0 ≤ (1 / 4 : ℝ) ^ J := by positivity
  linarith

lemma geom_bound (J n b : ℕ) :
    ∑ j ∈ range J, ((rOf n b j : ℝ) + 1) * (1 / 2 : ℝ) ^ j ≤ 4 * n + 8 * b + 2 := by
  have h1 := geom_half J
  have h2 := geom_half' J
  have e : ∑ j ∈ range J, ((rOf n b j : ℝ) + 1) * (1 / 2 : ℝ) ^ j
      = (2 * n + 1) * ∑ j ∈ range J, (1 / 2 : ℝ) ^ j
        + 2 * b * ∑ j ∈ range J, ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ j := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    unfold rOf; push_cast; ring
  rw [e, h1, h2]
  have : 0 ≤ (1 / 2 : ℝ) ^ J := by positivity
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have hb : (0 : ℝ) ≤ b := b.cast_nonneg
  have hJ : (0 : ℝ) ≤ J := J.cast_nonneg
  nlinarith [mul_nonneg hn this, mul_nonneg hb this, mul_nonneg (mul_nonneg hb hJ) this]


lemma level_bound {z s : ℝ} (hz : 2 ≤ z) {n b : ℕ} (hs : 4 * (n : ℝ) + 8 * b + 2 ≤ s)
    {D : Finset ℕ} (hD : D ⊆ primesLT z)
    (hcnt : ∀ j < Jof z, cnt (blkOf z) D j ≤ rOf n b j + 1) :
    ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ s := by
  have hz0 : 0 < z := by linarith
  have hlz : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  have hpos : ∀ p ∈ D, (0 : ℝ) < p := fun p hp => by
    exact_mod_cast (mem_primesLT' (hD hp)).1.pos
  have hd0 : (0 : ℝ) < ∏ p ∈ D, (p : ℝ) := prod_pos hpos
  push_cast
  have hlog : Real.log (∏ p ∈ D, (p : ℝ)) = ∑ p ∈ D, Real.log p :=
    Real.log_prod (fun p hp => (hpos p hp).ne')
  have key : ∑ p ∈ D, Real.log p ≤ Real.log z * s := by
    rw [← sum_fiberwise_of_maps_to (g := blkOf z) (t := range (Jof z))
      (fun p hp => mem_range.2 (blk_lt_J (hD hp)))]
    calc ∑ j ∈ range (Jof z), ∑ p ∈ D with blkOf z p = j, Real.log p
        ≤ ∑ j ∈ range (Jof z), ((rOf n b j : ℝ) + 1) * (Real.log z * (1 / 2 : ℝ) ^ j) := by
          refine sum_le_sum fun j hj => ?_
          have hterm : ∀ p ∈ D.filter (fun p => blkOf z p = j),
              Real.log p ≤ Real.log z * (1 / 2 : ℝ) ^ j := by
            intro p hp
            rw [mem_filter] at hp
            have := (blk_bounds (hD hp.1)).1
            rw [hp.2] at this
            rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
            linarith
          have h1 := sum_le_card_nsmul _ _ _ hterm
          rw [nsmul_eq_mul] at h1
          have hc : ((D.filter (fun p => blkOf z p = j)).card : ℝ) ≤ (rOf n b j : ℝ) + 1 := by
            have := hcnt j (mem_range.1 hj)
            unfold cnt at this
            exact_mod_cast this
          refine h1.trans ?_
          exact mul_le_mul_of_nonneg_right hc (by positivity)
      _ = Real.log z * ∑ j ∈ range (Jof z), ((rOf n b j : ℝ) + 1) * (1 / 2 : ℝ) ^ j := by
          rw [mul_sum]; refine sum_congr rfl fun j _ => ?_; ring
      _ ≤ Real.log z * s := by
          apply mul_le_mul_of_nonneg_left _ hlz
          exact (geom_bound _ n b).trans hs
  rw [Real.rpow_def_of_pos hz0, ← Real.exp_log hd0, hlog]
  exact Real.exp_le_exp.2 key


lemma Vinv_bound {κ K : ℝ} (hκ : 0 ≤ κ) (hK : 1 ≤ K) {z : ℝ} (hz : 2 ≤ z) {g : ℕ → ℝ}
    (hg : ∀ p ∈ primesLT z, 0 ≤ g p ∧ g p < 1)
    (hdim : ∀ w : ℝ, 2 ≤ w → w < z →
        ∏ p ∈ (primesLT z).filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - g p)⁻¹
          ≤ K * (Real.log z / Real.log w) ^ κ) (j : ℕ) :
    (Vp g (block (primesLT z) (blkOf z) j))⁻¹ ≤ K * ((2 : ℝ) ^ (j + 1)) ^ κ := by
  set B := block (primesLT z) (blkOf z) j with hBdef
  have hX1 : (1 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := one_le_pow₀ (by norm_num)
  by_cases hne : B = ∅
  · rw [hne]; simp only [Vp, prod_empty, inv_one]
    exact one_le_mul_of_one_le_of_one_le hK (Real.one_le_rpow hX1 hκ)
  obtain ⟨p, hp⟩ := nonempty_iff_ne_empty.2 hne
  have hpP : p ∈ primesLT z := (mem_filter.1 hp).1
  have hz0 : 0 < z := by linarith
  have hz2 : 2 < z := by
    have := (mem_primesLT' hpP)
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast this.1.two_le
    linarith [this.2]
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hX0 : (0 : ℝ) < (2 : ℝ) ^ (j + 1) := by positivity
  set w := max 2 (Real.exp (Real.log z / 2 ^ (j + 1))) with hw
  have hw2 : 2 ≤ w := le_max_left _ _
  have hwz : w < z := by
    refine max_lt hz2 ?_
    rw [← Real.exp_log hz0]
    apply Real.exp_lt_exp.2
    rw [Real.exp_log hz0]
    exact div_lt_self hlz (one_lt_pow₀ (by norm_num) (by omega))
  have hlw : Real.log z / 2 ^ (j + 1) ≤ Real.log w := by
    have := Real.log_le_log (Real.exp_pos _) (le_max_right 2 (Real.exp (Real.log z / 2 ^ (j + 1))))
    rwa [Real.log_exp] at this
  have hlw0 : 0 < Real.log w := lt_of_lt_of_le (by positivity) hlw
  set W := (primesLT z).filter (fun p : ℕ => w ≤ (p : ℝ)) with hWdef
  have hBW : B ⊆ W := by
    intro q hq
    have hq' := mem_filter.1 hq
    rw [mem_filter]
    refine ⟨hq'.1, max_le ?_ ?_⟩
    · exact_mod_cast (mem_primesLT' hq'.1).1.two_le
    · have hq0 : (0 : ℝ) < q := by exact_mod_cast (mem_primesLT' hq'.1).1.pos
      rw [← Real.exp_log hq0]
      apply Real.exp_le_exp.2
      have := (blk_bounds hq'.1).2
      rw [hq'.2] at this
      rw [div_le_iff₀ hX0]; linarith
  have hgW : ∀ q ∈ W, 0 < 1 - g q := fun q hq => by
    have := hg q (mem_filter.1 hq).1; linarith
  have VWpos : 0 < Vp g W := prod_pos hgW
  have VW : Vp g W ≤ Vp g B := by
    unfold Vp
    rw [← prod_sdiff hBW]
    apply mul_le_of_le_one_left
    · exact prod_nonneg fun q hq => (hgW q (hBW hq)).le
    · apply prod_le_one
      · exact fun q hq => (hgW q (mem_sdiff.1 hq).1).le
      · intro q hq
        have := hg q (mem_filter.1 (mem_sdiff.1 hq).1).1
        linarith
  have hratio : Real.log z / Real.log w ≤ (2 : ℝ) ^ (j + 1) := by
    rw [div_le_iff₀ hlw0]
    rw [div_le_iff₀ hX0] at hlw
    linarith
  calc (Vp g B)⁻¹ ≤ (Vp g W)⁻¹ := inv_anti₀ VWpos VW
    _ = ∏ p ∈ W, (1 - g p)⁻¹ := by rw [Vp, prod_inv_distrib]
    _ ≤ K * (Real.log z / Real.log w) ^ κ := hdim w hw2 hwz
    _ ≤ K * ((2 : ℝ) ^ (j + 1)) ^ κ := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact Real.rpow_le_rpow (div_nonneg hlz.le hlw0.le) hratio hκ

lemma pow_identity (n c j : ℕ) :
    (1 / 2 : ℝ) ^ (2 * n + (c + 2) * (j + 1) + 1) * ((2 : ℝ) ^ (j + 1)) ^ c
      = 1 / 2 * (1 / 4 : ℝ) ^ n * (1 / 4 : ℝ) ^ (j + 1) := by
  have e1 : (1 / 2 : ℝ) ^ (2 * n + (c + 2) * (j + 1) + 1)
      = ((1 / 2 : ℝ) ^ 2) ^ n * ((((1 / 2 : ℝ) ^ (j + 1)) ^ c) * ((1 / 2 : ℝ) ^ 2) ^ (j + 1))
        * (1 / 2) := by
    rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_succ]
    congr 1; ring
  have e2 : ((1 / 2 : ℝ) ^ (j + 1)) ^ c * ((2 : ℝ) ^ (j + 1)) ^ c = 1 := by
    rw [← mul_pow, ← mul_pow]; norm_num
  rw [e1]
  norm_num
  linear_combination ((1 / 4 : ℝ) ^ n * (1 / 4 : ℝ) ^ (j + 1) * (1 / 2)) * e2

lemma delta_bound {κ K : ℝ} (hK : 1 ≤ K) {b : ℕ} (hb : 3 * κ + 2 ≤ 2 * (b : ℝ))
    (hb1 : 1 ≤ b) (n j : ℕ) {V E : ℝ} (hV : 0 < V)
    (hE : E ≤ (1 / 2 : ℝ) ^ (rOf n b j + 1) * (V⁻¹) ^ 2)
    (hVinv : V⁻¹ ≤ K * ((2 : ℝ) ^ (j + 1)) ^ κ) :
    E / V ≤ K ^ 3 / 2 * (1 / 4 : ℝ) ^ n * (1 / 4 : ℝ) ^ (j + 1) := by
  set X : ℝ := (2 : ℝ) ^ (j + 1) with hX
  have hX1 : 1 ≤ X := one_le_pow₀ (by norm_num)
  obtain ⟨c, hc⟩ : ∃ c, 2 * b = c + 2 := ⟨2 * b - 2, by omega⟩
  have hY : (X ^ κ) ^ 3 ≤ X ^ c := by
    rw [← Real.rpow_mul_natCast (by linarith), ← Real.rpow_natCast X c]
    apply Real.rpow_le_rpow_of_exponent_le hX1
    have : (c : ℝ) = 2 * b - 2 := by
      have : ((2 * b : ℕ) : ℝ) = ((c + 2 : ℕ) : ℝ) := by rw [hc]
      push_cast at this; linarith
    push_cast; linarith
  have hVi0 : 0 ≤ V⁻¹ := (inv_pos.2 hV).le
  have hV3 : (V⁻¹) ^ 3 ≤ K ^ 3 * X ^ c := by
    calc (V⁻¹) ^ 3 ≤ (K * X ^ κ) ^ 3 := pow_le_pow_left₀ hVi0 hVinv 3
      _ = K ^ 3 * (X ^ κ) ^ 3 := by ring
      _ ≤ K ^ 3 * X ^ c := mul_le_mul_of_nonneg_left hY (by positivity)
  have hr : rOf n b j + 1 = 2 * n + (c + 2) * (j + 1) + 1 := by
    unfold rOf; rw [← hc]
  calc E / V = E * V⁻¹ := div_eq_mul_inv _ _
    _ ≤ (1 / 2 : ℝ) ^ (rOf n b j + 1) * (V⁻¹) ^ 2 * V⁻¹ := mul_le_mul_of_nonneg_right hE hVi0
    _ = (1 / 2 : ℝ) ^ (rOf n b j + 1) * (V⁻¹) ^ 3 := by ring
    _ ≤ (1 / 2 : ℝ) ^ (rOf n b j + 1) * (K ^ 3 * X ^ c) :=
        mul_le_mul_of_nonneg_left hV3 (by positivity)
    _ = K ^ 3 * ((1 / 2 : ℝ) ^ (2 * n + (c + 2) * (j + 1) + 1) * X ^ c) := by rw [hr]; ring
    _ = K ^ 3 / 2 * (1 / 4 : ℝ) ^ n * (1 / 4 : ℝ) ^ (j + 1) := by rw [hX, pow_identity]; ring


lemma subset_filter_dvd_iff {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {D : Finset ℕ} (hD : D ⊆ P)
    (m : ℕ) : D ⊆ P.filter (· ∣ m) ↔ (∏ p ∈ D, p) ∣ m := by
  constructor
  · intro h
    exact Finset.prod_primes_dvd m (fun a ha => (hP a (hD ha)).prime)
      (fun a ha => (mem_filter.1 (h ha)).2)
  · intro h p hp
    exact mem_filter.2 ⟨hD hp, (dvd_prod_of_mem _ hp).trans h⟩

lemma coprime_iff_filter {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    Nat.Coprime m (∏ p ∈ P, p) ↔ P.filter (· ∣ m) = ∅ := by
  rw [Nat.coprime_prod_right_iff, filter_eq_empty_iff]
  refine forall₂_congr fun p hp => ?_
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (hP p hp)]

lemma swap_sum {ι : Type} (A : Finset ι) (f : ι → ℕ) {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (lam : Finset ℕ → ℝ) :
    ∑ i ∈ A, ∑ D ∈ (P.filter (· ∣ f i)).powerset, lam D
      = ∑ D ∈ P.powerset, lam D * ((A.filter (fun i => (∏ p ∈ D, p) ∣ f i)).card : ℝ) := by
  have h1 : ∀ i ∈ A, ∑ D ∈ (P.filter (· ∣ f i)).powerset, lam D
      = ∑ D ∈ P.powerset, if (∏ p ∈ D, p) ∣ f i then lam D else 0 := by
    intro i _
    rw [← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext D
    simp only [mem_powerset, mem_filter]
    constructor
    · intro h
      exact ⟨h.trans (filter_subset _ _),
        (subset_filter_dvd_iff hP (h.trans (filter_subset _ _)) _).1 h⟩
    · rintro ⟨h1, h2⟩
      exact (subset_filter_dvd_iff hP h1 _).2 h2
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun D _ => ?_
  rw [card_filter]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- remainder `r_d`. -/
noncomputable def remd {ι : Type} (A : Finset ι) (f : ι → ℕ) (g : ℕ → ℝ) (X : ℝ) (d : ℕ) : ℝ :=
  ((A.filter (fun i => d ∣ f i)).card : ℝ) - X * ∏ p ∈ d.primeFactors, g p

lemma Pz_ne_zero (z : ℝ) : Pz z ≠ 0 := by
  unfold Pz
  exact prod_ne_zero_iff.2 fun p hp => (mem_primesLT' hp).1.ne_zero

lemma err_bound {ι : Type} (A : Finset ι) (f : ι → ℕ) (g : ℕ → ℝ) (X : ℝ) (z s : ℝ)
    (lam : Finset ℕ → ℝ) (hlam : ∀ D, |lam D| ≤ 1)
    (hsupp : ∀ D ⊆ primesLT z, lam D ≠ 0 → ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ s) :
    |∑ D ∈ (primesLT z).powerset, lam D * remd A f g X (∏ p ∈ D, p)|
      ≤ ∑ d ∈ (Pz z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ s), |remd A f g X d| := by
  have hprimes : ∀ D ∈ (primesLT z).powerset, ∀ p ∈ D, p.Prime :=
    fun D hD p hp => (mem_primesLT' (mem_powerset.1 hD hp)).1
  calc |∑ D ∈ (primesLT z).powerset, lam D * remd A f g X (∏ p ∈ D, p)|
      ≤ ∑ D ∈ (primesLT z).powerset, |lam D * remd A f g X (∏ p ∈ D, p)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ D ∈ (primesLT z).powerset,
          if ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ s then |remd A f g X (∏ p ∈ D, p)| else 0 := by
        refine sum_le_sum fun D hD => ?_
        split_ifs with h
        · rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (hlam D)
        · have : lam D = 0 := by
            by_contra hne
            exact h (hsupp D (mem_powerset.1 hD) hne)
          simp [this]
    _ = ∑ D ∈ (primesLT z).powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ s),
          |remd A f g X (∏ p ∈ D, p)| := (sum_filter _ _).symm
    _ = ∑ d ∈ ((primesLT z).powerset.filter
          (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ s)).image (fun D => ∏ p ∈ D, p),
          |remd A f g X d| := by
        rw [sum_image]
        intro D1 h1 D2 h2 h
        have e1 := Nat.primeFactors_prod (hprimes D1 (mem_filter.1 h1).1)
        have e2 := Nat.primeFactors_prod (hprimes D2 (mem_filter.1 h2).1)
        simp only at h
        rw [← e1, ← e2, h]
    _ ≤ ∑ d ∈ (Pz z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ s), |remd A f g X d| := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro d hd
          obtain ⟨D, hD, rfl⟩ := mem_image.1 hd
          have hD' := mem_filter.1 hD
          refine mem_filter.2 ⟨Nat.mem_divisors.2 ⟨?_, Pz_ne_zero z⟩, hD'.2⟩
          unfold Pz
          exact prod_dvd_prod_of_subset _ _ _ (mem_powerset.1 hD'.1)
        · intro _ _ _; exact abs_nonneg _

lemma card_eq_main_rem {ι : Type} (A : Finset ι) (f : ι → ℕ) (g : ℕ → ℝ) (X : ℝ)
    {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    ((A.filter (fun i => (∏ p ∈ D, p) ∣ f i)).card : ℝ)
      = X * ∏ p ∈ D, g p + remd A f g X (∏ p ∈ D, p) := by
  unfold remd
  rw [Nat.primeFactors_prod hD]
  ring

/-- Transfer: generic blocks. -/
lemma sieve_transfer {ι : Type} (A : Finset ι) (f : ι → ℕ) (g : ℕ → ℝ) (X : ℝ) (z s : ℝ)
    (blk : ℕ → ℕ) (J : ℕ) (r : ℕ → ℕ) (hP : ∀ p ∈ primesLT z, blk p < J) (hr : ∀ j, Even (r j))
    (hsupp : ∀ D ⊆ primesLT z, (lamPlus blk J r D ≠ 0 ∨ lamMinus blk J r D ≠ 0) →
      ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ s) :
    ((A.filter (fun i => Nat.Coprime (f i) (Pz z))).card : ℝ)
        ≤ X * ∑ D ∈ (primesLT z).powerset, lamPlus blk J r D * ∏ p ∈ D, g p
          + ∑ d ∈ (Pz z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ s), |remd A f g X d| ∧
      X * ∑ D ∈ (primesLT z).powerset, lamMinus blk J r D * ∏ p ∈ D, g p
          - ∑ d ∈ (Pz z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ s), |remd A f g X d|
        ≤ ((A.filter (fun i => Nat.Coprime (f i) (Pz z))).card : ℝ) := by
  set P := primesLT z with hPdef
  set R := ∑ d ∈ (Pz z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ s), |remd A f g X d|
  have hprime : ∀ p ∈ P, p.Prime := fun p hp => (mem_primesLT' hp).1
  have hS : ((A.filter (fun i => Nat.Coprime (f i) (Pz z))).card : ℝ)
      = ∑ i ∈ A, (if P.filter (· ∣ f i) = ∅ then (1 : ℝ) else 0) := by
    rw [card_filter]
    push_cast
    refine sum_congr rfl fun i _ => ?_
    unfold Pz
    rw [← hPdef]
    simp only [coprime_iff_filter hprime]
  have hexp : ∀ lam : Finset ℕ → ℝ,
      ∑ i ∈ A, ∑ D ∈ (P.filter (· ∣ f i)).powerset, lam D
        = X * ∑ D ∈ P.powerset, lam D * ∏ p ∈ D, g p
          + ∑ D ∈ P.powerset, lam D * remd A f g X (∏ p ∈ D, p) := by
    intro lam
    rw [swap_sum A f hprime, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun D hD => ?_
    rw [card_eq_main_rem A f g X (fun p hp => hprime p (mem_powerset.1 hD hp))]
    ring
  have hsieve := fun i => lam_sieve P blk J r hP hr (P.filter (· ∣ f i)) (filter_subset _ _)
  constructor
  · have e := err_bound A f g X z s (lamPlus blk J r) (abs_lamPlus_le blk J r)
      (fun D hD h => hsupp D hD (Or.inl h))
    have h1 : ((A.filter (fun i => Nat.Coprime (f i) (Pz z))).card : ℝ)
        ≤ ∑ i ∈ A, ∑ D ∈ (P.filter (· ∣ f i)).powerset, lamPlus blk J r D := by
      rw [hS]; exact sum_le_sum fun i _ => (hsieve i).2
    rw [hexp] at h1
    have := le_abs_self (∑ D ∈ P.powerset, lamPlus blk J r D * remd A f g X (∏ p ∈ D, p))
    linarith
  · have e := err_bound A f g X z s (lamMinus blk J r) (abs_lamMinus_le blk J r)
      (fun D hD h => hsupp D hD (Or.inr h))
    have h1 : ∑ i ∈ A, ∑ D ∈ (P.filter (· ∣ f i)).powerset, lamMinus blk J r D
        ≤ ((A.filter (fun i => Nat.Coprime (f i) (Pz z))).card : ℝ) := by
      rw [hS]; exact sum_le_sum fun i _ => (hsieve i).1
    rw [hexp] at h1
    have := neg_abs_le (∑ D ∈ P.powerset, lamMinus blk J r D * remd A f g X (∏ p ∈ D, p))
    linarith


lemma main_terms {κ K : ℝ} (hκ : 0 ≤ κ) (hK : 1 ≤ K) {b : ℕ} (hb : 3 * κ + 2 ≤ 2 * (b : ℝ))
    (hb1 : 1 ≤ b) {z : ℝ} (hz : 2 ≤ z) {g : ℕ → ℝ}
    (hg : ∀ p ∈ primesLT z, 0 ≤ g p ∧ g p < 1)
    (hdim : ∀ w : ℝ, 2 ≤ w → w < z →
        ∏ p ∈ (primesLT z).filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - g p)⁻¹
          ≤ K * (Real.log z / Real.log w) ^ κ)
    (n : ℕ) (hsmall : K ^ 3 * (1 / 4 : ℝ) ^ n ≤ 1) :
    ∑ D ∈ (primesLT z).powerset, lamPlus (blkOf z) (Jof z) (rOf n b) D * ∏ p ∈ D, g p
        ≤ (∏ p ∈ primesLT z, (1 - g p)) * (1 + K ^ 3 * (1 / 4 : ℝ) ^ n) ∧
      (∏ p ∈ primesLT z, (1 - g p)) * (1 - K ^ 3 * (1 / 4 : ℝ) ^ n)
        ≤ ∑ D ∈ (primesLT z).powerset, lamMinus (blkOf z) (Jof z) (rOf n b) D * ∏ p ∈ D, g p := by
  set P := primesLT z with hPdef
  have hP : ∀ p ∈ P, blkOf z p < Jof z := fun p hp => blk_lt_J hp
  have hgB : ∀ j, ∀ p ∈ block P (blkOf z) j, 0 ≤ g p ∧ g p < 1 :=
    fun j p hp => hg p (mem_filter.1 hp).1
  have hVpos : ∀ j, 0 < Vp g (block P (blkOf z) j) :=
    fun j => (esym_rankin g _ (hgB j) 0).1
  have hbon : ∀ j, Vp g (block P (blkOf z) j) ≤ Utr g (block P (blkOf z) j) (rOf n b j) ∧
      Utr g (block P (blkOf z) j) (rOf n b j)
        ≤ Vp g (block P (blkOf z) j) + Esym g (block P (blkOf z) j) (rOf n b j + 1) :=
    fun j => bonferroni_weighted g _ (fun p hp => ⟨(hgB j p hp).1, (hgB j p hp).2.le⟩)
      (rOf n b j) (rOf_even n b j)
  have hDnn : ∀ j, 0 ≤ Esym g (block P (blkOf z) j) (rOf n b j + 1) := by
    intro j
    unfold Esym
    refine sum_nonneg fun D hD => prod_nonneg fun p hp => ?_
    exact (hgB j p ((mem_powersetCard.1 hD).1 hp)).1
  have hδ : ∀ j, Esym g (block P (blkOf z) j) (rOf n b j + 1) / Vp g (block P (blkOf z) j)
      ≤ K ^ 3 / 2 * (1 / 4 : ℝ) ^ n * (1 / 4 : ℝ) ^ (j + 1) :=
    fun j => delta_bound hK hb hb1 n j (hVpos j) (esym_rankin g _ (hgB j) _).2
      (Vinv_bound hκ hK hz hg hdim j)
  have hEsum : ∑ j ∈ range (Jof z),
      Esym g (block P (blkOf z) j) (rOf n b j + 1) / Vp g (block P (blkOf z) j)
        ≤ K ^ 3 / 2 * (1 / 4 : ℝ) ^ n := by
    calc _ ≤ ∑ j ∈ range (Jof z), K ^ 3 / 2 * (1 / 4 : ℝ) ^ n * (1 / 4 : ℝ) ^ (j + 1) :=
          sum_le_sum fun j _ => hδ j
      _ = K ^ 3 / 2 * (1 / 4 : ℝ) ^ n * ∑ j ∈ range (Jof z), (1 / 4 : ℝ) ^ (j + 1) := by
          rw [mul_sum]
      _ ≤ K ^ 3 / 2 * (1 / 4 : ℝ) ^ n * 1 :=
          mul_le_mul_of_nonneg_left (geom_quarter _) (by positivity)
      _ = K ^ 3 / 2 * (1 / 4 : ℝ) ^ n := mul_one _
  have hE : ∑ j ∈ range (Jof z),
      Esym g (block P (blkOf z) j) (rOf n b j + 1) / Vp g (block P (blkOf z) j) ≤ 1 / 2 := by
    linarith
  obtain ⟨h1, h2⟩ := perturb (range (Jof z)) (fun j => Vp g (block P (blkOf z) j))
    (fun j => Utr g (block P (blkOf z) j) (rOf n b j))
    (fun j => Esym g (block P (blkOf z) j) (rOf n b j + 1))
    (fun j _ => hVpos j) (fun j _ => hDnn j) (fun j _ => hbon j) hE
  have hprod : ∏ j ∈ range (Jof z), Vp g (block P (blkOf z) j) = ∏ p ∈ P, (1 - g p) := by
    unfold Vp block
    exact prod_fiberwise_of_maps_to (fun p hp => mem_range.2 (hP p hp)) _
  rw [hprod] at h1 h2
  have hVg0 : 0 ≤ ∏ p ∈ P, (1 - g p) :=
    prod_nonneg fun p hp => by have := hg p hp; linarith
  rw [sum_lamPlus_eq P _ _ _ hP g, sum_lamMinus_eq P _ _ _ hP (rOf_even n b) g]
  constructor
  · refine h1.trans (mul_le_mul_of_nonneg_left ?_ hVg0)
    linarith
  · refine le_trans (mul_le_mul_of_nonneg_left ?_ hVg0) h2
    linarith

lemma quarter_exp (s : ℝ) :
    (1 / 4 : ℝ) ^ ⌊s / 8⌋₊ ≤ 4 * Real.exp (-(Real.log 2 / 4 * s)) := by
  set n := ⌊s / 8⌋₊
  have hn : s / 8 < n + 1 := Nat.lt_floor_add_one _
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e1 : (1 / 4 : ℝ) ^ n = Real.exp (n * -Real.log 4) := by
    rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have e2 : 4 * Real.exp (-(Real.log 2 / 4 * s)) = Real.exp (Real.log 4 + -(Real.log 2 / 4 * s)) := by
    rw [Real.exp_add, Real.exp_log (by norm_num)]
  rw [e1, e2, Real.exp_le_exp, hl4]
  nlinarith

lemma tendsto_eta (K : ℝ) :
    Tendsto (fun s => s * (8 * K ^ 3 * Real.exp (-(Real.log 2 / 4 * s)))) atTop (𝓝 0) := by
  set a := Real.log 2 / 4 with ha
  have ha0 : 0 < a := by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); rw [ha]; positivity
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (tendsto_id.const_mul_atTop ha0)
  have h2 := h.const_mul (8 * K ^ 3 / a)
  rw [mul_zero] at h2
  refine h2.congr fun s => ?_
  simp only [Function.comp, id, pow_one]
  field_simp


end Erdos971.FLC


namespace Erdos971

theorem fundamental_lemma_proved (κ K : ℝ) (hκ : 0 < κ) (hK : 1 ≤ K) :
  ∃ η : ℝ → ℝ, Tendsto (fun s => s * η s) atTop (𝓝 0) ∧ ∃ s₀ : ℝ, ∀ z s : ℝ, 2 ≤ z → s₀ ≤ s →
    ∀ {ι : Type} (A : Finset ι) (f : ι → ℕ) (g : ℕ → ℝ) (X : ℝ), 0 ≤ X →
      (∀ p ∈ primesLT z, 0 ≤ g p ∧ g p < 1) →
      (∀ w : ℝ, 2 ≤ w → w < z →
        ∏ p ∈ (primesLT z).filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - g p)⁻¹
          ≤ K * (Real.log z / Real.log w) ^ κ) →
      let S : ℝ := ((A.filter (fun i => Nat.Coprime (f i) (Pz z))).card : ℝ)
      let Vg : ℝ := ∏ p ∈ primesLT z, (1 - g p)
      let R : ℝ := ∑ d ∈ (Pz z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ s),
        |((A.filter (fun i => d ∣ f i)).card : ℝ) - X * ∏ p ∈ d.primeFactors, g p|
      S ≤ X * Vg * (1 + η s) + R ∧ X * Vg * (1 - η s) - R ≤ S := by
  dsimp only
  set b : ℕ := ⌈(3 * κ + 2) / 2⌉₊ with hbdef
  have hb : 3 * κ + 2 ≤ 2 * (b : ℝ) := by
    have := Nat.le_ceil ((3 * κ + 2) / 2); rw [← hbdef] at this; linarith
  have hb1 : 1 ≤ b := by
    have : (1 : ℝ) < b := by linarith
    exact_mod_cast this.le
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨fun s => 8 * K ^ 3 * Real.exp (-(Real.log 2 / 4 * s)), FLC.tendsto_eta K,
    max (16 * (b : ℝ) + 4) (Real.log (8 * K ^ 3) / (Real.log 2 / 4)), ?_⟩
  intro z s hz hs ι A f g X hX hg hdim
  dsimp only
  have hs1 : 16 * (b : ℝ) + 4 ≤ s := le_of_max_le_left hs
  have hs2 : Real.log (8 * K ^ 3) / (Real.log 2 / 4) ≤ s := le_of_max_le_right hs
  have hb0 : (0 : ℝ) ≤ b := b.cast_nonneg
  have hs0 : 0 ≤ s := by linarith
  set n := ⌊s / 8⌋₊ with hn
  have hn8 : (n : ℝ) ≤ s / 8 := Nat.floor_le (by linarith)
  have hlev : 4 * (n : ℝ) + 8 * b + 2 ≤ s := by linarith
  have hq : (1 / 4 : ℝ) ^ n ≤ 4 * Real.exp (-(Real.log 2 / 4 * s)) := FLC.quarter_exp s
  have hK3 : 1 ≤ K ^ 3 := one_le_pow₀ hK
  have hexp : Real.exp (-(Real.log 2 / 4 * s)) ≤ (8 * K ^ 3)⁻¹ := by
    have h1 : Real.log (8 * K ^ 3) ≤ Real.log 2 / 4 * s := by
      rw [div_le_iff₀ (by positivity)] at hs2; linarith
    rw [← Real.exp_log (by positivity : (0 : ℝ) < 8 * K ^ 3), ← Real.exp_neg]
    exact Real.exp_le_exp.2 (by linarith)
  have hexp0 : 0 ≤ Real.exp (-(Real.log 2 / 4 * s)) := (Real.exp_pos _).le
  have hQ1 : K ^ 3 * (1 / 4 : ℝ) ^ n ≤ K ^ 3 * (4 * Real.exp (-(Real.log 2 / 4 * s))) :=
    mul_le_mul_of_nonneg_left hq (by linarith)
  have hsmall : K ^ 3 * (1 / 4 : ℝ) ^ n ≤ 1 := by
    have h2 : K ^ 3 * (4 * Real.exp (-(Real.log 2 / 4 * s))) ≤ K ^ 3 * (4 * (8 * K ^ 3)⁻¹) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h3 : K ^ 3 * (4 * (8 * K ^ 3)⁻¹) = 1 / 2 := by field_simp; norm_num
    linarith
  have hη : K ^ 3 * (1 / 4 : ℝ) ^ n ≤ 8 * K ^ 3 * Real.exp (-(Real.log 2 / 4 * s)) := by
    have : 0 ≤ K ^ 3 * Real.exp (-(Real.log 2 / 4 * s)) := mul_nonneg (by linarith) hexp0
    linarith
  obtain ⟨hM1, hM2⟩ := FLC.main_terms hκ.le hK hb hb1 hz hg hdim n hsmall
  obtain ⟨hT1, hT2⟩ := FLC.sieve_transfer A f g X z s (FLC.blkOf z) (FLC.Jof z) (FLC.rOf n b)
    (fun p hp => FLC.blk_lt_J hp) (FLC.rOf_even n b)
    (fun D hD h => FLC.level_bound hz hlev hD (fun j hj => FL.cnt_le_of_lam_ne _ _ _ D h j hj))
  have hR : ∑ d ∈ (Pz z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ s),
        |FLC.remd A f g X d|
      = ∑ d ∈ (Pz z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ s),
        |((A.filter (fun i => d ∣ f i)).card : ℝ) - X * ∏ p ∈ d.primeFactors, g p| := rfl
  rw [hR] at hT1 hT2
  have hVg0 : 0 ≤ ∏ p ∈ primesLT z, (1 - g p) :=
    prod_nonneg fun p hp => by have := hg p hp; linarith
  have hXV : 0 ≤ X * ∏ p ∈ primesLT z, (1 - g p) := mul_nonneg hX hVg0
  have hA1 := mul_le_mul_of_nonneg_left hM1 hX
  have hA2 := mul_le_mul_of_nonneg_left hM2 hX
  have hB := mul_le_mul_of_nonneg_left hη hXV
  constructor
  · nlinarith
  · nlinarith


/-- The fundamental lemma of sieve theory, in the consequence form used by the project
(formerly an axiom; now proved above). -/
alias fundamental_lemma := fundamental_lemma_proved

end Erdos971
