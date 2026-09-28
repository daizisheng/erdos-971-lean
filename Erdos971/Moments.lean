import Erdos971.Scale
import Erdos971.Singular
import Erdos971.Sieve
import Erdos971.MomentsComb

/-!
# Moments (BLUEPRINT §5).
-/

open Real Finset Filter Topology

namespace Erdos971

/-! ### Elementary growth facts -/

lemma ev_gt_one : ∀ᶠ q : ℕ in atTop, (1 : ℝ) < q := by
  filter_upwards [eventually_ge_atTop 2] with q hq
  exact_mod_cast (show 1 < q by omega)

/-- `(q log q)^e (log q)^m ≤ ε q / log q` eventually, for `e < 1`. -/
lemma ev_small (e m ε : ℝ) (he : e < 1) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, ((q : ℝ) * Real.log q) ^ e * (Real.log q) ^ m ≤ ε * (q / Real.log q) := by
  have h := (isLittleO_log_rpow_rpow_atTop (e + m + 1) (sub_pos.2 he)).bound hε
  have h2 := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h2, eventually_ge_atTop 3] with q hq hq3
  have hq1 : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (0 : ℝ) < q := by linarith
  have hl : 0 < Real.log q := Real.log_pos (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hl _),
    abs_of_pos (Real.rpow_pos_of_pos hq0 _)] at hq
  rw [Real.mul_rpow hq0.le hl.le, ← mul_div_assoc, le_div_iff₀ hl]
  have e1 : (q : ℝ) ^ e * Real.log q ^ e * Real.log q ^ m * Real.log q
      = (q : ℝ) ^ e * Real.log q ^ (e + m + 1) := by
    rw [Real.rpow_add hl, Real.rpow_add hl, Real.rpow_one]; ring
  have e2 : ε * (q : ℝ) = (q : ℝ) ^ e * (ε * (q : ℝ) ^ (1 - e)) := by
    rw [show (q : ℝ) ^ e * (ε * (q : ℝ) ^ (1 - e)) = ε * ((q : ℝ) ^ e * (q : ℝ) ^ (1 - e)) by ring,
      ← Real.rpow_add hq0]; simp
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg hq0.le _)

lemma xq_nonneg (q : ℕ) : 0 ≤ xq q := by
  unfold xq
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg q)

lemma xq_le_qlog (q : ℕ) : xq q ≤ q * Real.log q := by
  unfold xq
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le q) (Real.log_natCast_nonneg q)

/-- `q / log q ≤ φ(q)` eventually. -/
lemma ev_phi_ge : ∀ᶠ q : ℕ in atTop, (q : ℝ) / Real.log q ≤ q.totient := by
  filter_upwards [q_le_xq, eventually_ge_atTop 3] with q hq hq3
  have hl : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  rw [div_le_iff₀ hl]; unfold xq at hq; linarith

/-- `K ≤ log q`. -/
lemma Kq_le_log (q : ℕ) (hq : 0 < q) : (Kq q : ℝ) ≤ Real.log q := by
  unfold Kq
  have h0 : 0 ≤ xq q / q := div_nonneg (xq_nonneg q) (Nat.cast_nonneg _)
  calc (⌊xq q / q⌋₊ : ℝ) ≤ xq q / q := Nat.floor_le h0
    _ ≤ Real.log q := by
      rw [div_le_iff₀ (by exact_mod_cast hq)]; linarith [xq_le_qlog q]

/-- `q K ≤ x`. -/
lemma q_mul_Kq_le (q : ℕ) (hq : 0 < q) : (q : ℝ) * Kq q ≤ xq q := by
  unfold Kq
  have h0 : 0 ≤ xq q / q := div_nonneg (xq_nonneg q) (Nat.cast_nonneg _)
  have := Nat.floor_le h0
  rw [le_div_iff₀ (by exact_mod_cast hq)] at this
  linarith

/-- For fixed `e < 1`, `x^e ≤ ε φ(q)` eventually. -/
lemma ev_xpow_small (e ε : ℝ) (he : e < 1) (he0 : 0 ≤ e) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, xq q ^ e ≤ ε * q.totient := by
  filter_upwards [ev_small e 0 ε he hε, ev_phi_ge, eventually_ge_atTop 3] with q h1 h2 h3
  have hl : 1 ≤ Real.log q := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    have h3' : (3 : ℝ) ≤ q := by exact_mod_cast h3
    linarith
  rw [Real.rpow_zero, mul_one] at h1
  calc xq q ^ e ≤ ((q : ℝ) * Real.log q) ^ e :=
        Real.rpow_le_rpow (xq_nonneg q) (xq_le_qlog q) he0
    _ ≤ ε * (q / Real.log q) := h1
    _ ≤ ε * q.totient := mul_le_mul_of_nonneg_left h2 hε.le

/-- `V z ≥ 0`. -/
lemma V_nonneg (z : ℝ) : 0 ≤ V z := by
  unfold V
  apply Finset.prod_nonneg
  intro p hp
  simp only [primesLT, mem_filter] at hp
  have : (1 : ℝ) ≤ p := by exact_mod_cast hp.2.1.one_lt.le
  rw [sub_nonneg, div_le_one (by linarith)]; exact this

lemma Aq_nonneg (q u : ℕ) : 0 ≤ Aq q u := by
  unfold Aq; exact div_nonneg (mul_nonneg (xq_nonneg q) (V_nonneg _)) (Nat.cast_nonneg _)

/-- `η(s) → 0` and `s η(s) → 0` give `|η(u/4)| ≤ ε` and `|u η(u/4)| ≤ ε` for all large `u`. -/
lemma eta_small (η : ℝ → ℝ) (hη : Tendsto (fun s => s * η s) atTop (𝓝 0)) (ε : ℝ) (hε : 0 < ε) :
    ∃ u₁ : ℕ, ∀ u : ℕ, u₁ ≤ u → |η (u / 4)| ≤ ε ∧ |(u : ℝ) * η (u / 4)| ≤ ε := by
  have h4 : Tendsto (fun u : ℕ => ((u : ℝ) / 4) * η (u / 4)) atTop (𝓝 0) :=
    hη.comp (tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num))
  have hev := (h4.eventually (Metric.ball_mem_nhds 0 (show 0 < ε / 4 by positivity)))
  obtain ⟨u₁, hu₁⟩ := eventually_atTop.1 (hev.and (eventually_ge_atTop 4))
  refine ⟨u₁, fun u hu => ?_⟩
  obtain ⟨hb, h4u⟩ := hu₁ u hu
  simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hb
  have hu4 : (4 : ℝ) ≤ u := by exact_mod_cast h4u
  have habs : |(u : ℝ) * η (u / 4)| = 4 * |(u : ℝ) / 4 * η (u / 4)| := by
    rw [← abs_of_pos (show (0 : ℝ) < 4 by norm_num), ← abs_mul]; ring_nf
  have h2 : |(u : ℝ) * η (u / 4)| ≤ ε := by rw [habs]; linarith
  refine ⟨?_, h2⟩
  have : |(u : ℝ) * η (u / 4)| = u * |η (u / 4)| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg u)]
  rw [this] at h2
  have : |η (u / 4)| ≤ u * |η (u / 4)| := le_mul_of_one_le_left (abs_nonneg _) (by linarith)
  linarith

/-! ### M1: the third moment -/

theorem third_moment : ∃ u₀ : ℕ, ∀ u : ℕ, u₀ ≤ u → ∃ B : ℝ, 0 < B ∧
    ∀ᶠ q : ℕ in atTop, avg q (fun a => (Wc q u a : ℝ) ^ 3) ≤ B := by
  obtain ⟨η, hη, u₁, hdim1⟩ := sieve_dim1
  obtain ⟨u₂, htrip⟩ := sieve_triple
  obtain ⟨C₃, hC₃⟩ := lemma3
  obtain ⟨CM, hCM, hA⟩ := Aq_le
  obtain ⟨u₃, hu₃⟩ := eta_small η hη 1 one_pos
  refine ⟨max (max u₁ u₂) (max u₃ 1), fun u hu => ?_⟩
  have hu1 : u₁ ≤ u := by omega
  have hu2 : u₂ ≤ u := by omega
  have hu3 : u₃ ≤ u := by omega
  have hu1' : 1 ≤ u := by omega
  set C := max C₃ 0 with hC
  set B := 24 * (8 * C * (CM * u) ^ 3 + 1) + 4 * (2 * (CM * u) + 1) with hB
  have hηu := (hu₃ u hu3).1
  refine ⟨B, by positivity, ?_⟩
  have hQz := (Qz_ratio u hu1').eventually_lt_const (show (1 : ℝ) < 2 by norm_num)
  have hK2 : ∀ᶠ q : ℕ in atTop, (Kq q : ℝ) ^ 2 * xq q ^ ((1 : ℝ) / 3) ≤ q.totient := by
    filter_upwards [ev_small (1 / 3) 3 1 (by norm_num) one_pos, ev_phi_ge,
      eventually_ge_atTop 3] with q h1 h2 h3
    have hl : 0 ≤ Real.log q := Real.log_natCast_nonneg q
    have hK := Kq_le_log q (by omega)
    have hK0 : (0 : ℝ) ≤ Kq q := Nat.cast_nonneg _
    calc (Kq q : ℝ) ^ 2 * xq q ^ ((1 : ℝ) / 3)
        ≤ Real.log q ^ 2 * ((q : ℝ) * Real.log q) ^ ((1 : ℝ) / 3) := by
          apply mul_le_mul (pow_le_pow_left₀ hK0 hK 2)
            (Real.rpow_le_rpow (xq_nonneg q) (xq_le_qlog q) (by norm_num))
            (Real.rpow_nonneg (xq_nonneg q) _) (by positivity)
      _ ≤ ((q : ℝ) * Real.log q) ^ ((1 : ℝ) / 3) * Real.log q ^ (3 : ℝ) := by
          have hl1 : 1 ≤ Real.log q := by
            rw [Real.le_log_iff_exp_le (by positivity)]
            have : Real.exp 1 < 3 := by
              have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
            have h3' : (3 : ℝ) ≤ q := by exact_mod_cast h3
            linarith
          rw [mul_comm]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          exact pow_le_pow_right₀ hl1 (by norm_num)
      _ ≤ 1 * (q / Real.log q) := h1
      _ ≤ q.totient := by linarith
  have hx4 := ev_xpow_small (1 / 4) 1 (by norm_num) (by norm_num) one_pos
  filter_upwards [(hdim1 u hu1).1, htrip u hu2, hQz, hA u hu1', hK2, hx4,
    eventually_ge_atTop 2] with q hW1 htr hQz hAq hK2 hx4 hq2
  have hq0 : 0 < q := by omega
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq0
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
  set x := xq q
  set z := zq q u
  set K := Kq q
  set A := Aq q u
  have hx0 : 0 ≤ x := xq_nonneg q
  have hV0 : 0 ≤ V z := V_nonneg z
  have hA0 : 0 ≤ A := Aq_nonneg q u
  have hA' : A * q.totient = x * V z := by
    show Aq q u * q.totient = xq q * V (zq q u)
    unfold Aq; field_simp
  -- Step 1: cube ≤ 24 C(W,3) + 4 W, summed
  have hstep1 : ∑ a ∈ reduced q, (Wc q u a : ℝ) ^ 3
      ≤ 24 * (∑ a ∈ reduced q, ((Wc q u a).choose 3 : ℝ)) + 4 * ∑ a ∈ reduced q, (Wc q u a : ℝ) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_le_sum (fun a _ => cube_le_choose _)
  -- Step 2: triples
  have hstep2 : (∑ a ∈ reduced q, ((Wc q u a).choose 3 : ℝ))
      ≤ ∑ k ∈ Icc 1 K, ∑ h ∈ Ico 1 k, (Qtrip q u (h * q) (k * q) : ℝ) := by
    exact_mod_cast sum_choose_three_le q u hq0
  have hstep3 : ∑ k ∈ Icc 1 K, ∑ h ∈ Ico 1 k, (Qtrip q u (h * q) (k * q) : ℝ)
      ≤ 2 * x * V z ^ 3 * (C * Qz q z ^ 2 * (K : ℝ) ^ 2) + (K : ℝ) ^ 2 * x ^ ((1 : ℝ) / 3) := by
    have hpt : ∀ k ∈ Icc 1 K, ∀ h ∈ Ico 1 k, (Qtrip q u (h * q) (k * q) : ℝ)
        ≤ 2 * x * V z ^ 3 * S3 z (h * q) (k * q) + x ^ ((1 : ℝ) / 3) := by
      intro k hk h hh
      exact htr h k (mem_Ico.1 hh).1 (mem_Ico.1 hh).2 (mem_Icc.1 hk).2
    have hs1 := sum_le_sum (fun k hk => sum_le_sum (fun h hh => hpt k hk h hh))
    refine hs1.trans ?_
    simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
    have hS3 : ∑ k ∈ Icc 1 K, ∑ h ∈ Ico 1 k, S3 z (h * q) (k * q) ≤ C * Qz q z ^ 2 * (K : ℝ) ^ 2 :=
      (hC₃ q z K hq0).trans (by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (sq_nonneg _)) (sq_nonneg _))
    have hcnt : ∑ k ∈ Icc 1 K, ((Ico 1 k).card : ℝ) * x ^ ((1 : ℝ) / 3)
        ≤ (K : ℝ) ^ 2 * x ^ ((1 : ℝ) / 3) := by
      rw [← sum_mul]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx0 _)
      have : ∀ k ∈ Icc 1 K, ((Ico 1 k).card : ℝ) ≤ K := by
        intro k hk; simp only [Nat.card_Ico]
        exact_mod_cast (show k - 1 ≤ K by have := (mem_Icc.1 hk).2; omega)
      refine (sum_le_sum this).trans ?_
      simp [sq]
    have h2x : 0 ≤ 2 * x * V z ^ 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hS3 h2x]
  -- Step 4: normalize
  have hQz' : Qz q z ≤ 2 * q / q.totient := by
    rw [le_div_iff₀ hφ]; have := hQz; rw [div_lt_iff₀ hqr] at this; linarith
  have hQz0 : 0 ≤ Qz q z := by
    unfold Qz; apply Finset.prod_nonneg; intro p hp
    simp only [primesLT, mem_filter] at hp
    have : (1 : ℝ) < p := by exact_mod_cast hp.1.2.1.one_lt
    exact div_nonneg (by linarith) (by linarith)
  have hKx : (K : ℝ) ≤ x / q := by rw [le_div_iff₀ hqr]; linarith [q_mul_Kq_le q hq0]
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hmain : x * V z ^ 3 * (Qz q z ^ 2 * (K : ℝ) ^ 2) ≤ 4 * A ^ 3 * q.totient := by
    have h1 : Qz q z ^ 2 * (K : ℝ) ^ 2 ≤ (2 * q / q.totient) ^ 2 * (x / q) ^ 2 :=
      mul_le_mul (pow_le_pow_left₀ hQz0 hQz' 2) (pow_le_pow_left₀ hK0 hKx 2) (by positivity)
        (by positivity)
    have h2 : (2 * q / q.totient : ℝ) ^ 2 * (x / q) ^ 2 = 4 * x ^ 2 / (q.totient : ℝ) ^ 2 := by
      field_simp; ring
    calc x * V z ^ 3 * (Qz q z ^ 2 * (K : ℝ) ^ 2)
        ≤ x * V z ^ 3 * (4 * x ^ 2 / (q.totient : ℝ) ^ 2) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 * (x * V z) ^ 3 / (q.totient : ℝ) ^ 2 := by ring
      _ = 4 * A ^ 3 * q.totient := by rw [← hA']; field_simp
  have hA3 : A ^ 3 ≤ (CM * u) ^ 3 := pow_le_pow_left₀ hA0 hAq 3
  have hW1' : ∑ a ∈ reduced q, (Wc q u a : ℝ) ≤ 2 * A * q.totient + 1 * q.totient := by
    have hη1 : 1 + η (u / 4) ≤ 2 := by linarith [le_abs_self (η (u / 4))]
    have : (1 + η (u / 4)) * x * V z ≤ 2 * (x * V z) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hη1 (by positivity)
    rw [mul_assoc 2 A, hA']; linarith
  unfold avg
  rw [div_le_iff₀ hφ]
  have hCnn : 0 ≤ C := le_max_right _ _
  have hT := hstep2.trans hstep3
  have e1 : 2 * x * V z ^ 3 * (C * Qz q z ^ 2 * (K : ℝ) ^ 2)
      = 2 * C * (x * V z ^ 3 * (Qz q z ^ 2 * (K : ℝ) ^ 2)) := by ring
  have t1 : 2 * C * (x * V z ^ 3 * (Qz q z ^ 2 * (K : ℝ) ^ 2)) ≤ 2 * C * (4 * A ^ 3 * q.totient) :=
    mul_le_mul_of_nonneg_left hmain (by positivity)
  have t2 : 2 * C * (4 * A ^ 3 * q.totient) ≤ 2 * C * (4 * (CM * u) ^ 3 * q.totient) :=
    mul_le_mul_of_nonneg_left (by gcongr) (by positivity)
  have t3 : 2 * A * q.totient ≤ 2 * (CM * u) * q.totient := by gcongr
  have e2 : B * q.totient = 24 * (2 * C * (4 * (CM * u) ^ 3 * q.totient) + q.totient)
      + 4 * (2 * (CM * u) * q.totient + q.totient) := by rw [hB]; ring
  rw [e1] at hT
  rw [e2]
  linarith


/-! ### M3: the mixed moment -/

/-- `z/q → 0` for `u ≥ 2`. -/
lemma zq_div_q_tendsto (u : ℕ) (hu : 2 ≤ u) :
    Tendsto (fun q : ℕ => zq q u / q) atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards with q
    exact lt_of_lt_of_le ha (div_nonneg (Real.rpow_nonneg (xq_nonneg q) _) (Nat.cast_nonneg _))
  · filter_upwards [ev_small (1 / 2) 0 (a / 2) (by norm_num) (by positivity), q_le_xq,
      eventually_ge_atTop 3] with q h1 h2 h3
    have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast h3
    have hq0 : (0 : ℝ) < q := by linarith
    have hl : 1 ≤ Real.log q := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have : Real.exp 1 < 3 := by
        have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
      linarith
    have hx1 : 1 ≤ xq q := by linarith
    rw [Real.rpow_zero, mul_one] at h1
    have hz : zq q u ≤ xq q ^ ((1 : ℝ) / 2) := by
      unfold zq
      apply Real.rpow_le_rpow_of_exponent_le hx1
      have : (2 : ℝ) ≤ u := by exact_mod_cast hu
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have hz2 : xq q ^ ((1 : ℝ) / 2) ≤ ((q : ℝ) * Real.log q) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (xq_nonneg q) (xq_le_qlog q) (by norm_num)
    rw [div_lt_iff₀ hq0]
    have : a / 2 * (q / Real.log q) ≤ a / 2 * q := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [div_le_iff₀ (by linarith)]; nlinarith
    nlinarith

/-- `ω(q) log 2 ≤ log q`. -/
lemma omega_le (q : ℕ) (hq : q ≠ 0) : (q.primeFactors.card : ℝ) ≤ Real.log q / Real.log 2 := by
  rw [le_div_iff₀ (Real.log_pos (by norm_num))]
  exact card_mul_log_le hq (by norm_num) q.primeFactors (subset_refl _)
    (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le)

/-- Pointwise lower bound for `X₊ + X₋` (via `Li_sub_ge`). -/
lemma X_lower (q u h : ℕ) (hq0 : 0 < q) (hz2 : 2 ≤ zq q u) (hzq : zq q u < q)
    (hlx : 0 < Real.log (xq q)) (hh : h ∈ Ico 1 (Kq q)) :
    ((Kq q : ℝ) - h) * ((2 * q - zq q u) / Real.log (xq q))
      ≤ (Li (xq q - h * q) - Li (zq q u)) + (Li (xq q) - Li (h * q)) := by
  set x := xq q
  set z := zq q u
  set K := Kq q
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
  have h1 : (1 : ℝ) ≤ h := by exact_mod_cast (mem_Ico.1 hh).1
  have hhK : (h : ℝ) + 1 ≤ K := by exact_mod_cast (mem_Ico.1 hh).2
  have hqK : (q : ℝ) * K ≤ x := q_mul_Kq_le q hq0
  have hq2 : (2 : ℝ) < q := by linarith
  have hxh : (q : ℝ) * (K - h) ≤ x - h * q := by nlinarith
  have hxh2 : (q : ℝ) ≤ x - h * q := by nlinarith
  have hhq2 : (2 : ℝ) ≤ h * q := by nlinarith
  have hhqx : (h : ℝ) * q ≤ x := by nlinarith
  have a1 := Li_sub_ge hz2 (show z ≤ x - h * q by linarith)
  have a2 := Li_sub_ge hhq2 hhqx
  have hlog1 : Real.log (x - h * q) ≤ Real.log x := Real.log_le_log (by linarith) (by linarith)
  have hlog0 : 0 < Real.log (x - h * q) := Real.log_pos (by linarith)
  have b1 : (x - h * q - z) / Real.log x ≤ (x - h * q - z) / Real.log (x - h * q) :=
    div_le_div_of_nonneg_left (by linarith) hlog0 hlog1
  have c1 : ((K : ℝ) - h) * ((2 * q - z) / Real.log x)
      ≤ (x - h * q - z) / Real.log x + (x - h * q) / Real.log x := by
    rw [← add_div, mul_div_assoc', div_le_div_iff_of_pos_right hlx]
    nlinarith
  linarith

/-- `|π(y) - Li y| ≤ ε y / log y` for large `y` (PNT + `Li y ∼ y/log y`). -/
lemma pi_Li_close (ε : ℝ) (hε : 0 < ε) :
    ∃ Y : ℝ, 2 ≤ Y ∧ ∀ y : ℝ, Y ≤ y →
      |(Nat.primeCounting ⌊y⌋₊ : ℝ) - Li y| ≤ ε * (y / Real.log y) := by
  have h := pnt.sub li_asymp
  simp only [sub_self] at h
  have hev := (h.eventually (Metric.ball_mem_nhds 0 hε)).and (eventually_ge_atTop (2 : ℝ))
  obtain ⟨Y, hY⟩ := eventually_atTop.1 hev
  refine ⟨max Y 2, le_max_right _ _, fun y hy => ?_⟩
  obtain ⟨hb, hy2⟩ := hY y (le_trans (le_max_left _ _) hy)
  simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hb
  have hy0 : 0 < y := by linarith
  have hl : 0 < Real.log y := Real.log_pos (by linarith)
  have e : (Nat.primeCounting ⌊y⌋₊ : ℝ) - Li y
      = ((Nat.primeCounting ⌊y⌋₊ : ℝ) * Real.log y / y - Li y * Real.log y / y) * (y / Real.log y) := by
    field_simp
  rw [e, abs_mul, abs_of_pos (div_pos hy0 hl)]
  exact mul_le_mul_of_nonneg_right hb.le (div_pos hy0 hl).le

/-- Pointwise lower bound for the prime-counting main terms. -/
lemma X_lower_pi (q u h : ℕ) (hq0 : 0 < q) (hz2 : 2 ≤ zq q u) (hzq : zq q u < q)
    (hlx : 0 < Real.log (xq q)) (hh : h ∈ Ico 1 (Kq q)) (ε Y : ℝ)
    (hY : ∀ y : ℝ, Y ≤ y → |(Nat.primeCounting ⌊y⌋₊ : ℝ) - Li y| ≤ ε * (y / Real.log y))
    (hzY : Y ≤ zq q u) (hε : 0 ≤ ε) :
    ((Kq q : ℝ) - h) * ((2 * q - zq q u) / Real.log (xq q)) - 4 * ε * (xq q / Real.log (zq q u))
      ≤ ((Nat.primeCounting ⌊xq q - h * q⌋₊ : ℝ) - Nat.primeCounting ⌊zq q u⌋₊)
        + ((Nat.primeCounting ⌊xq q⌋₊ : ℝ) - Nat.primeCounting (h * q)) := by
  have hL := X_lower q u h hq0 hz2 hzq hlx hh
  set x := xq q
  set z := zq q u
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
  have h1 : (1 : ℝ) ≤ h := by exact_mod_cast (mem_Ico.1 hh).1
  have hhK : (h : ℝ) + 1 ≤ Kq q := by exact_mod_cast (mem_Ico.1 hh).2
  have hqK : (q : ℝ) * Kq q ≤ x := q_mul_Kq_le q hq0
  have hxh2 : (q : ℝ) ≤ x - h * q := by nlinarith
  have hhq : (q : ℝ) ≤ h * q := by nlinarith
  have hhqx : (h : ℝ) * q ≤ x := by nlinarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have bnd : ∀ y : ℝ, z ≤ y → y ≤ x →
      |(Nat.primeCounting ⌊y⌋₊ : ℝ) - Li y| ≤ ε * (x / Real.log z) := by
    intro y hzy hyx
    refine (hY y (le_trans hzY hzy)).trans (mul_le_mul_of_nonneg_left ?_ hε)
    have hly : Real.log z ≤ Real.log y := Real.log_le_log (by linarith) hzy
    exact div_le_div₀ (by linarith) hyx hlz hly
  have b1 := bnd (x - h * q) (by linarith) (by linarith)
  have b2 := bnd z le_rfl (by linarith)
  have b3 := bnd x (by linarith) le_rfl
  have b4 := bnd (h * q) (by linarith) hhqx
  have hfl : (Nat.primeCounting (h * q) : ℝ) = Nat.primeCounting ⌊(h : ℝ) * q⌋₊ := by
    rw [show (h : ℝ) * q = ((h * q : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  rw [hfl]
  have a1 := neg_abs_le ((Nat.primeCounting ⌊x - h * q⌋₊ : ℝ) - Li (x - h * q))
  have a2 := le_abs_self ((Nat.primeCounting ⌊z⌋₊ : ℝ) - Li z)
  have a3 := neg_abs_le ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x)
  have a4 := le_abs_self ((Nat.primeCounting ⌊(h : ℝ) * q⌋₊ : ℝ) - Li (h * q))
  linarith

/-- The main-term identity `V · (2q−z)/log x · (1−δ) Qz K²/2 = A φ ρ`. -/
lemma main_identity (q u : ℕ) (d : ℝ) (hq0 : 0 < q) (hx0 : 0 < xq q) :
    V (zq q u) * ((2 * q - zq q u) / Real.log (xq q) * (d * Qz q (zq q u) * (Kq q : ℝ) ^ 2 / 2))
      = Aq q u * q.totient * ((1 - zq q u / (2 * q)) * d
        * (Qz q (zq q u) * q.totient / q) * ((q : ℝ) * Kq q / xq q) ^ 2
        * (Real.log q / Real.log (xq q))) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq0
  have hlq : Real.log q = xq q / q.totient := by unfold xq; field_simp
  unfold Aq
  rw [hlq]
  field_simp

/-- Final linear arithmetic of M3. -/
lemma mixed_final (SNW SW SN SM MT P φ e ε E1 E2 E3 : ℝ)
    (h1 : SN + SM - E1 ≤ SNW) (h2 : MT - E2 ≤ SM) (h3 : SW ≤ (1 + e) * P + E3)
    (h4 : 15 / 16 * φ ≤ SN) (h5 : E1 ≤ 1 / 32 * φ) (h6 : E2 ≤ 1 / 32 * φ) (h7 : E3 ≤ 1 / 32 * φ)
    (k1 : e * P ≤ 1 / 16 * φ) (k2 : ε * (1 - e) * P ≤ 1 / 16 * φ)
    (k3 : (1 - e) * P * (1 - ε) ≤ MT) (hφ : 0 ≤ φ) :
    1 / 2 * φ ≤ SNW - SW := by
  nlinarith

set_option maxHeartbeats 2000000 in
theorem mixed_moment : ∃ u₀ : ℕ, ∀ u : ℕ, u₀ ≤ u →
    ∀ᶠ q : ℕ in atTop, (1 : ℝ) / 2 ≤ avg q (fun a => ((Nc q u a : ℝ) - 1) * Wc q u a) := by
  obtain ⟨η, hη, u₁, hdim1⟩ := sieve_dim1
  obtain ⟨δ, hδ, hL2⟩ := lemma2_finite
  obtain ⟨CM, hCM, hA⟩ := Aq_le
  obtain ⟨C₂, hC₂⟩ := sum_S2_le
  obtain ⟨u₃, hu₃⟩ := eta_small η hη (min (1 / 2) (1 / (16 * CM))) (by positivity)
  refine ⟨max (max u₁ u₃) 4, fun u hu => ?_⟩
  have hu1 : u₁ ≤ u := by omega
  have hu3 : u₃ ≤ u := by omega
  have hu4 : 4 ≤ u := by omega
  have hur : (4 : ℝ) ≤ u := by exact_mod_cast hu4
  obtain ⟨hηa, hηb⟩ := hu₃ u hu3
  have hηh : |η (u / 4)| ≤ 1 / 2 := hηa.trans (min_le_left _ _)
  have hηu : |(u : ℝ) * η (u / 4)| ≤ 1 / (16 * CM) := hηb.trans (min_le_right _ _)
  set e := η (u / 4) with he
  set ε1 : ℝ := 1 / (24 * CM * u) with hε1
  have hε1p : 0 < ε1 := by positivity
  have hη0 : 0 ≤ 1 - e := by linarith [le_abs_self e]
  set C₂' := max C₂ 0 with hC₂'
  have hC₂'0 : 0 ≤ C₂' := le_max_right _ _
  set ε : ℝ := ε1 / (16 * (C₂' + 1) * u) with hεdef
  have hεp : 0 < ε := by positivity
  obtain ⟨Y, hY2, hY⟩ := pi_Li_close ε hεp
  -- ρ → 1
  have hKn : Tendsto (fun q : ℕ => Kq q) atTop atTop := tendsto_natCast_atTop_iff.1 Kq_tendsto
  have hf1 : Tendsto (fun q : ℕ => 1 - zq q u / (2 * q)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub ((zq_div_q_tendsto u (by omega)).div_const 2)
    simp only [zero_div, sub_zero] at h
    refine h.congr (fun q => ?_); rw [div_div, mul_comm (q : ℝ) 2]
  have hf2 : Tendsto (fun q : ℕ => 1 - δ (Kq q)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hδ.comp hKn)
  have hf4 : Tendsto (fun q : ℕ => (q : ℝ) * Kq q / xq q) atTop (𝓝 1) := by
    have hinv : Tendsto (fun q : ℕ => (q : ℝ) / xq q) atTop (𝓝 0) := by
      refine xq_div_tendsto.inv_tendsto_atTop.congr' ?_
      filter_upwards with q
      simp [inv_div]
    have hlow : Tendsto (fun q : ℕ => 1 - (q : ℝ) / xq q) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [xq_pos, eventually_gt_atTop 0] with q hx hq
      have hq' : (0 : ℝ) < q := by exact_mod_cast hq
      rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hx]
      unfold Kq
      have := Nat.lt_floor_add_one (xq q / q)
      rw [div_lt_iff₀ hq'] at this
      nlinarith
    · filter_upwards [xq_pos, eventually_gt_atTop 0] with q hx hq
      rw [div_le_one hx]; exact q_mul_Kq_le q hq
  have hρlim : Tendsto (fun q : ℕ => (1 - zq q u / (2 * q)) * (1 - δ (Kq q))
      * (Qz q (zq q u) * q.totient / q) * ((q : ℝ) * Kq q / xq q) ^ 2
      * (Real.log q / Real.log (xq q))) atTop (𝓝 1) := by
    simpa using (((hf1.mul hf2).mul (Qz_ratio u (by omega))).mul (hf4.pow 2)).mul log_ratio
  have hρ := hρlim.eventually_const_lt (show 1 - ε1 / 2 < 1 by linarith)
  have hEN := (avgN_tendsto u (by omega)).eventually_const_lt (show (15 : ℝ) / 16 < 1 by norm_num)
  have hz2 := (zq_tendsto u (by omega)).eventually_ge_atTop (max 2 Y)
  have hzq := (zq_div_q_tendsto u (by omega)).eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num)
  have hQz2 := (Qz_ratio u (by omega)).eventually_lt_const (show (1 : ℝ) < 2 by norm_num)
  have hlogx : ∀ᶠ q : ℕ in atTop, (32 : ℝ) ≤ Real.log (xq q) :=
    (Real.tendsto_log_atTop.comp xq_tendsto).eventually_ge_atTop 32
  have herr1 : ∀ᶠ q : ℕ in atTop,
      2 * (Kq q : ℝ) * q.primeFactors.card ≤ 1 / 32 * q.totient := by
    filter_upwards [ev_small 0 2 (1 / 128) (by norm_num) (by norm_num), ev_phi_ge,
      eventually_ge_atTop 3] with q h1 h2 h3
    have hq0 : q ≠ 0 := by omega
    have hK := Kq_le_log q (by omega)
    have hω := omega_le q hq0
    have hl0 : 0 ≤ Real.log q := Real.log_natCast_nonneg q
    have hl2 : Real.log 2 > 1 / 2 := by have := Real.log_two_gt_d9; linarith
    rw [Real.rpow_zero, one_mul, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast] at h1
    have hω' : (q.primeFactors.card : ℝ) ≤ 2 * Real.log q := by
      refine hω.trans ?_
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have hK0 : (0 : ℝ) ≤ Kq q := Nat.cast_nonneg _
    have hω0 : (0 : ℝ) ≤ q.primeFactors.card := Nat.cast_nonneg _
    have := mul_le_mul hK hω' hω0 hl0
    have : 2 * (Kq q : ℝ) * q.primeFactors.card ≤ 4 * Real.log q ^ 2 := by nlinarith
    linarith
  have herr3 := ev_xpow_small (1 / 4) (1 / 32) (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [(hdim1 u hu1).1, (hdim1 u hu1).2, hρ, hEN, hz2, hzq, hQz2, hlogx, herr1, herr3,
    hA u (by omega), q_le_xq, eventually_ge_atTop 2]
    with q hW1 hM hρq hENq hz2q hzqq hQz2q hlogq herr1q herr3q hAq hqx hq2
  have hq0 : 0 < q := by omega
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq0
  have hlx : 0 < Real.log (xq q) := by linarith
  have hx0 : 0 < xq q := by linarith
  have hzq' : zq q u < q := by
    have := hzqq; rw [div_lt_iff₀ hqr] at this; linarith
  have hz2' : 2 ≤ zq q u := le_trans (le_max_left _ _) hz2q
  have hzY : Y ≤ zq q u := le_trans (le_max_right _ _) hz2q
  have hA0 : 0 ≤ Aq q u := Aq_nonneg q u
  have hAφ : Aq q u * q.totient = xq q * V (zq q u) := by unfold Aq; field_simp
  have hMC := mixed_count q u hq0 hzq'
  have hV0 : 0 ≤ V (zq q u) := V_nonneg _
  have hQz0 : 0 ≤ Qz q (zq q u) := by
    unfold Qz; apply Finset.prod_nonneg; intro p hp
    simp only [primesLT, mem_filter] at hp
    have : (1 : ℝ) < p := by exact_mod_cast hp.1.2.1.one_lt
    exact div_nonneg (by linarith) (by linarith)
  set x := xq q with hx
  set z := zq q u with hz
  set K := Kq q with hK
  set ρq := (1 - z / (2 * q)) * (1 - δ K) * (Qz q z * q.totient / q) * ((q : ℝ) * K / x) ^ 2
      * (Real.log q / Real.log x) with hρq_def
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlzx : Real.log z = Real.log x / u := log_zq hx0
  -- sum of the π-main terms
  have hsum : ((2 * q - z) / Real.log x) * ∑ h ∈ Ico 1 K, ((K : ℝ) - h) * S2 z (h * q)
      - 4 * ε * (x / Real.log z) * ∑ h ∈ Ico 1 K, S2 z (h * q)
      ≤ ∑ h ∈ Ico 1 K, S2 z (h * q) *
          (((Nat.primeCounting ⌊x - h * q⌋₊ : ℝ) - Nat.primeCounting ⌊z⌋₊)
            + ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Nat.primeCounting (h * q))) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_le_sum
    intro h hh
    have := mul_le_mul_of_nonneg_left
      (X_lower_pi q u h hq0 hz2' hzq' hlx hh ε Y hY hzY hεp.le) (S2_nonneg z (h * q))
    nlinarith [this]
  have hL := hL2 q z K hq0
  have hc0 : 0 ≤ (2 * q - z) / Real.log x := div_nonneg (by linarith) hlx.le
  have hS2sum : ∑ h ∈ Ico 1 K, S2 z (h * q) ≤ C₂' * Qz q z * K :=
    (hC₂ q z K hq0).trans (by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hQz0)
        (Nat.cast_nonneg _))
  have hQzK : Qz q z * K ≤ 2 * Real.log x := by
    have hQ : Qz q z ≤ 2 * q / q.totient := by
      rw [le_div_iff₀ hφ]; have := hQz2q; rw [div_lt_iff₀ hqr] at this; linarith
    have hKx : (K : ℝ) ≤ x / q := by rw [le_div_iff₀ hqr]; linarith [q_mul_Kq_le q hq0]
    have hlq : Real.log q ≤ Real.log x := Real.log_le_log hqr hqx
    calc Qz q z * K ≤ (2 * q / q.totient) * (x / q) :=
          mul_le_mul hQ hKx (Nat.cast_nonneg _) (by positivity)
      _ = 2 * Real.log q := by rw [hx]; unfold xq; field_simp
      _ ≤ 2 * Real.log x := by linarith
  -- error term ≤ (1-e) A φ ε1/2
  have herrM : (1 - e) * V z * (4 * ε * (x / Real.log z) * ∑ h ∈ Ico 1 K, S2 z (h * q))
      ≤ (1 - e) * (Aq q u * q.totient) * (ε1 / 2) := by
    have h1 : 4 * ε * (x / Real.log z) * ∑ h ∈ Ico 1 K, S2 z (h * q)
        ≤ 4 * ε * (x / Real.log z) * (C₂' * (2 * Real.log x)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc ∑ h ∈ Ico 1 K, S2 z (h * q) ≤ C₂' * Qz q z * K := hS2sum
        _ = C₂' * (Qz q z * K) := by ring
        _ ≤ C₂' * (2 * Real.log x) := mul_le_mul_of_nonneg_left hQzK hC₂'0
    have h2 : 4 * ε * (x / Real.log z) * (C₂' * (2 * Real.log x)) = 8 * ε * C₂' * u * x := by
      rw [hlzx]; field_simp; ring
    have h3 : 8 * ε * C₂' * u ≤ ε1 / 2 := by
      rw [hεdef]
      have hu0 : (0 : ℝ) < u := by linarith
      rw [show 8 * (ε1 / (16 * (C₂' + 1) * u)) * C₂' * u = ε1 / 2 * (C₂' / (C₂' + 1)) by
        field_simp; ring]
      have : C₂' / (C₂' + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      nlinarith
    have h4 : V z * (4 * ε * (x / Real.log z) * ∑ h ∈ Ico 1 K, S2 z (h * q))
        ≤ Aq q u * q.totient * (ε1 / 2) := by
      calc V z * (4 * ε * (x / Real.log z) * ∑ h ∈ Ico 1 K, S2 z (h * q))
          ≤ V z * (8 * ε * C₂' * u * x) := by rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hV0
        _ = (8 * ε * C₂' * u) * (x * V z) := by ring
        _ ≤ (ε1 / 2) * (x * V z) := mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = Aq q u * q.totient * (ε1 / 2) := by rw [hAφ]; ring
    calc (1 - e) * V z * (4 * ε * (x / Real.log z) * ∑ h ∈ Ico 1 K, S2 z (h * q))
        = (1 - e) * (V z * (4 * ε * (x / Real.log z) * ∑ h ∈ Ico 1 K, S2 z (h * q))) := by ring
      _ ≤ (1 - e) * (Aq q u * q.totient * (ε1 / 2)) := mul_le_mul_of_nonneg_left h4 hη0
      _ = _ := by ring
  have hmainM : (1 - e) * (Aq q u * q.totient) * ρq
      - (1 - e) * V z * (4 * ε * (x / Real.log z) * ∑ h ∈ Ico 1 K, S2 z (h * q))
      ≤ (1 - e) * V z * ∑ h ∈ Ico 1 K, S2 z (h * q) *
          (((Nat.primeCounting ⌊x - h * q⌋₊ : ℝ) - Nat.primeCounting ⌊z⌋₊)
            + ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Nat.primeCounting (h * q))) := by
    have hid := main_identity q u (1 - δ K) hq0 hx0
    have hA1 : (2 * q - z) / Real.log x * ((1 - δ K) * Qz q z * (K : ℝ) ^ 2 / 2)
        ≤ ((2 * q - z) / Real.log x) * ∑ h ∈ Ico 1 K, ((K : ℝ) - h) * S2 z (h * q) :=
      mul_le_mul_of_nonneg_left hL hc0
    have hB := mul_le_mul_of_nonneg_left (hA1.trans (by linarith [hsum] :
      ((2 * q - z) / Real.log x) * ∑ h ∈ Ico 1 K, ((K : ℝ) - h) * S2 z (h * q)
        ≤ ∑ h ∈ Ico 1 K, S2 z (h * q) *
          (((Nat.primeCounting ⌊x - h * q⌋₊ : ℝ) - Nat.primeCounting ⌊z⌋₊)
            + ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Nat.primeCounting (h * q)))
          + 4 * ε * (x / Real.log z) * ∑ h ∈ Ico 1 K, S2 z (h * q)))
      (mul_nonneg hη0 hV0)
    have : (1 - e) * V z * ((2 * q - z) / Real.log x * ((1 - δ K) * Qz q z * (K : ℝ) ^ 2 / 2))
        = (1 - e) * (Aq q u * q.totient) * ρq := by
      rw [mul_assoc, hid, hρq_def]; ring
    rw [this] at hB
    linarith
  unfold avg
  rw [le_div_iff₀ hφ]
  have hsplit : ∑ a ∈ reduced q, ((Nc q u a : ℝ) - 1) * Wc q u a
      = ∑ a ∈ reduced q, (Nc q u a : ℝ) * Wc q u a - ∑ a ∈ reduced q, (Wc q u a : ℝ) := by
    rw [← sum_sub_distrib]; exact sum_congr rfl (fun a _ => by ring)
  rw [hsplit]
  have hENq' : 15 / 16 * (q.totient : ℝ) ≤ ∑ a ∈ reduced q, (Nc q u a : ℝ) := by
    have := hENq; unfold avg at this; rw [lt_div_iff₀ hφ] at this; linarith
  have hW1' : ∑ a ∈ reduced q, (Wc q u a : ℝ)
      ≤ (1 + e) * (Aq q u * q.totient) + x ^ ((1 : ℝ) / 4) := by
    rw [hAφ]; linarith [show (1 + e) * x * V z = (1 + e) * (x * V z) by ring]
  have herr2 : x / Real.log x ^ 2 ≤ 1 / 32 * q.totient := by
    have hlqx : Real.log q ≤ Real.log x := Real.log_le_log hqr hqx
    have hlq0 : 0 ≤ Real.log q := Real.log_natCast_nonneg q
    rw [div_le_iff₀ (by positivity)]
    have hxe : x = q.totient * Real.log q := rfl
    have h32 : (32 : ℝ) * Real.log q ≤ Real.log x ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left h32 hφ.le
    nlinarith
  have hP : 0 ≤ Aq q u * q.totient := mul_nonneg hA0 hφ.le
  have k1 : e * (Aq q u * q.totient) ≤ 1 / 16 * q.totient := by
    have hb : |e| * Aq q u ≤ 1 / 16 := by
      have h1 : |e| * Aq q u ≤ |e| * (CM * u) := mul_le_mul_of_nonneg_left hAq (abs_nonneg _)
      have h2 : |e| * (CM * u) = CM * |(u : ℝ) * e| := by
        rw [abs_mul, Nat.abs_cast]; ring
      have h3 : CM * |(u : ℝ) * e| ≤ CM * (1 / (16 * CM)) := mul_le_mul_of_nonneg_left hηu hCM.le
      have h4 : CM * (1 / (16 * CM)) = 1 / 16 := by field_simp
      linarith
    have hb' : e * Aq q u ≤ 1 / 16 := (mul_le_mul_of_nonneg_right (le_abs_self e) hA0).trans hb
    have := mul_le_mul_of_nonneg_right hb' hφ.le
    linarith [show e * (Aq q u * q.totient) = e * Aq q u * q.totient by ring]
  have k2 : ε1 * (1 - e) * (Aq q u * q.totient) ≤ 1 / 16 * q.totient := by
    have h1 : ε1 * Aq q u ≤ 1 / 24 := by
      have : ε1 * Aq q u ≤ ε1 * (CM * u) := mul_le_mul_of_nonneg_left hAq hε1p.le
      have h2 : ε1 * (CM * u) = 1 / 24 := by rw [hε1]; field_simp
      linarith
    have h2 : 1 - e ≤ 3 / 2 := by linarith [neg_abs_le e]
    have h3 : (1 - e) * (ε1 * Aq q u) ≤ 3 / 2 * (1 / 24) :=
      mul_le_mul h2 h1 (by positivity) (by norm_num)
    have := mul_le_mul_of_nonneg_right h3 hφ.le
    linarith [show ε1 * (1 - e) * (Aq q u * q.totient) = (1 - e) * (ε1 * Aq q u) * q.totient by ring]
  have k3 : (1 - e) * (Aq q u * q.totient) * (1 - ε1)
      ≤ (1 - e) * V z * ∑ h ∈ Ico 1 K, S2 z (h * q) *
          (((Nat.primeCounting ⌊x - h * q⌋₊ : ℝ) - Nat.primeCounting ⌊z⌋₊)
            + ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Nat.primeCounting (h * q))) := by
    have hρ' : 1 - ε1 / 2 ≤ ρq := hρq.le
    have := mul_le_mul_of_nonneg_left hρ' (mul_nonneg hη0 hP)
    have hx' : (1 - e) * (Aq q u * q.totient) * (1 - ε1)
        = (1 - e) * (Aq q u * q.totient) * (1 - ε1 / 2) - (1 - e) * (Aq q u * q.totient) * (ε1 / 2) := by
      ring
    linarith [hmainM, herrM]
  exact mixed_final (∑ a ∈ reduced q, (Nc q u a : ℝ) * Wc q u a) (∑ a ∈ reduced q, (Wc q u a : ℝ))
    (∑ a ∈ reduced q, (Nc q u a : ℝ)) (∑ h ∈ Ico 1 K, ((Mplus q u h : ℝ) + Mminus q u h))
    ((1 - e) * V z * ∑ h ∈ Ico 1 K, S2 z (h * q) *
          (((Nat.primeCounting ⌊x - h * q⌋₊ : ℝ) - Nat.primeCounting ⌊z⌋₊)
            + ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Nat.primeCounting (h * q))))
    (Aq q u * q.totient) q.totient e ε1 (2 * (K : ℝ) * q.primeFactors.card)
    (x / Real.log x ^ 2) (x ^ ((1 : ℝ) / 4)) hMC hM hW1' hENq'
    herr1q herr2 herr3q k1 k2 k3 hφ.le

end Erdos971
