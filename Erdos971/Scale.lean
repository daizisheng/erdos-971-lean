import Erdos971.Defs

/-!
# Scale facts (BLUEPRINT §2). Uses `pnt`, `mertens_product`.
-/

open Real Finset Filter Topology

namespace Erdos971

/-! ### Auxiliary lemmas -/

lemma totient_real (q : ℕ) :
    (q.totient : ℝ) = q * ∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ)) := by
  have h := congrArg (fun r : ℚ => (r : ℝ)) (Nat.totient_eq_mul_prod_factors q)
  simpa [Rat.cast_prod, one_div] using h

lemma pow_card_le {q : ℕ} (hq : q ≠ 0) {w : ℝ} (hw : 0 ≤ w) (T : Finset ℕ)
    (hT : T ⊆ q.primeFactors) (hwT : ∀ p ∈ T, w ≤ p) : w ^ T.card ≤ q := by
  have h1 : (∏ p ∈ T, p) ∣ q :=
    (Finset.prod_dvd_prod_of_subset T q.primeFactors (fun p => p) hT).trans
      (Nat.prod_primeFactors_dvd q)
  have h2 : (∏ p ∈ T, p) ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) h1
  calc w ^ T.card = ∏ _p ∈ T, w := by simp
    _ ≤ ∏ p ∈ T, (p : ℝ) := Finset.prod_le_prod (fun _ _ => hw) hwT
    _ = ((∏ p ∈ T, p : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ q := by exact_mod_cast h2

lemma card_mul_log_le {q : ℕ} (hq : q ≠ 0) {w : ℝ} (hw : 0 < w) (T : Finset ℕ)
    (hT : T ⊆ q.primeFactors) (hwT : ∀ p ∈ T, w ≤ p) :
    (T.card : ℝ) * Real.log w ≤ Real.log q := by
  rw [← Real.log_pow]
  exact Real.log_le_log (pow_pos hw _) (pow_card_le hq hw.le T hT hwT)

/-- Lower bound for the product of `1 - 1/p` over prime factors `p ≥ w`. -/
lemma prod_large_ge {q : ℕ} (hq : q ≠ 0) {w : ℝ} (hw : 1 < w) (T : Finset ℕ)
    (hT : T ⊆ q.primeFactors) (hwT : ∀ p ∈ T, w ≤ p) :
    1 - Real.log q / (w * Real.log w) ≤ ∏ p ∈ T, (1 - 1 / (p : ℝ)) := by
  have hlw : 0 < Real.log w := Real.log_pos hw
  have hw0 : 0 < w := by linarith
  have hc := card_mul_log_le hq hw0 T hT hwT
  have h1w : 1 / w < 1 := (div_lt_one hw0).2 hw
  have h1w0 : 0 < 1 / w := by positivity
  have hB := one_add_mul_le_pow (a := -(1 / w)) (by linarith) T.card
  have hcard : (T.card : ℝ) ≤ Real.log q / Real.log w := (le_div_iff₀ hlw).2 hc
  have hcard' : (T.card : ℝ) / w ≤ Real.log q / (w * Real.log w) := by
    calc (T.card : ℝ) / w ≤ (Real.log q / Real.log w) / w :=
          div_le_div_of_nonneg_right hcard hw0.le
      _ = Real.log q / (w * Real.log w) := by rw [div_div, mul_comm]
  calc 1 - Real.log q / (w * Real.log w) ≤ 1 + (T.card : ℝ) * (-(1 / w)) := by
        have : (T.card : ℝ) * (-(1 / w)) = -((T.card : ℝ) / w) := by ring
        rw [this]; linarith
    _ ≤ (1 + -(1 / w)) ^ T.card := hB
    _ = ∏ _p ∈ T, (1 - 1 / w) := by simp [sub_eq_add_neg]
    _ ≤ ∏ p ∈ T, (1 - 1 / (p : ℝ)) := by
        apply Finset.prod_le_prod
        · intro _ _; linarith
        · intro p hp
          have := one_div_le_one_div_of_le hw0 (hwT p hp)
          linarith

lemma mem_primesLT {z : ℝ} {p : ℕ} : p ∈ primesLT z ↔ p.Prime ∧ (p : ℝ) < z := by
  unfold primesLT
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨h1, h2⟩; exact ⟨Nat.lt_ceil.2 h2, h1, h2⟩

/-- **S1** `q/φ(q) ≤ C log log q`. -/
theorem S1 : ∃ C : ℝ, 0 < C ∧ ∀ᶠ q : ℕ in atTop,
    (q : ℝ) ≤ C * Real.log (Real.log q) * q.totient := by
  obtain ⟨c, C0, hc, hM⟩ := mertens_product
  refine ⟨2 / c, by positivity, ?_⟩
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
    (Real.exp (Real.exp 2))] with q hq
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (Real.exp_pos _) hq
  have hqn : q ≠ 0 := by exact_mod_cast hq0.ne'
  set L := Real.log q with hL
  have hL2 : Real.exp 2 ≤ L := (Real.le_log_iff_exp_le hq0).2 hq
  have hlogL : 2 ≤ Real.log L :=
    (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) hL2)).2 hL2
  have hLgt : 2 ≤ L := le_trans (by linarith [Real.add_one_le_exp (2 : ℝ)]) hL2
  set P := q.primeFactors with hP
  have hsplit := (Finset.prod_filter_mul_prod_filter_not P (fun p : ℕ => (p : ℝ) < L)
    (fun p => 1 - 1 / (p : ℝ)))
  have hS : c / Real.log L ≤ ∏ p ∈ P.filter (fun p : ℕ => (p : ℝ) < L), (1 - 1 / (p : ℝ)) := by
    refine le_trans (hM L hLgt).1 ?_
    unfold V
    apply Finset.prod_le_prod_of_subset_of_le_one
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact mem_primesLT.2 ⟨Nat.prime_of_mem_primeFactors hp.1, hp.2⟩
    · intro p hp
      have h2 := (mem_primesLT.1 hp).1.two_le
      have : 1 / (p : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]; exact_mod_cast (by omega : 1 ≤ p)
      linarith
    · intro p hp _
      have h2 := (mem_primesLT.1 hp).1.two_le
      have : 0 ≤ 1 / (p : ℝ) := by positivity
      linarith
  have hT : 1 / 2 ≤ ∏ p ∈ P.filter (fun p : ℕ => ¬ (p : ℝ) < L), (1 - 1 / (p : ℝ)) := by
    have := prod_large_ge hqn (w := L) (by linarith) _ (Finset.filter_subset _ _)
      (fun p hp => not_lt.1 (Finset.mem_filter.1 hp).2)
    refine le_trans ?_ this
    have hL0 : 0 < L := by linarith
    have hlL0 : 0 < Real.log L := by linarith
    have : L / (L * Real.log L) = 1 / Real.log L := by field_simp
    rw [this]
    have : 1 / Real.log L ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hlogL
    linarith
  have hφ : (q : ℝ) * (c / Real.log L * (1 / 2)) ≤ q.totient := by
    rw [totient_real q, ← hsplit]
    have : 0 ≤ c / Real.log L := div_nonneg hc.le (by linarith)
    have hSnn := le_trans this hS
    gcongr
  have hlL0 : 0 < Real.log L := by linarith
  calc (q : ℝ) = (2 / c * Real.log L) * ((q : ℝ) * (c / Real.log L * (1 / 2))) := by
        field_simp
    _ ≤ 2 / c * Real.log L * q.totient := by
        gcongr

lemma tendsto_div_log : Tendsto (fun L : ℝ => L / Real.log L) atTop atTop := by
  have h0 : Tendsto (fun L : ℝ => Real.log L / L) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h1 : Tendsto (fun L : ℝ => Real.log L / L) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨h0, by
      filter_upwards [eventually_gt_atTop 1] with L hL
      exact div_pos (Real.log_pos hL) (by linarith)⟩
  simpa [Pi.inv_def, inv_div] using h1.inv_tendsto_nhdsGT_zero

lemma tendsto_log_div_self : Tendsto (fun L : ℝ => Real.log L / L) atTop (𝓝 0) := by
  simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero

lemma tendsto_logq : Tendsto (fun q : ℕ => Real.log q) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma xq_div_tendsto : Tendsto (fun q : ℕ => xq q / q) atTop atTop := by
  obtain ⟨C, hC, hS⟩ := S1
  have hlow : Tendsto (fun q : ℕ => Real.log q / Real.log (Real.log q) / C) atTop atTop :=
    (tendsto_div_log.comp tendsto_logq).atTop_div_const hC
  refine tendsto_atTop_mono' _ ?_ hlow
  filter_upwards [hS, tendsto_logq.eventually_gt_atTop 1, eventually_gt_atTop 0] with q hq hL hq0
  have hq0' : (0 : ℝ) < q := by exact_mod_cast hq0
  have hll : 0 < Real.log (Real.log q) := Real.log_pos hL
  have hlq : 0 < Real.log q := by linarith
  unfold xq
  rw [div_div, div_le_div_iff₀ (by positivity) hq0']
  calc Real.log q * q ≤ Real.log q * (C * Real.log (Real.log q) * q.totient) :=
        mul_le_mul_of_nonneg_left hq hlq.le
    _ = _ := by ring

/-- **S2** `K → ∞`. -/
theorem Kq_tendsto : Tendsto (fun q : ℕ => (Kq q : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_nat_floor_atTop.comp xq_div_tendsto)

/-- **S2** eventually `q ≤ x`. -/
theorem q_le_xq : ∀ᶠ q : ℕ in atTop, (q : ℝ) ≤ xq q := by
  filter_upwards [xq_div_tendsto.eventually_ge_atTop 1, eventually_gt_atTop 0] with q h hq
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have := (le_div_iff₀ hq').1 h
  linarith

lemma xq_tendsto : Tendsto xq atTop atTop :=
  tendsto_atTop_mono' _ q_le_xq tendsto_natCast_atTop_atTop

lemma xq_le (q : ℕ) (hq : 1 ≤ q) : xq q ≤ q * Real.log q := by
  unfold xq
  have : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  gcongr
  exact_mod_cast Nat.totient_le q

/-- Eventually `0 < log q ≤ log x`. -/
lemma log_le_log_xq : ∀ᶠ q : ℕ in atTop, 0 < Real.log q ∧ Real.log q ≤ Real.log (xq q) := by
  filter_upwards [q_le_xq, eventually_gt_atTop 1] with q h hq
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  exact ⟨Real.log_pos hq', Real.log_le_log (by linarith) h⟩

/-- **S2** `log q / log x → 1`. -/
theorem log_ratio : Tendsto (fun q : ℕ => Real.log q / Real.log (xq q)) atTop (𝓝 1) := by
  have hr : Tendsto (fun q : ℕ => Real.log (Real.log q) / Real.log q) atTop (𝓝 0) :=
    tendsto_log_div_self.comp tendsto_logq
  have hlow : Tendsto (fun q : ℕ => 1 / (1 + Real.log (Real.log q) / Real.log q)) atTop
      (𝓝 1) := by
    simpa using (tendsto_const_nhds.add hr).inv₀ (by norm_num : (1 : ℝ) + 0 ≠ 0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [log_le_log_xq, eventually_gt_atTop 1, tendsto_logq.eventually_gt_atTop 1]
      with q ⟨hl0, hl⟩ hq hL
    have hx0 : 0 < xq q := by
      unfold xq; have : 0 < q.totient := Nat.totient_pos.2 (by omega)
      positivity
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
    have hxu : Real.log (xq q) ≤ Real.log q + Real.log (Real.log q) := by
      rw [← Real.log_mul (by linarith) (by linarith)]
      exact Real.log_le_log hx0 (xq_le q hq.le)
    have hlx : 0 < Real.log (xq q) := by linarith
    have : 1 / (1 + Real.log (Real.log q) / Real.log q)
        = Real.log q / (Real.log q + Real.log (Real.log q)) := by
      field_simp
    rw [this]
    exact div_le_div_of_nonneg_left hl0.le hlx hxu
  · filter_upwards [log_le_log_xq] with q ⟨hl0, hl⟩
    exact div_le_one_of_le₀ hl (by linarith)

lemma zq_tendsto (u : ℕ) (hu : 1 ≤ u) : Tendsto (fun q : ℕ => zq q u) atTop atTop := by
  have hu' : (0 : ℝ) < 1 / u := by
    have : (0 : ℝ) < u := by exact_mod_cast hu
    positivity
  exact (tendsto_rpow_atTop hu').comp xq_tendsto

lemma log_zq {q u : ℕ} (hx : 0 < xq q) : Real.log (zq q u) = Real.log (xq q) / u := by
  unfold zq
  rw [Real.log_rpow hx]
  ring

lemma xq_pos : ∀ᶠ q : ℕ in atTop, 0 < xq q := by
  filter_upwards [q_le_xq, eventually_gt_atTop 0] with q h hq
  have : (0 : ℝ) < q := by exact_mod_cast hq
  linarith

/-- `Qz q z · φ(q)/q` is the product over prime factors `p ≥ z` of `1 - 1/p`. -/
lemma Qz_mul_eq {q : ℕ} (hq : q ≠ 0) (z : ℝ) :
    Qz q z * q.totient / q =
      ∏ p ∈ q.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) < z), (1 - 1 / (p : ℝ)) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hset : (primesLT z).filter (· ∣ q) = q.primeFactors.filter (fun p : ℕ => (p : ℝ) < z) := by
    ext p
    simp only [Finset.mem_filter, mem_primesLT, Nat.mem_primeFactors]
    tauto
  unfold Qz
  rw [hset, totient_real q, ← Finset.prod_filter_mul_prod_filter_not q.primeFactors
    (fun p : ℕ => (p : ℝ) < z)]
  have h1 : (∏ p ∈ q.primeFactors.filter (fun p : ℕ => (p : ℝ) < z), (p : ℝ) / ((p : ℝ) - 1)) *
      ∏ p ∈ q.primeFactors.filter (fun p : ℕ => (p : ℝ) < z), (1 - 1 / (p : ℝ)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).two_le
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    have : (p : ℝ) ≠ 0 := by linarith
    field_simp
  calc _ = ((∏ p ∈ q.primeFactors.filter (fun p : ℕ => (p : ℝ) < z), (p : ℝ) / ((p : ℝ) - 1)) *
      ∏ p ∈ q.primeFactors.filter (fun p : ℕ => (p : ℝ) < z), (1 - 1 / (p : ℝ))) *
      (∏ p ∈ q.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) < z), (1 - 1 / (p : ℝ))) * q / q := by
        ring
    _ = _ := by rw [h1, one_mul, mul_div_assoc, div_self hq', mul_one]

/-- `Qz q z(q) · φ(q)/q → 1` for fixed `u` (at most `u` prime factors of `q` are `≥ z`). -/
theorem Qz_ratio (u : ℕ) (hu : 1 ≤ u) :
    Tendsto (fun q : ℕ => Qz q (zq q u) * q.totient / q) atTop (𝓝 1) := by
  have hz := zq_tendsto u hu
  have hlow : Tendsto (fun q : ℕ => 1 - (u : ℝ) / zq q u) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hz)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [log_le_log_xq, hz.eventually_gt_atTop 1, eventually_gt_atTop 0, xq_pos]
      with q ⟨hl0, hl⟩ hz1 hq hx
    rw [Qz_mul_eq (by omega)]
    refine le_trans ?_ (prod_large_ge (by omega) hz1 _ (Finset.filter_subset _ _)
      (fun p hp => not_lt.1 (Finset.mem_filter.1 hp).2))
    have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
    have hz0 : 0 < zq q u := by linarith
    have hlx : 0 < Real.log (xq q) := by linarith
    rw [log_zq hx]
    have : Real.log q / (zq q u * (Real.log (xq q) / u))
        = (u / zq q u) * (Real.log q / Real.log (xq q)) := by
      field_simp
    rw [this]
    have hr : Real.log q / Real.log (xq q) ≤ 1 := div_le_one_of_le₀ hl hlx.le
    have : 0 ≤ (u : ℝ) / zq q u := by positivity
    nlinarith
  · filter_upwards [eventually_gt_atTop 0] with q hq
    rw [Qz_mul_eq (by omega)]
    apply Finset.prod_le_one
    · intro p hp
      have h2 : (2 : ℝ) ≤ p := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).two_le
      have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    · intro p hp
      have h2 : (2 : ℝ) ≤ p := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).two_le
      have : 0 ≤ 1 / (p : ℝ) := by positivity
      linarith

lemma primeCounting_eq_card (n : ℕ) :
    Nat.primeCounting n = ((Finset.range (n + 1)).filter Nat.Prime).card := by
  rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting']
  rfl

lemma primeCounting_le_succ (n : ℕ) : Nat.primeCounting n ≤ n + 1 := by
  rw [primeCounting_eq_card]
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma tendsto_log_div_sqrt :
    Tendsto (fun x : ℝ => Real.log x / x ^ ((1 : ℝ) / 2)) atTop (𝓝 0) :=
  (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero

/-- **S3** `π(z)/φ(q) → 0`. -/
theorem pi_z_small (u : ℕ) (hu : 2 ≤ u) :
    Tendsto (fun q : ℕ => (Nat.primeCounting ⌊zq q u⌋₊ : ℝ) / q.totient) atTop (𝓝 0) := by
  have hup : Tendsto (fun q : ℕ => 2 * (Real.log (xq q) / xq q ^ ((1 : ℝ) / 2))) atTop (𝓝 0) := by
    simpa using (tendsto_log_div_sqrt.comp xq_tendsto).const_mul 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards with q
    positivity
  · filter_upwards [log_le_log_xq, xq_tendsto.eventually_ge_atTop 1, eventually_gt_atTop 0]
      with q ⟨hl0, hl⟩ hx1 hq
    have hx0 : 0 < xq q := by linarith
    have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
    have hs1 : 1 ≤ xq q ^ ((1 : ℝ) / 2) := Real.one_le_rpow hx1 (by norm_num)
    have hu' : (1 : ℝ) / u ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num); exact_mod_cast hu
    have hz : zq q u ≤ xq q ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hx1 hu'
    have hz0 : 0 ≤ zq q u := by unfold zq; positivity
    have hπ : (Nat.primeCounting ⌊zq q u⌋₊ : ℝ) ≤ 2 * xq q ^ ((1 : ℝ) / 2) := by
      have h1 : (Nat.primeCounting ⌊zq q u⌋₊ : ℝ) ≤ ⌊zq q u⌋₊ + 1 := by
        exact_mod_cast primeCounting_le_succ _
      have h2 : (⌊zq q u⌋₊ : ℝ) ≤ zq q u := Nat.floor_le hz0
      linarith
    have hφx : (q.totient : ℝ) = xq q / Real.log q := by
      unfold xq; field_simp
    have hsq : xq q = xq q ^ ((1 : ℝ) / 2) * xq q ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hx0]; norm_num
    have hs0 : 0 < xq q ^ ((1 : ℝ) / 2) := by positivity
    rw [hφx, div_div_eq_mul_div]
    calc (Nat.primeCounting ⌊zq q u⌋₊ : ℝ) * Real.log q / xq q
        ≤ 2 * xq q ^ ((1 : ℝ) / 2) * Real.log (xq q) / xq q := by gcongr
      _ = 2 * xq q ^ ((1 : ℝ) / 2) * Real.log (xq q) /
            (xq q ^ ((1 : ℝ) / 2) * xq q ^ ((1 : ℝ) / 2)) := by rw [← hsq]
      _ = 2 * (Real.log (xq q) / xq q ^ ((1 : ℝ) / 2)) := by field_simp

/-- `π(⌊k x⌋)/φ(q) → k` for fixed `k ≥ 1`. -/
lemma pi_over_phi (k : ℝ) (hk : 1 ≤ k) :
    Tendsto (fun q : ℕ => (Nat.primeCounting ⌊k * xq q⌋₊ : ℝ) / q.totient) atTop (𝓝 k) := by
  have hk0 : 0 < k := by linarith
  have hy : Tendsto (fun q : ℕ => k * xq q) atTop atTop := xq_tendsto.const_mul_atTop hk0
  have hP := pnt.comp hy
  have hlx : Tendsto (fun q : ℕ => Real.log (xq q)) atTop atTop :=
    Real.tendsto_log_atTop.comp xq_tendsto
  have hB : Tendsto (fun q : ℕ => 1 / (Real.log k / Real.log (xq q) + 1)) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds.div_atTop hlx).add tendsto_const_nhds).inv₀
      (by norm_num : (0 : ℝ) + 1 ≠ 0)
  have hall := (hP.mul (tendsto_const_nhds (x := k))).mul (log_ratio.mul hB)
  rw [one_mul, one_mul, mul_one] at hall
  refine hall.congr' ?_
  filter_upwards [log_le_log_xq, xq_tendsto.eventually_gt_atTop 1, eventually_gt_atTop 0]
    with q ⟨hl0, hl⟩ hx1 hq
  have hx0 : 0 < xq q := by linarith
  have hlx0 : 0 < Real.log (xq q) := Real.log_pos hx1
  have hlk : 0 ≤ Real.log k := Real.log_nonneg hk
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hlog : Real.log (k * xq q) = Real.log k + Real.log (xq q) := Real.log_mul hk0.ne' hx0.ne'
  have hxd : xq q = q.totient * Real.log q := rfl
  simp only [Function.comp_apply]
  have hlkx : 0 < Real.log (k * xq q) := by rw [hlog]; linarith
  have e1 : 1 / (Real.log k / Real.log (xq q) + 1) = Real.log (xq q) / Real.log (k * xq q) := by
    rw [hlog]; field_simp
  rw [e1]
  field_simp
  rw [hxd]
  ring

lemma coprime_mod_iff {p q : ℕ} : Nat.Coprime (p % q) q ↔ Nat.Coprime p q := by
  unfold Nat.Coprime
  rw [← Nat.gcd_rec, Nat.gcd_comm]

lemma sum_Nc_eq (q u : ℕ) (hq : 0 < q) :
    (∑ a ∈ reduced q, (Nc q u a : ℝ)) =
      (((Icc 1 ⌊xq q⌋₊).filter (fun p : ℕ => p.Prime ∧ zq q u < (p : ℝ) ∧
        Nat.Coprime p q)).card : ℝ) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p => p % q) (t := reduced q)]
  · push_cast
    apply Finset.sum_congr rfl
    intro a ha
    unfold Nc
    rw [Finset.filter_filter]
    congr 2
    apply Finset.filter_congr
    intro p _
    have ha' := Finset.mem_filter.1 ha
    have hlt : a < q := Finset.mem_range.1 ha'.1
    constructor
    · rintro ⟨hp, hz, hmod⟩
      have hm : p % q = a := by
        have := hmod; unfold Nat.ModEq at this; rwa [Nat.mod_eq_of_lt hlt] at this
      refine ⟨⟨hp, hz, ?_⟩, hm⟩
      have := ha'.2
      rw [← hm] at this
      exact coprime_mod_iff.1 this
    · rintro ⟨⟨hp, hz, _⟩, hm⟩
      refine ⟨hp, hz, ?_⟩
      unfold Nat.ModEq; rw [Nat.mod_eq_of_lt hlt]; exact hm
  · intro p hp
    have hp' := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
    simp only [reduced, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.mod_lt _ hq, coprime_mod_iff.2 hp'.2.2.2⟩

lemma card_s_le (q u : ℕ) :
    ((Icc 1 ⌊xq q⌋₊).filter (fun p : ℕ => p.Prime ∧ zq q u < (p : ℝ) ∧
        Nat.Coprime p q)).card ≤ Nat.primeCounting ⌊xq q⌋₊ := by
  rw [primeCounting_eq_card]
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2.1⟩

lemma card_s_ge (q u : ℕ) (hq : q ≠ 0) (hz : 0 ≤ zq q u) :
    Nat.primeCounting ⌊xq q⌋₊ ≤ ((Icc 1 ⌊xq q⌋₊).filter (fun p : ℕ => p.Prime ∧
        zq q u < (p : ℝ) ∧ Nat.Coprime p q)).card + Nat.primeCounting ⌊zq q u⌋₊ +
        q.primeFactors.card := by
  rw [primeCounting_eq_card, primeCounting_eq_card]
  refine le_trans (Finset.card_le_card ?_) ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range,
    Nat.mem_primeFactors]
  by_cases hzp : zq q u < (p : ℝ)
  · by_cases hcop : Nat.Coprime p q
    · left; left; exact ⟨⟨hp.2.one_lt.le, by omega⟩, hp.2, hzp, hcop⟩
    · right; exact ⟨hp.2, (Nat.Prime.dvd_iff_not_coprime hp.2).2 hcop, hq⟩
  · left; right
    refine ⟨?_, hp.2⟩
    have := Nat.le_floor (not_lt.1 hzp)
    omega

/-- **S4** `E N → 1`. -/
theorem avgN_tendsto (u : ℕ) (hu : 2 ≤ u) :
    Tendsto (fun q : ℕ => avg q (fun a => (Nc q u a : ℝ))) atTop (𝓝 1) := by
  have h1 : Tendsto (fun q : ℕ => (Nat.primeCounting ⌊xq q⌋₊ : ℝ) / q.totient) atTop (𝓝 1) := by
    simpa using pi_over_phi 1 le_rfl
  have h2 := pi_z_small u hu
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h3' : Tendsto (fun q : ℕ => Real.log (xq q) ^ 2 / (Real.log 2 * xq q + 0)) atTop (𝓝 0) :=
    (Real.tendsto_pow_log_div_mul_add_atTop (Real.log 2) 0 2 hlog2.ne').comp xq_tendsto
  have h3 : Tendsto (fun q : ℕ => (q.primeFactors.card : ℝ) / q.totient) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3' ?_ ?_
    · filter_upwards with q; positivity
    · filter_upwards [log_le_log_xq, eventually_gt_atTop 0, xq_pos] with q ⟨hl0, hl⟩ hq hx0
      have hc := card_mul_log_le (q := q) (by omega) (w := 2) (by norm_num) q.primeFactors
        subset_rfl (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le)
      have hφx : (q.totient : ℝ) = xq q / Real.log q := by
        unfold xq; field_simp
      rw [hφx, add_zero]
      have hcard : (q.primeFactors.card : ℝ) ≤ Real.log q / Real.log 2 := (le_div_iff₀ hlog2).2 hc
      calc (q.primeFactors.card : ℝ) / (xq q / Real.log q)
          = (q.primeFactors.card : ℝ) * Real.log q / xq q := by field_simp
        _ ≤ (Real.log q / Real.log 2) * Real.log q / xq q := by gcongr
        _ ≤ (Real.log (xq q) / Real.log 2) * Real.log (xq q) / xq q := by
            gcongr
            exact div_nonneg (by linarith) hlog2.le
        _ = _ := by field_simp
  have hlow := (h1.sub h2).sub h3
  rw [sub_zero, sub_zero] at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow h1 ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with q hq
    have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
    have hz0 : 0 ≤ zq q u := Real.rpow_nonneg
      (by unfold xq; exact mul_nonneg (by positivity) (Real.log_natCast_nonneg q)) _
    simp only [avg]
    rw [sum_Nc_eq q u hq, ← sub_div, ← sub_div]
    apply div_le_div_of_nonneg_right _ hφ.le
    have := card_s_ge q u (by omega) hz0
    have : ((Nat.primeCounting ⌊xq q⌋₊ : ℕ) : ℝ) ≤
        (((Icc 1 ⌊xq q⌋₊).filter (fun p : ℕ => p.Prime ∧ zq q u < (p : ℝ) ∧
          Nat.Coprime p q)).card : ℝ) + (Nat.primeCounting ⌊zq q u⌋₊ : ℝ) +
          (q.primeFactors.card : ℝ) := by exact_mod_cast this
    linarith
  · filter_upwards [eventually_gt_atTop 0] with q hq
    have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
    simp only [avg]
    rw [sum_Nc_eq q u hq]
    apply div_le_div_of_nonneg_right _ hφ.le
    exact_mod_cast card_s_le q u

/-- **S5** `A_q ≤ C_M u`. -/
theorem Aq_le : ∃ CM : ℝ, 0 < CM ∧ ∀ u : ℕ, 1 ≤ u → ∀ᶠ q : ℕ in atTop, Aq q u ≤ CM * u := by
  obtain ⟨c, C0, hc, hM⟩ := mertens_product
  refine ⟨max C0 1, by positivity, fun u hu => ?_⟩
  filter_upwards [log_le_log_xq, (zq_tendsto u hu).eventually_ge_atTop 2, xq_pos,
    eventually_gt_atTop 0] with q ⟨hl0, hl⟩ hz2 hx0 hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have hlx : 0 < Real.log (xq q) := by linarith
  have hlz : Real.log (zq q u) = Real.log (xq q) / u := log_zq hx0
  have hlz0 : 0 < Real.log (zq q u) := by rw [hlz]; positivity
  have hA : Aq q u = Real.log q * V (zq q u) := by
    unfold Aq xq; field_simp
  have hV : V (zq q u) ≤ max C0 1 / Real.log (zq q u) :=
    (hM _ hz2).2.trans (div_le_div_of_nonneg_right (le_max_left _ _) hlz0.le)
  rw [hA]
  calc Real.log q * V (zq q u) ≤ Real.log q * (max C0 1 / Real.log (zq q u)) := by gcongr
    _ = max C0 1 * u * (Real.log q / Real.log (xq q)) := by rw [hlz]; field_simp
    _ ≤ max C0 1 * u * 1 := by
        gcongr
        exact div_le_one_of_le₀ hl hlx.le
    _ = max C0 1 * u := mul_one _

lemma continuousOn_inv_log : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Ici 2) := by
  apply ContinuousOn.div continuousOn_const
  · exact Real.continuousOn_log.mono (fun t ht => by
      simp only [Set.mem_Ici] at ht; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith)
  · intro t ht
    simp only [Set.mem_Ici] at ht
    exact (Real.log_pos (by linarith)).ne'

lemma intervalIntegrable_inv_log {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_inv_log.mono
  intro t ht
  simp only [Set.mem_Ici]
  rcases Set.mem_uIcc.1 ht with h | h <;> linarith [h.1]

/-- **S6** -/
theorem Li_sub_ge {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) : (b - a) / Real.log b ≤ Li b - Li a := by
  have hb : 2 ≤ b := ha.trans hab
  unfold Li
  rw [intervalIntegral.integral_interval_sub_left (intervalIntegrable_inv_log le_rfl hb)
    (intervalIntegrable_inv_log le_rfl ha)]
  have hc : ∫ _t in a..b, 1 / Real.log b = (b - a) / Real.log b := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  rw [← hc]
  apply intervalIntegral.integral_mono_on hab intervalIntegrable_const
    (intervalIntegrable_inv_log ha hb)
  intro t ht
  exact one_div_le_one_div_of_le (Real.log_pos (by linarith [ht.1]))
    (Real.log_le_log (by linarith [ht.1]) ht.2)

/-- **S7** `(π((1+c)x) - π(x))/φ(q) → c`. -/
theorem pi_window (c : ℝ) (hc : 0 < c) :
    Tendsto (fun q : ℕ => ((Nat.primeCounting ⌊(1 + c) * xq q⌋₊ : ℝ)
      - Nat.primeCounting ⌊xq q⌋₊) / q.totient) atTop (𝓝 c) := by
  have h1 := pi_over_phi (1 + c) (by linarith)
  have h2 : Tendsto (fun q : ℕ => (Nat.primeCounting ⌊xq q⌋₊ : ℝ) / q.totient) atTop (𝓝 1) := by
    simpa using pi_over_phi 1 le_rfl
  have := h1.sub h2
  rw [add_sub_cancel_left] at this
  refine this.congr (fun q => ?_)
  rw [sub_div]

/-- `N_a ≤ W_a` (primes `> z` are `z`-rough). -/
theorem Nc_le_Wc (q u a : ℕ) : Nc q u a ≤ Wc q u a := by
  unfold Nc Wc
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  obtain ⟨hI, hpr, hz, hmod⟩ := hp
  refine ⟨hI, (Nat.Prime.coprime_iff_not_dvd hpr).2 ?_, hmod⟩
  intro hdvd
  unfold Pz at hdvd
  obtain ⟨p', hp', hdp⟩ := (Nat.Prime.prime hpr).dvd_finset_prod_iff _ |>.1 hdvd
  obtain ⟨hp'pr, hp'z⟩ := mem_primesLT.1 hp'
  have := (Nat.prime_dvd_prime_iff_eq hpr hp'pr).1 hdp
  subst this
  linarith

end Erdos971
