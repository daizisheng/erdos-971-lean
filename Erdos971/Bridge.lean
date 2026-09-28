import Erdos971.Axioms
import Erdos971.FL.Instance
import BombieriVinogradov.Assembly.PrimeCountingConversion.Main
import BombieriVinogradov.Definitions.Statement
import PrimeNumberTheoremAnd.Consequences
import PrimeNumberTheoremAnd.IEANTN.Mertens

/-!
# Erdős #971 — proved analytic inputs (bridge to PrimeNumberTheoremAnd and bombieri-vinogradov)

In the final build these are derived from
* `pi_alt` / `pi_asymp` (PrimeNumberTheoremAnd, `Consequences.lean`),
* `prod_one_minus_div_prime_eq`, `E₃.abs_le` (PrimeNumberTheoremAnd, `IEANTN/Mertens.lean`),
* `BombieriVinogradov.bombieriVinogradov` (kimihiro64/bombieri-vinogradov, `Solution.lean`).
-/

open Real Finset Filter Topology Asymptotics

namespace Erdos971

private lemma prod_le_prod_of_subset_unit {s t : Finset ℕ} (h : s ⊆ t) (f : ℕ → ℝ)
    (hf0 : ∀ p ∈ t, 0 ≤ f p) (hf1 : ∀ p ∈ t, f p ≤ 1) :
    ∏ p ∈ t, f p ≤ ∏ p ∈ s, f p := by
  rw [← Finset.prod_sdiff h]
  have h1 : ∏ p ∈ t \ s, f p ≤ 1 :=
    Finset.prod_le_one (fun p hp => hf0 p (Finset.sdiff_subset hp))
      (fun p hp => hf1 p (Finset.sdiff_subset hp))
  have h2 : 0 ≤ ∏ p ∈ s, f p := Finset.prod_nonneg (fun p hp => hf0 p (h hp))
  nlinarith

private lemma prime_factor_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ 1 - 1 / (p : ℝ) := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [sub_nonneg, div_le_one (by linarith)]; linarith

private lemma prime_factor_le_one (p : ℕ) : 1 - 1 / (p : ℝ) ≤ 1 := by
  have : 0 ≤ 1 / (p : ℝ) := by positivity
  linarith

/-- `P(x) = ∏_{p ≤ x}`. -/
private lemma primesLT_subset_Ioc (z : ℝ) :
    primesLT z ⊆ (Finset.Ioc 0 ⌊z⌋₊).filter Nat.Prime := by
  intro p hp
  simp only [primesLT, Finset.mem_filter, Finset.mem_range] at hp
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  refine ⟨⟨hp.2.1.pos, Nat.le_floor hp.2.2.le⟩, hp.2.1⟩

private lemma Ioc_subset_primesLT (z : ℝ) (hz : 1 ≤ z) :
    (Finset.Ioc 0 ⌊z - 1/2⌋₊).filter Nat.Prime ⊆ primesLT z := by
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
  have h1 : (p : ℝ) ≤ z - 1/2 := (Nat.le_floor_iff (by linarith)).mp hp.1.2
  have h2 : (p : ℝ) < z := by linarith
  simp only [primesLT, Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_ceil.mpr h2, hp.2, h2⟩

private lemma V_le_one (z : ℝ) : V z ≤ 1 := by
  unfold V
  apply Finset.prod_le_one
  · intro p hp
    simp only [primesLT, Finset.mem_filter] at hp
    exact prime_factor_nonneg hp.2.1
  · intro p _; exact prime_factor_le_one p


/-- `(log x)^A ≤ K x^{3/20}` for `x ≥ 1`. -/
private lemma log_rpow_le_small (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 1 ≤ x → Real.log x ^ A ≤ K * x ^ ((3:ℝ)/20) := by
  set ε : ℝ := 3 / (20 * A) with hε
  have hε0 : 0 < ε := by positivity
  refine ⟨1 / ε ^ A, by positivity, fun x hx => ?_⟩
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : Real.log x ≤ x ^ ε / ε := Real.log_le_rpow_div (by linarith) hε0
  calc Real.log x ^ A ≤ (x ^ ε / ε) ^ A := Real.rpow_le_rpow hl0 h1 hA.le
    _ = 1 / ε ^ A * x ^ ((3:ℝ)/20) := by
      rw [Real.div_rpow (by positivity) hε0.le, ← Real.rpow_mul (by linarith)]
      have : ε * A = 3 / 20 := by rw [hε]; field_simp
      rw [this]; ring

private lemma piAP_le (y : ℝ) (r b : ℕ) (hy : 0 ≤ y) : (piAP y r b : ℝ) ≤ y + 1 := by
  unfold piAP
  have h1 : ((Finset.range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ b [MOD r])).card
      ≤ ⌊y⌋₊ + 1 := by
    simpa using Finset.card_filter_le (Finset.range (⌊y⌋₊ + 1)) (fun p => p.Prime ∧ p ≡ b [MOD r])
  have h2 : ((⌊y⌋₊ : ℕ) : ℝ) ≤ y := Nat.floor_le hy
  have : ((((Finset.range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ b [MOD r])).card : ℕ) : ℝ)
      ≤ ((⌊y⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at this
  linarith

private lemma term_le_trivial (y : ℝ) (hy : 0 ≤ y) (r b : ℕ) (hr : 1 ≤ r) :
    |(piAP y r b : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ) / (r.totient : ℝ)| ≤ 2 * (y + 1) := by
  have h1 := piAP_le y r b hy
  have ht : (1 : ℝ) ≤ (r.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hpi : (Nat.primeCounting ⌊y⌋₊ : ℝ) ≤ y + 1 := by
    have : Nat.primeCounting ⌊y⌋₊ ≤ ⌊y⌋₊ + 1 := by
      unfold Nat.primeCounting Nat.primeCounting'
      exact Nat.count_le (p := Nat.Prime) (n := ⌊y⌋₊ + 1)
    have h2 : ((⌊y⌋₊ : ℕ) : ℝ) ≤ y := Nat.floor_le hy
    have : (Nat.primeCounting ⌊y⌋₊ : ℝ) ≤ ((⌊y⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  have hpi0 : (0:ℝ) ≤ Nat.primeCounting ⌊y⌋₊ := by positivity
  have hq : (Nat.primeCounting ⌊y⌋₊ : ℝ) / (r.totient : ℝ) ≤ y + 1 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hq0 : 0 ≤ (Nat.primeCounting ⌊y⌋₊ : ℝ) / (r.totient : ℝ) := by positivity
  have hp0 : (0:ℝ) ≤ piAP y r b := by positivity
  rw [abs_le]; constructor <;> linarith

private lemma piAP_eq_primeCountingZMod (y : ℝ) (hy : 0 ≤ y) (r b : ℕ) (h : Nat.Coprime b r) :
    (piAP y r b : ℝ) =
      (Real.primeCountingZMod y r ((ZMod.unitOfCoprime b h : (ZMod r)ˣ) : ZMod r) : ℝ) := by
  congr 1
  unfold piAP Real.primeCountingZMod
  rw [← Set.ncard_coe_finset]
  congr 1
  ext p
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, ZMod.coe_unitOfCoprime,
    ZMod.natCast_eq_natCast_iff]
  constructor
  · rintro ⟨hp, hpr, hmod⟩
    refine ⟨hpr, hmod, ?_⟩
    exact (Nat.le_floor_iff hy).mp (by omega)
  · rintro ⟨hpr, hmod, hp⟩
    refine ⟨?_, hpr, hmod⟩
    have := Nat.le_floor hp
    omega

private lemma term_le_sup (y : ℝ) (hy : 0 ≤ y) (r b : ℕ) (h : Nat.Coprime b r) :
    |(piAP y r b : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ) / (r.totient : ℝ)| ≤
      ⨆ a : (ZMod r)ˣ,
        |((Real.primeCountingZMod y r a : ℝ) - pi y / r.totient : ℝ)| := by
  rw [piAP_eq_primeCountingZMod y hy r b h]
  exact le_ciSup (f := fun a : (ZMod r)ˣ =>
      |((Real.primeCountingZMod y r a : ℝ) - pi y / r.totient : ℝ)|)
    (Set.finite_range _).bddAbove (ZMod.unitOfCoprime b h)

/-- **Prime number theorem**: `π(x) log x / x → 1`. -/
theorem pnt :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x) atTop (𝓝 1) := by
  have hne : ∀ᶠ x : ℝ in atTop, x / Real.log x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (Real.exp 1)] with x hx
    have hx1 : 1 < x := lt_trans (by
      have := Real.add_one_le_exp (1:ℝ); linarith) hx
    exact div_ne_zero (by linarith) (Real.log_pos hx1).ne'
  have h := (isEquivalent_iff_tendsto_one hne).mp pi_alt'
  refine h.congr (fun x => ?_)
  simp only [Pi.div_apply]
  rw [div_div_eq_mul_div]

/-- `Li y ∼ y / log y`. -/
theorem li_asymp :
    Tendsto (fun y : ℝ => Li y * Real.log y / y) atTop (𝓝 1) := by
  obtain ⟨c, hc, hev⟩ := integral_div_log_asymptotic
  have hc0 : Tendsto c atTop (𝓝 0) := by
    simpa using hc.tendsto_div_nhds_zero
  have h1 : Tendsto (fun x => 1 + c x) atTop (𝓝 1) := by
    simpa using hc0.const_add 1
  refine h1.congr' ?_
  filter_upwards [hev, eventually_ge_atTop (2:ℝ)] with x hx hx2
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hLi : Li x = ∫ t in Set.Icc 2 x, 1 / Real.log t := by
    unfold Li
    rw [intervalIntegral.integral_of_le hx2, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hLi, hx]
  field_simp

/-- **Mertens' product theorem**, weak two-sided form `V(z) ≍ 1 / log z`. -/
theorem mertens_product :
    ∃ c C : ℝ, 0 < c ∧ ∀ z : ℝ, 2 ≤ z → c / Real.log z ≤ V z ∧ V z ≤ C / Real.log z := by
  obtain ⟨C₀, hC₀⟩ := Mertens.E₃.abs_le
  set K : ℝ := |C₀| / Real.log 2 with hK
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hE : ∀ x : ℝ, 2 ≤ x → |Mertens.E₃ x| ≤ K := by
    intro x hx
    have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    calc |Mertens.E₃ x| ≤ C₀ / Real.log x := hC₀ x hx
      _ ≤ |C₀| / Real.log x := div_le_div_of_nonneg_right (le_abs_self C₀) (by linarith)
      _ ≤ |C₀| / Real.log 2 := by gcongr
  set γ : ℝ := eulerMascheroniConstant with hγ
  refine ⟨Real.exp (-γ) * Real.exp (-K), max 1 (2 * (Real.exp (-γ) * Real.exp K)),
    by positivity, fun z hz => ⟨?_, ?_⟩⟩
  · -- lower bound
    have hlz : 0 < Real.log z := Real.log_pos (by linarith)
    have hsub := prod_le_prod_of_subset_unit (primesLT_subset_Ioc z) (fun p => 1 - 1 / (p : ℝ))
      (fun p hp => prime_factor_nonneg (Finset.mem_filter.mp hp).2)
      (fun p _ => prime_factor_le_one p)
    rw [Mertens.prod_one_minus_div_prime_eq (by linarith)] at hsub
    have hEz := (abs_le.mp (hE z hz)).1
    calc Real.exp (-γ) * Real.exp (-K) / Real.log z
        ≤ Real.exp (-γ) * Real.exp (Mertens.E₃ z) / Real.log z := by
          gcongr
      _ ≤ V z := hsub
  · -- upper bound
    have hlz : 0 < Real.log z := Real.log_pos (by linarith)
    by_cases hz' : 5/2 ≤ z
    · have hx2 : 2 ≤ z - 1/2 := by linarith
      have hsub := prod_le_prod_of_subset_unit (Ioc_subset_primesLT z (by linarith))
        (fun p => 1 - 1 / (p : ℝ))
        (fun p hp => by
          simp only [primesLT, Finset.mem_filter] at hp
          exact prime_factor_nonneg hp.2.1)
        (fun p _ => prime_factor_le_one p)
      rw [Mertens.prod_one_minus_div_prime_eq (by linarith)] at hsub
      have hEz := (abs_le.mp (hE (z - 1/2) hx2)).2
      have hlx : 0 < Real.log (z - 1/2) := Real.log_pos (by linarith)
      have hsq : Real.log z ≤ 2 * Real.log (z - 1/2) := by
        rw [← Real.log_rpow (by linarith)]
        apply Real.log_le_log (by linarith)
        rw [Real.rpow_two]; nlinarith [sq_nonneg (z - 2)]
      calc V z ≤ Real.exp (-γ) * Real.exp (Mertens.E₃ (z - 1/2)) / Real.log (z - 1/2) := hsub
        _ ≤ Real.exp (-γ) * Real.exp K / Real.log (z - 1/2) := by gcongr
        _ ≤ 2 * (Real.exp (-γ) * Real.exp K) / Real.log z := by
          rw [div_le_div_iff₀ hlx hlz]
          have : 0 < Real.exp (-γ) * Real.exp K := by positivity
          nlinarith
        _ ≤ max 1 (2 * (Real.exp (-γ) * Real.exp K)) / Real.log z := by
          gcongr; exact le_max_right _ _
    · push Not at hz'
      have hl1 : Real.log z < 1 := by
        rw [Real.log_lt_iff_lt_exp (by linarith)]
        have := Real.exp_one_gt_d9; linarith
      calc V z ≤ 1 := V_le_one z
        _ ≤ 1 / Real.log z := by rw [le_div_iff₀ hlz]; linarith
        _ ≤ max 1 (2 * (Real.exp (-γ) * Real.exp K)) / Real.log z := by
          gcongr; exact le_max_left _ _

/-- **Bombieri–Vinogradov**, fixed height `y ≤ x`, moduli up to `x^{1/4}`, main term `π(y)/φ(r)`. -/
theorem bv_pi (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ y : ℝ, 2 ≤ y → y ≤ x → ∀ b : ℕ → ℕ,
      (∀ r, Nat.Coprime (b r) r) →
      ∑ r ∈ Finset.Icc 1 ⌊x ^ ((1 : ℝ) / 4)⌋₊,
          |(piAP y r (b r) : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ) / (r.totient : ℝ)|
        ≤ C * x / (Real.log x) ^ A := by
  obtain ⟨K, hK0, hK⟩ := log_rpow_le_small A hA
  have hBV := BombieriVinogradov.PrimeCountingConversion.weighted_to_prime_counting
  obtain ⟨c, hc0, hc⟩ := hBV (5/12) (by norm_num) (max A 1) (le_max_right _ _)
  refine ⟨max (8 * K) (c / (3/5 : ℝ) ^ A), fun x hx y hy hyx b hb => ?_⟩
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlxA : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hlx A
  have hxl0 : 0 ≤ x / Real.log x ^ A := by positivity
  set S := ∑ r ∈ Finset.Icc 1 ⌊x ^ ((1 : ℝ) / 4)⌋₊,
          |(piAP y r (b r) : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ) / (r.totient : ℝ)| with hS
  rw [mul_div_assoc]
  by_cases hbig : 3 ≤ y ∧ x ^ ((3:ℝ)/5) ≤ y
  · -- BV case
    obtain ⟨hy3, hyx'⟩ := hbig
    have hfloor : ⌊x ^ ((1 : ℝ) / 4)⌋₊ ≤ ⌊y ^ ((5:ℝ)/12)⌋₊ := by
      apply Nat.floor_le_floor
      calc x ^ ((1:ℝ)/4) = (x ^ ((3:ℝ)/5)) ^ ((5:ℝ)/12) := by
            rw [← Real.rpow_mul hx0.le]; norm_num
        _ ≤ y ^ ((5:ℝ)/12) := Real.rpow_le_rpow (by positivity) hyx' (by norm_num)
    have hy0 : 0 ≤ y := by linarith
    have h1 : S ≤ ∑ r ∈ Finset.Icc 1 ⌊y ^ ((5:ℝ)/12)⌋₊,
        |(piAP y r (b r) : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ) / (r.totient : ℝ)| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.Icc_subset_Icc le_rfl hfloor
      · intro _ _ _; exact abs_nonneg _
    have h2 : ∑ r ∈ Finset.Icc 1 ⌊y ^ ((5:ℝ)/12)⌋₊,
        |(piAP y r (b r) : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ) / (r.totient : ℝ)| ≤
        ∑ q ∈ Finset.Icc 1 ⌊y ^ ((5:ℝ)/12)⌋₊, ⨆ a : (ZMod q)ˣ,
          |((Real.primeCountingZMod y q a : ℝ) - pi y / q.totient : ℝ)| := by
      apply Finset.sum_le_sum
      intro r hr
      exact term_le_sup y hy0 r (b r) (hb r)
    have h3 := hc y hy3
    -- compare c y / (log y)^{A'} with (c/(3/5)^A) x/(log x)^A
    have hly : (3/5 : ℝ) * Real.log x ≤ Real.log y := by
      have := Real.log_le_log (by positivity) hyx'
      rwa [Real.log_rpow hx0] at this
    have hly1 : 1 ≤ Real.log y := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    have hlyA : ((3/5 : ℝ) * Real.log x) ^ A ≤ Real.log y ^ max A 1 := by
      calc ((3/5 : ℝ) * Real.log x) ^ A ≤ Real.log y ^ A :=
            Real.rpow_le_rpow (by positivity) hly hA.le
        _ ≤ Real.log y ^ max A 1 := Real.rpow_le_rpow_of_exponent_le hly1 (le_max_left _ _)
    have hpos : 0 < ((3/5 : ℝ) * Real.log x) ^ A := by positivity
    have h4 : c * y / Real.log y ^ max A 1 ≤ c / (3/5 : ℝ) ^ A * (x / Real.log x ^ A) := by
      rw [Real.mul_rpow (by norm_num) hlx.le] at hpos hlyA
      have hlyA' : 0 < Real.log y ^ max A 1 := lt_of_lt_of_le hpos hlyA
      rw [div_le_iff₀ hlyA']
      have h35 : 0 < (3/5 : ℝ) ^ A := by positivity
      calc c * y ≤ c * x := by gcongr
        _ = c / (3/5 : ℝ) ^ A * (x / Real.log x ^ A) * ((3/5 : ℝ) ^ A * Real.log x ^ A) := by
          field_simp
        _ ≤ c / (3/5 : ℝ) ^ A * (x / Real.log x ^ A) * Real.log y ^ max A 1 := by
          gcongr
    calc S ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ c * y / Real.log y ^ max A 1 := h3
      _ ≤ c / (3/5 : ℝ) ^ A * (x / Real.log x ^ A) := h4
      _ ≤ max (8 * K) (c / (3/5 : ℝ) ^ A) * (x / Real.log x ^ A) := by
          gcongr; exact le_max_right _ _
  · -- trivial case
    have hy0 : 0 ≤ y := by linarith
    have hx35 : 1 ≤ x ^ ((3:ℝ)/5) := Real.one_le_rpow (by linarith) (by norm_num)
    have hy1 : 2 * (y + 1) ≤ 8 * x ^ ((3:ℝ)/5) := by
      rcases not_and_or.mp hbig with h | h
      · push Not at h; linarith
      · push Not at h; linarith
    have hterm : ∀ r ∈ Finset.Icc 1 ⌊x ^ ((1 : ℝ) / 4)⌋₊,
        |(piAP y r (b r) : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ) / (r.totient : ℝ)| ≤ 2 * (y + 1) :=
      fun r hr => term_le_trivial y hy0 r (b r) (Finset.mem_Icc.mp hr).1
    have hcard : ((Finset.Icc 1 ⌊x ^ ((1 : ℝ) / 4)⌋₊).card : ℝ) ≤ x ^ ((1:ℝ)/4) := by
      rw [Nat.card_Icc]; simp only [add_tsub_cancel_right]
      exact Nat.floor_le (by positivity)
    have h1 : S ≤ x ^ ((1:ℝ)/4) * (2 * (y + 1)) := by
      calc S ≤ ∑ r ∈ Finset.Icc 1 ⌊x ^ ((1 : ℝ) / 4)⌋₊, 2 * (y + 1) := Finset.sum_le_sum hterm
        _ = ((Finset.Icc 1 ⌊x ^ ((1 : ℝ) / 4)⌋₊).card : ℝ) * (2 * (y + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ x ^ ((1:ℝ)/4) * (2 * (y + 1)) := by gcongr
    have h2 : x ^ ((1:ℝ)/4) * (2 * (y + 1)) ≤ 8 * x ^ ((17:ℝ)/20) := by
      calc x ^ ((1:ℝ)/4) * (2 * (y + 1)) ≤ x ^ ((1:ℝ)/4) * (8 * x ^ ((3:ℝ)/5)) := by gcongr
        _ = 8 * x ^ ((17:ℝ)/20) := by
          rw [show ((17:ℝ)/20) = 1/4 + 3/5 by norm_num, Real.rpow_add hx0]; ring
    have h3 : 8 * x ^ ((17:ℝ)/20) ≤ 8 * K * (x / Real.log x ^ A) := by
      have hk := hK x (by linarith)
      rw [mul_assoc, mul_le_mul_iff_right₀ (by norm_num : (0:ℝ) < 8), mul_div_assoc',
        le_div_iff₀ hlxA]
      calc x ^ ((17:ℝ)/20) * Real.log x ^ A ≤ x ^ ((17:ℝ)/20) * (K * x ^ ((3:ℝ)/20)) := by
            gcongr
        _ = K * x := by
          rw [mul_left_comm, ← Real.rpow_add hx0]; norm_num
    calc S ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ _ := h3
      _ ≤ max (8 * K) (c / (3/5 : ℝ) ^ A) * (x / Real.log x ^ A) := by
          gcongr; exact le_max_left _ _

end Erdos971
