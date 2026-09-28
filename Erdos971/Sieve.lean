import Erdos971.Defs

/-!
# Sieve applications (BLUEPRINT §4). Uses `fundamental_lemma`, `mertens_product`, `bv_pi`.
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

lemma mem_primesLT_sv {z : ℝ} {p : ℕ} : p ∈ primesLT z ↔ p.Prime ∧ (p : ℝ) < z := by
  unfold primesLT
  simp only [Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  intro h
  exact Nat.lt_ceil.mpr h.2

lemma one_sub_inv_pos_sv {p : ℕ} (hp : p.Prime) : 0 < 1 - 1 / (p : ℝ) := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [sub_pos, div_lt_one (by linarith)]; linarith

lemma V_pos (z : ℝ) : 0 < V z := by
  unfold V
  exact Finset.prod_pos fun p hp => one_sub_inv_pos_sv (mem_primesLT_sv.mp hp).1

lemma Pz_pos (z : ℝ) : 0 < Pz z := by
  unfold Pz
  exact Finset.prod_pos fun p hp => (mem_primesLT_sv.mp hp).1.pos

lemma dvd_Pz {z : ℝ} {p : ℕ} (hp : p ∈ primesLT z) : p ∣ Pz z :=
  Finset.dvd_prod_of_mem _ hp

lemma prime_dvd_Pz {z : ℝ} {p : ℕ} (hp : p.Prime) (h : p ∣ Pz z) : p ∈ primesLT z := by
  unfold Pz at h
  obtain ⟨a, ha, hpa⟩ := (Prime.dvd_finset_prod_iff hp.prime _).mp h
  have ha' := (mem_primesLT_sv.mp ha).1
  rw [(Nat.prime_dvd_prime_iff_eq hp ha').mp hpa]; exact ha

lemma Pz_squarefree (z : ℝ) : Squarefree (Pz z) := by
  unfold Pz
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro a ha b hb hab
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (mem_primesLT_sv.mp ha).1 (mem_primesLT_sv.mp hb).1).mpr hab)
  · intro p hp; exact (mem_primesLT_sv.mp hp).1.prime.squarefree

lemma sqf_of_mem_divisors {z : ℝ} {d : ℕ} (hd : d ∈ (Pz z).divisors) : Squarefree d :=
  (Pz_squarefree z).squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)

lemma primeFactors_sub {z : ℝ} {d : ℕ} (hd : d ∈ (Pz z).divisors) {p : ℕ}
    (hp : p ∈ d.primeFactors) : p ∈ primesLT z :=
  prime_dvd_Pz (Nat.prime_of_mem_primeFactors hp)
    ((Nat.dvd_of_mem_primeFactors hp).trans (Nat.dvd_of_mem_divisors hd))

/-- totient of a squarefree number. -/
lemma totient_sqf {d : ℕ} (hd : Squarefree d) :
    (d.totient : ℝ) = ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) := by
  have h1 := Nat.totient_mul_prod_primeFactors d
  rw [Nat.prod_primeFactors_of_squarefree hd] at h1
  have hd0 : d ≠ 0 := hd.ne_zero
  have h2 : d.totient = ∏ p ∈ d.primeFactors, (p - 1) := by
    rw [mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd0) h1
  rw [h2, Nat.cast_prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]; simp

lemma V_split {z w : ℝ} (hwz : w < z) :
    V z = V w * ∏ p ∈ (primesLT z).filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - 1 / (p : ℝ)) := by
  unfold V
  rw [← Finset.prod_filter_not_mul_prod_filter (primesLT z) (fun p : ℕ => w ≤ (p : ℝ))]
  congr 1
  apply Finset.prod_congr _ (fun _ _ => rfl)
  ext p
  simp only [Finset.mem_filter, mem_primesLT_sv, not_le]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3.trans hwz⟩, h3⟩

/-- Dimension condition from Mertens, for any `g` dominated by `(1 - 1/p)^5`. -/
lemma dimcond : ∃ K : ℝ, 1 ≤ K ∧ ∀ z : ℝ, 2 ≤ z → ∀ g : ℕ → ℝ,
    (∀ p ∈ primesLT z, (1 - 1 / (p : ℝ)) ^ 5 ≤ 1 - g p) →
    ∀ w : ℝ, 2 ≤ w → w < z →
      ∏ p ∈ (primesLT z).filter (fun p : ℕ => w ≤ (p : ℝ)), (1 - g p)⁻¹
        ≤ K * (Real.log z / Real.log w) ^ (5 : ℝ) := by
  obtain ⟨c, C, hc, hM⟩ := mertens_product
  refine ⟨max 1 ((C / c) ^ 5), le_max_left _ _, ?_⟩
  intro z hz g hg w hw hwz
  set F := (primesLT z).filter (fun p : ℕ => w ≤ (p : ℝ))
  set P := ∏ p ∈ F, (1 - 1 / (p : ℝ)) with hP
  have hPpos : 0 < P := Finset.prod_pos fun p hp =>
    one_sub_inv_pos_sv (mem_primesLT_sv.mp (Finset.mem_filter.mp hp).1).1
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have h1 : ∏ p ∈ F, (1 - g p)⁻¹ ≤ ∏ p ∈ F, ((1 - 1 / (p : ℝ)) ^ 5)⁻¹ := by
    apply Finset.prod_le_prod
    · intro p hp
      have := one_sub_inv_pos_sv (mem_primesLT_sv.mp (Finset.mem_filter.mp hp).1).1
      have h := hg p (Finset.mem_filter.mp hp).1
      exact inv_nonneg.mpr (lt_of_lt_of_le (by positivity) h).le
    · intro p hp
      have := one_sub_inv_pos_sv (mem_primesLT_sv.mp (Finset.mem_filter.mp hp).1).1
      exact inv_anti₀ (by positivity) (hg p (Finset.mem_filter.mp hp).1)
  have h2 : ∏ p ∈ F, ((1 - 1 / (p : ℝ)) ^ 5)⁻¹ = (P⁻¹) ^ 5 := by
    rw [Finset.prod_inv_distrib, Finset.prod_pow, inv_pow]
  have hsplit := V_split hwz
  have hVw := hM w hw
  have hVz := hM z hz
  have hVwpos := V_pos w
  have hCpos : 0 < C := by
    have := lt_of_lt_of_le hVwpos hVw.2
    exact (div_pos_iff_of_pos_right hlw).mp this
  -- P = V z / V w ≥ (c / log z) / (C / log w)
  have h3 : P⁻¹ ≤ C / c * (Real.log z / Real.log w) := by
    have hPe : P = V z / V w := by rw [hsplit, hP]; field_simp; rfl
    rw [hPe, inv_div, div_le_iff₀ (V_pos z)]
    calc V w ≤ C / Real.log w := hVw.2
      _ = C / c * (Real.log z / Real.log w) * (c / Real.log z) := by field_simp
      _ ≤ C / c * (Real.log z / Real.log w) * V z := by
          apply mul_le_mul_of_nonneg_left hVz.1; positivity
  rw [h2] at h1
  refine h1.trans ?_
  rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc (P⁻¹) ^ 5 ≤ (C / c * (Real.log z / Real.log w)) ^ 5 :=
        pow_le_pow_left₀ (by positivity) h3 5
    _ = (C / c) ^ 5 * (Real.log z / Real.log w) ^ 5 := by ring
    _ ≤ max 1 ((C / c) ^ 5) * (Real.log z / Real.log w) ^ 5 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)


/-- The remainder sum of the fundamental lemma. -/
noncomputable def Rem {ι : Type} (z D : ℝ) (A : Finset ι) (f : ι → ℕ) (g : ℕ → ℝ) (X : ℝ) : ℝ :=
  ∑ d ∈ (Pz z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ D),
    |((A.filter (fun i => d ∣ f i)).card : ℝ) - X * ∏ p ∈ d.primeFactors, g p|

/-- The fundamental lemma with the dimension condition discharged by `dimcond`. -/
lemma FL_setup : ∃ η : ℝ → ℝ, Tendsto (fun s => s * η s) atTop (𝓝 0) ∧ ∃ s₀ : ℝ,
    ∀ z s : ℝ, 2 ≤ z → s₀ ≤ s →
    ∀ {ι : Type} (A : Finset ι) (f : ι → ℕ) (g : ℕ → ℝ) (X : ℝ), 0 ≤ X →
      (∀ p ∈ primesLT z, 0 ≤ g p ∧ g p < 1) →
      (∀ p ∈ primesLT z, (1 - 1 / (p : ℝ)) ^ 5 ≤ 1 - g p) →
      ((A.filter (fun i => Nat.Coprime (f i) (Pz z))).card : ℝ)
          ≤ X * (∏ p ∈ primesLT z, (1 - g p)) * (1 + η s) + Rem z (z ^ s) A f g X ∧
        X * (∏ p ∈ primesLT z, (1 - g p)) * (1 - η s) - Rem z (z ^ s) A f g X
          ≤ ((A.filter (fun i => Nat.Coprime (f i) (Pz z))).card : ℝ) := by
  obtain ⟨K, hK, hdim⟩ := dimcond
  obtain ⟨η, hη, s₀, hFL⟩ := fundamental_lemma 5 K (by norm_num) hK
  refine ⟨η, hη, s₀, ?_⟩
  intro z s hz hs ι A f g X hX hg hg5
  exact hFL z s hz hs A f g X hX hg (hdim z hz g hg5)

lemma level_eq {x : ℝ} (hx : 0 ≤ x) {u : ℕ} (hu : u ≠ 0) (a : ℝ) :
    (x ^ ((1 : ℝ) / u)) ^ ((u : ℝ) * a) = x ^ a := by
  rw [← Real.rpow_mul hx]
  congr 1
  have : (u : ℝ) ≠ 0 := by exact_mod_cast hu
  field_simp

lemma xq_nonneg_sv (q : ℕ) : 0 ≤ xq q := by
  unfold xq
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg q)

lemma abs_floor_sub_le {y : ℝ} (hy : 0 ≤ y) : |(⌊y⌋₊ : ℝ) - y| ≤ 1 := by
  rw [abs_le]
  constructor
  · linarith [Nat.lt_floor_add_one y]
  · linarith [Nat.floor_le hy]

lemma prod_inv_primeFactors {d : ℕ} (hd : Squarefree d) :
    ∏ p ∈ d.primeFactors, (1 / (p : ℝ)) = 1 / (d : ℝ) := by
  rw [Finset.prod_div_distrib, Finset.prod_const_one, ← Nat.cast_prod,
    Nat.prod_primeFactors_of_squarefree hd]

lemma divisors_filter_card_le (z D : ℝ) :
    (((Pz z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ D)).card : ℝ) ≤ ⌊D⌋₊ := by
  have hsub : (Pz z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ D) ⊆ Icc 1 ⌊D⌋₊ := by
    intro d hd
    rw [Finset.mem_filter] at hd
    rw [Finset.mem_Icc]
    refine ⟨Nat.pos_of_mem_divisors hd.1, ?_⟩
    exact Nat.le_floor hd.2
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc] at this
  exact_mod_cast (by omega : _ ≤ ⌊D⌋₊)

lemma mem_divisors_filter_le {z D : ℝ} {d : ℕ}
    (hd : d ∈ (Pz z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ D)) : d ∈ Icc 1 ⌊D⌋₊ := by
  rw [Finset.mem_filter] at hd
  rw [Finset.mem_Icc]
  exact ⟨Nat.pos_of_mem_divisors hd.1, Nat.le_floor hd.2⟩

/-- Sum over reduced classes of `W_a` is at most the number of rough `n ≤ x`. -/
lemma sum_Wc_le (q u : ℕ) (hq : 0 < q) :
    (∑ a ∈ reduced q, (Wc q u a : ℝ))
      ≤ (((Icc 1 ⌊xq q⌋₊).filter (fun n => Nat.Coprime n (Pz (zq q u)))).card : ℝ) := by
  set T := (Icc 1 ⌊xq q⌋₊).filter (fun n => Nat.Coprime n (Pz (zq q u)))
  have hfib := Finset.card_eq_sum_card_fiberwise (f := fun n => n % q) (s := T) (t := range q)
    (fun n _ => by simp only [Finset.coe_range, Set.mem_Iio]; exact Nat.mod_lt n hq)
  have hW : ∀ a ∈ reduced q, Wc q u a = (T.filter (fun n => n % q = a)).card := by
    intro a ha
    have ha' : a < q := by unfold reduced at ha; exact Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    unfold Wc
    rw [Finset.filter_filter]
    congr 1
    apply Finset.filter_congr
    intro n _
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt ha']
  rw [← Nat.cast_sum]
  rw [Finset.sum_congr rfl hW]
  exact_mod_cast (Finset.sum_le_sum_of_subset (by
    intro a ha; unfold reduced at ha; exact (Finset.mem_filter.mp ha).1)).trans hfib.ge

/-- **SV1** at the level of one `q`. -/
lemma first_moment {η : ℝ → ℝ} {s₀ : ℝ}
    (hFL : ∀ z s : ℝ, 2 ≤ z → s₀ ≤ s →
    ∀ {ι : Type} (A : Finset ι) (f : ι → ℕ) (g : ℕ → ℝ) (X : ℝ), 0 ≤ X →
      (∀ p ∈ primesLT z, 0 ≤ g p ∧ g p < 1) →
      (∀ p ∈ primesLT z, (1 - 1 / (p : ℝ)) ^ 5 ≤ 1 - g p) →
      ((A.filter (fun i => Nat.Coprime (f i) (Pz z))).card : ℝ)
          ≤ X * (∏ p ∈ primesLT z, (1 - g p)) * (1 + η s) + Rem z (z ^ s) A f g X ∧
        X * (∏ p ∈ primesLT z, (1 - g p)) * (1 - η s) - Rem z (z ^ s) A f g X
          ≤ ((A.filter (fun i => Nat.Coprime (f i) (Pz z))).card : ℝ))
    (q u : ℕ) (hq : 0 < q) (hu : u ≠ 0) (hz : 2 ≤ zq q u) (hs : s₀ ≤ (u : ℝ) / 4) :
    (∑ a ∈ reduced q, (Wc q u a : ℝ))
      ≤ (1 + η (u / 4)) * xq q * V (zq q u) + xq q ^ ((1 : ℝ) / 4) := by
  have hx := xq_nonneg_sv q
  have hlev : zq q u ^ ((u : ℝ) / 4) = xq q ^ ((1 : ℝ) / 4) := by
    unfold zq; rw [← level_eq hx hu (1 / 4)]; congr 1; ring
  obtain ⟨hup, -⟩ := hFL (zq q u) ((u : ℝ) / 4) hz hs (Icc 1 ⌊xq q⌋₊) id (fun p => 1 / (p : ℝ))
    (xq q) hx
    (fun p hp => by
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesLT_sv.mp hp).1.two_le
      exact ⟨by positivity, by rw [div_lt_one (by linarith)]; linarith⟩)
    (fun p hp => by
      have := one_sub_inv_pos_sv (mem_primesLT_sv.mp hp).1
      have h1 : 1 - 1 / (p : ℝ) ≤ 1 := by
        have : (0 : ℝ) ≤ 1 / p := by positivity
        linarith
      calc (1 - 1 / (p : ℝ)) ^ 5 ≤ (1 - 1 / (p : ℝ)) ^ 1 :=
            pow_le_pow_of_le_one this.le h1 (by norm_num)
        _ = _ := pow_one _)
  have hR : Rem (zq q u) (zq q u ^ ((u : ℝ) / 4)) (Icc 1 ⌊xq q⌋₊) id (fun p => 1 / (p : ℝ)) (xq q)
      ≤ xq q ^ ((1 : ℝ) / 4) := by
    unfold Rem
    rw [hlev]
    have hD : 0 ≤ xq q ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hx _
    refine le_trans ?_ ((divisors_filter_card_le (zq q u) _).trans (Nat.floor_le hD))
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    apply Finset.sum_le_sum
    intro d hd
    have hd1 := (Finset.mem_filter.mp hd).1
    have hsq := sqf_of_mem_divisors hd1
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd1
    rw [prod_inv_primeFactors hsq]
    have hcount : ((Icc 1 ⌊xq q⌋₊).filter (fun i => d ∣ id i)).card = ⌊xq q / d⌋₊ := by
      rw [Nat.floor_div_natCast, ← Nat.card_multiples']
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range, id]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, by omega, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by omega, by omega⟩, h3⟩
    rw [hcount, mul_one_div]
    exact abs_floor_sub_le (by positivity)
  have hVg : ∏ p ∈ primesLT (zq q u), (1 - 1 / (p : ℝ)) = V (zq q u) := rfl
  have hW : (∑ a ∈ reduced q, (Wc q u a : ℝ))
      ≤ (((Icc 1 ⌊xq q⌋₊).filter (fun n => Nat.Coprime (id n) (Pz (zq q u)))).card : ℝ) :=
    sum_Wc_le q u hq
  rw [hVg] at hup
  have e : xq q * V (zq q u) * (1 + η ((u : ℝ) / 4)) = (1 + η (u / 4)) * xq q * V (zq q u) := by
    ring
  linarith


/-- `n (n + H) (n + K)`. -/
def F3 (H K n : ℕ) : ℕ := n * (n + H) * (n + K)

/-- Number of roots of `n (n+H) (n+K) ≡ 0 (mod d)` among `0 ≤ n < d`. -/
def rho (H K d : ℕ) : ℕ := ((range d).filter (fun r => d ∣ F3 H K r)).card

lemma dvd_F3_iff (H K d n : ℕ) :
    d ∣ F3 H K n ↔ (n : ZMod d) * ((n : ZMod d) + H) * ((n : ZMod d) + K) = 0 := by
  rw [← ZMod.natCast_eq_zero_iff]; unfold F3; push_cast; rfl

lemma dvd_F3_mod (H K d n : ℕ) : d ∣ F3 H K n ↔ d ∣ F3 H K (n % d) := by
  rw [dvd_F3_iff, dvd_F3_iff, ZMod.natCast_mod]

lemma rho_le (H K d : ℕ) : rho H K d ≤ d := by
  unfold rho
  exact (Finset.card_filter_le _ _).trans (Finset.card_range d).le

lemma rho_eq_card_zmod (H K d : ℕ) [NeZero d] :
    rho H K d = (univ.filter (fun x : ZMod d => x * (x + H) * (x + K) = 0)).card := by
  unfold rho
  refine Finset.card_nbij' (fun r : ℕ => ((r : ℕ) : ZMod d)) (fun x : ZMod d => x.val) ?_ ?_ ?_ ?_
  · intro r hr
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hr
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact (dvd_F3_iff H K d r).mp hr.2
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    refine ⟨ZMod.val_lt x, ?_⟩
    rw [dvd_F3_iff, ZMod.natCast_zmod_val]; exact hx
  · intro r hr
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hr
    simp only [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hr.1
  · intro x _
    simp only [ZMod.natCast_zmod_val]

lemma rho_mul (H K m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) :
    rho H K (m * n) = rho H K m * rho H K n := by
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : NeZero (m * n) := ⟨(Nat.mul_pos hm hn).ne'⟩
  rw [rho_eq_card_zmod, rho_eq_card_zmod, rho_eq_card_zmod, ← Finset.card_product,
    ← Finset.filter_product, Finset.univ_product_univ]
  apply Finset.card_equiv (ZMod.chineseRemainder hmn).toEquiv
  intro x
  set e := ZMod.chineseRemainder hmn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have key : e (x * (x + H) * (x + K)) = e x * (e x + H) * (e x + K) := by
    simp only [map_mul, map_add, map_natCast]
  have h0 : x * (x + H) * (x + K) = 0 ↔ e (x * (x + H) * (x + K)) = 0 :=
    (map_eq_zero_iff e e.injective).symm
  rw [h0, key, Prod.ext_iff]
  simp only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, Prod.fst_mul, Prod.fst_add,
    Prod.fst_natCast, Prod.snd_mul, Prod.snd_add, Prod.snd_natCast, Prod.fst_zero, Prod.snd_zero]

lemma rho_one (H K : ℕ) : rho H K 1 = 1 := by
  simp [rho]

lemma rho_prod (H K : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    rho H K (∏ p ∈ s, p) = ∏ p ∈ s, rho H K p := by
  induction s using Finset.induction_on with
  | empty => simp [rho_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hpa := hs a (Finset.mem_insert_self a s)
    have hs' : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    rw [rho_mul H K a _ hpa.pos (Finset.prod_pos fun p hp => (hs' p hp).pos), ih hs']
    apply Nat.Coprime.prod_right
    intro p hp
    exact (Nat.coprime_primes hpa (hs' p hp)).mpr (fun h => ha (h ▸ hp))

lemma rho_prime (H K p : ℕ) (hp : p.Prime) : rho H K p = nu3 H K p := by
  haveI := Fact.mk hp
  rw [rho_eq_card_zmod]
  have h1 : (univ.filter (fun x : ZMod p => x * (x + H) * (x + K) = 0))
      = ({0, -(H : ZMod p), -(K : ZMod p)} : Finset (ZMod p)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, mul_eq_zero, add_eq_zero_iff_eq_neg]
    tauto
  have h2 : ({0, -(H : ZMod p), -(K : ZMod p)} : Finset (ZMod p))
      = ({0, H % p, K % p} : Finset ℕ).image (fun r : ℕ => -(r : ZMod p)) := by
    simp [Finset.image_insert, ZMod.natCast_mod]
  rw [h1, h2, Finset.card_image_of_injOn]
  · rfl
  · intro a ha b hb hab
    have hlt : ∀ c ∈ (({0, H % p, K % p} : Finset ℕ) : Set ℕ), c < p := by
      intro c hc
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl | rfl
      · exact hp.pos
      · exact Nat.mod_lt _ hp.pos
      · exact Nat.mod_lt _ hp.pos
    simp only [neg_inj] at hab
    have := (ZMod.natCast_eq_natCast_iff' a b p).mp hab
    rwa [Nat.mod_eq_of_lt (hlt a ha), Nat.mod_eq_of_lt (hlt b hb)] at this

lemma nu3_le (H K p : ℕ) (hp : 0 < p) : nu3 H K p ≤ p := by
  unfold nu3
  calc ({0, H % p, K % p} : Finset ℕ).card ≤ (range p).card := by
        apply Finset.card_le_card
        intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rw [Finset.mem_range]
        rcases hc with rfl | rfl | rfl
        · exact hp
        · exact Nat.mod_lt _ hp
        · exact Nat.mod_lt _ hp
    _ = p := Finset.card_range p

lemma nu3_le_three (H K p : ℕ) : nu3 H K p ≤ 3 := Finset.card_le_three

/-- Counting a periodic predicate. -/
lemma count_periodic (P : ℕ → Prop) [DecidablePred P] (d : ℕ) (hd : 0 < d)
    (hP : ∀ n, P (n + d) ↔ P n) (M : ℕ) :
    (M / d) * ((range d).filter P).card ≤ ((range M).filter P).card ∧
      ((range M).filter P).card ≤ (M / d) * ((range d).filter P).card + ((range d).filter P).card := by
  have hper : Function.Periodic P d := fun n => propext (hP n)
  have hIco : ∀ a, ((Ico a (a + d)).filter P).card = ((range d).filter P).card := by
    intro a
    rw [Nat.filter_Ico_card_eq_of_periodic a d P hper, Nat.count_eq_card_filter_range]
  have hmul : ∀ k, ((range (d * k)).filter P).card = k * ((range d).filter P).card := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show d * (k + 1) = d * k + d by ring, Finset.range_eq_Ico,
        ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le (d * k)) (Nat.le_add_right _ d),
        Finset.filter_union, Finset.card_union_of_disjoint
          (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
        ← Finset.range_eq_Ico, ih, hIco]
      ring
  have hsplit : ((range M).filter P).card = ((range (d * (M / d))).filter P).card
      + ((Ico (d * (M / d)) M).filter P).card := by
    rw [Finset.range_eq_Ico,
      ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le (d * (M / d))) (Nat.mul_div_le M d),
      Finset.filter_union, Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
      ← Finset.range_eq_Ico]
  have htail : ((Ico (d * (M / d)) M).filter P).card ≤ ((range d).filter P).card := by
    rw [← hIco (d * (M / d))]
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    apply Finset.Ico_subset_Ico_right
    have := Nat.div_add_mod M d
    have := Nat.mod_lt M hd
    linarith
  rw [hsplit, hmul]
  constructor <;> omega


lemma pow5_nu {p ν : ℕ} (hp : p.Prime) (h3 : ν ≤ 3) (hνp : ν < p) :
    (1 - 1 / (p : ℝ)) ^ 5 ≤ 1 - (ν : ℝ) / p := by
  have h2 := hp.two_le
  rcases Nat.lt_or_ge p 5 with h | h
  · interval_cases p
    · have : ν ≤ 1 := by omega
      have : (ν : ℝ) ≤ 1 := by exact_mod_cast this
      norm_num; linarith
    · have : ν ≤ 2 := by omega
      have : (ν : ℝ) ≤ 2 := by exact_mod_cast this
      norm_num; linarith
    · exact absurd hp (by norm_num)
  · have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast h
    have hν : (ν : ℝ) ≤ 3 := by exact_mod_cast h3
    have hpos : (0 : ℝ) < p := by linarith
    have e1 : (1 - 1 / (p : ℝ)) ^ 5 = (p - 1) ^ 5 / p ^ 5 := by field_simp
    have e2 : 1 - (ν : ℝ) / p ≥ 1 - 3 / p := by
      have : (ν : ℝ) / p ≤ 3 / p := div_le_div_of_nonneg_right hν hpos.le
      linarith
    have e3 : 1 - 3 / (p : ℝ) = (p - 3) * p ^ 4 / p ^ 5 := by field_simp
    rw [e1]
    refine le_trans ?_ e2
    rw [e3]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_nonneg (pow_nonneg hpos.le 3) (sub_nonneg.mpr hp5), pow_nonneg hpos.le 2]

lemma pow5_pair {p : ℕ} (hp : 3 ≤ p) :
    (1 - 1 / (p : ℝ)) ^ 5 ≤ 1 - 1 / ((p : ℝ) - 1) := by
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h0 : 0 ≤ 1 - 1 / (p : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have h1 : 1 - 1 / (p : ℝ) ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / p := by positivity
    linarith
  calc (1 - 1 / (p : ℝ)) ^ 5 ≤ (1 - 1 / (p : ℝ)) ^ 2 := pow_le_pow_of_le_one h0 h1 (by norm_num)
    _ ≤ 1 - 1 / ((p : ℝ) - 1) := by
      have hp1 : (0 : ℝ) < p - 1 := by linarith
      rw [div_eq_inv_mul, div_eq_inv_mul]
      have ep : (p : ℝ)⁻¹ = 1 / p := by ring
      field_simp
      nlinarith


lemma count_F3 (H K d : ℕ) (hd : 0 < d) {x : ℝ} (hx : 0 ≤ x) :
    |(((range (⌊x⌋₊ + 1)).filter (fun n => d ∣ F3 H K n)).card : ℝ)
        - x * ((rho H K d : ℝ) / d)| ≤ 2 * rho H K d := by
  have hper : ∀ n, d ∣ F3 H K (n + d) ↔ d ∣ F3 H K n := by
    intro n; rw [dvd_F3_mod, Nat.add_mod_right, ← dvd_F3_mod]
  obtain ⟨h1, h2⟩ := count_periodic (fun n => d ∣ F3 H K n) d hd hper (⌊x⌋₊ + 1)
  set M := ⌊x⌋₊ + 1 with hM
  set c := ((range M).filter (fun n => d ∣ F3 H K n)).card
  have hρ : ((range d).filter (fun n => d ∣ F3 H K n)).card = rho H K d := rfl
  rw [hρ] at h1 h2
  set ρ := rho H K d
  set k := M / d
  have hkM : d * k ≤ M := Nat.mul_div_le M d
  have hMk : M < d * k + d := by
    show M < d * (M / d) + d
    have := Nat.div_add_mod M d
    have := Nat.mod_lt M hd
    linarith
  have hxM : x < (M : ℝ) := by rw [hM]; push_cast; exact Nat.lt_floor_add_one x
  have hMx : (M : ℝ) ≤ x + 1 := by rw [hM]; push_cast; linarith [Nat.floor_le hx]
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hkM' : (d : ℝ) * k ≤ M := by exact_mod_cast hkM
  have hMk' : (M : ℝ) < d * k + d := by exact_mod_cast hMk
  have h1' : (k : ℝ) * ρ ≤ c := by exact_mod_cast h1
  have h2' : (c : ℝ) ≤ k * ρ + ρ := by exact_mod_cast h2
  have hρ0 : (0 : ℝ) ≤ ρ := Nat.cast_nonneg _
  have up : (d : ℝ) * c ≤ x * ρ + 2 * d * ρ := by
    have a1 : (d : ℝ) * c ≤ d * (k * ρ + ρ) := mul_le_mul_of_nonneg_left h2' (by linarith)
    have a2 : (d : ℝ) * k * ρ ≤ (x + 1) * ρ := mul_le_mul_of_nonneg_right (hkM'.trans hMx) hρ0
    nlinarith
  have lo : x * ρ - d * ρ ≤ (d : ℝ) * c := by
    have a1 : (d : ℝ) * (k * ρ) ≤ d * c := mul_le_mul_of_nonneg_left h1' (by linarith)
    have a2 : (x - d) * ρ ≤ (d * k) * ρ := mul_le_mul_of_nonneg_right (by linarith) hρ0
    nlinarith
  have hdpos : (0 : ℝ) < d := by linarith
  rw [abs_le]
  constructor
  · have : x * ((ρ : ℝ) / d) = x * ρ / d := by ring
    rw [this]
    have : (x * ρ - d * ρ) / d ≤ c := by rw [div_le_iff₀ hdpos]; linarith
    have e : (x * ρ - d * ρ) / d = x * ρ / d - ρ := by field_simp
    rw [e] at this
    linarith
  · have : x * ((ρ : ℝ) / d) = x * ρ / d := by ring
    rw [this]
    have : (c : ℝ) ≤ (x * ρ + 2 * d * ρ) / d := by rw [le_div_iff₀ hdpos]; linarith
    have e : (x * ρ + 2 * d * ρ) / d = x * ρ / d + 2 * ρ := by field_simp
    rw [e] at this
    linarith

lemma prod_nu (H K d : ℕ) (hd : Squarefree d) :
    ∏ p ∈ d.primeFactors, ((nu3 H K p : ℝ) / p) = (rho H K d : ℝ) / d := by
  rw [Finset.prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod,
    Nat.prod_primeFactors_of_squarefree hd]
  congr 2
  conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hd]
  rw [rho_prod H K _ (fun p hp => Nat.prime_of_mem_primeFactors hp)]
  exact Finset.prod_congr rfl fun p hp => (rho_prime H K p (Nat.prime_of_mem_primeFactors hp)).symm

lemma Vg3 (z : ℝ) (H K : ℕ) :
    ∏ p ∈ primesLT z, (1 - (nu3 H K p : ℝ) / p) = V z ^ 3 * S3 z H K := by
  unfold V S3
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have := one_sub_inv_pos_sv (mem_primesLT_sv.mp hp).1
  field_simp

/-- **SV2** at the level of one `q`. -/
lemma triple_bound {η : ℝ → ℝ} {s₀ : ℝ}
    (hFL : ∀ z s : ℝ, 2 ≤ z → s₀ ≤ s →
    ∀ {ι : Type} (A : Finset ι) (f : ι → ℕ) (g : ℕ → ℝ) (X : ℝ), 0 ≤ X →
      (∀ p ∈ primesLT z, 0 ≤ g p ∧ g p < 1) →
      (∀ p ∈ primesLT z, (1 - 1 / (p : ℝ)) ^ 5 ≤ 1 - g p) →
      ((A.filter (fun i => Nat.Coprime (f i) (Pz z))).card : ℝ)
          ≤ X * (∏ p ∈ primesLT z, (1 - g p)) * (1 + η s) + Rem z (z ^ s) A f g X ∧
        X * (∏ p ∈ primesLT z, (1 - g p)) * (1 - η s) - Rem z (z ^ s) A f g X
          ≤ ((A.filter (fun i => Nat.Coprime (f i) (Pz z))).card : ℝ))
    (q u H K : ℕ) (s : ℝ) (hz : 2 ≤ zq q u) (hs : s₀ ≤ s) (hη : η s ≤ 1) :
    (Qtrip q u H K : ℝ)
      ≤ 2 * xq q * V (zq q u) ^ 3 * S3 (zq q u) H K + 2 * (zq q u ^ s) ^ 2 := by
  set z := zq q u with hzdef
  have hx := xq_nonneg_sv q
  have hD : 0 ≤ z ^ s := Real.rpow_nonneg (by linarith) s
  have hQ : Qtrip q u H K
      = ((Icc 1 ⌊xq q⌋₊).filter (fun n => Nat.Coprime (F3 H K n) (Pz z))).card := rfl
  by_cases hdeg : ∃ p ∈ primesLT z, p ≤ nu3 H K p
  · obtain ⟨p, hp, hle⟩ := hdeg
    have hpp := (mem_primesLT_sv.mp hp).1
    have hνeq : nu3 H K p = p := le_antisymm (nu3_le H K p hpp.pos) hle
    have hrho : rho H K p = p := (rho_prime H K p hpp).trans hνeq
    have hfull : (range p).filter (fun r => p ∣ F3 H K r) = range p := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      rw [Finset.card_range]; exact hrho.ge
    have hzero : Qtrip q u H K = 0 := by
      rw [hQ, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro n _ hcop
      have h1 : p ∣ F3 H K n := by
        rw [dvd_F3_mod]
        have : n % p ∈ (range p).filter (fun r => p ∣ F3 H K r) := by
          rw [hfull, Finset.mem_range]; exact Nat.mod_lt n hpp.pos
        exact (Finset.mem_filter.mp this).2
      have h2 : p ∣ Pz z := dvd_Pz hp
      exact hpp.not_dvd_one (Nat.Coprime.gcd_eq_one hcop ▸ Nat.dvd_gcd h1 h2)
    have hS3 : S3 z H K = 0 := by
      unfold S3
      apply Finset.prod_eq_zero hp
      rw [hνeq]
      have : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
      rw [div_self this, sub_self, zero_div]
    rw [hzero, hS3]
    simp only [Nat.cast_zero, mul_zero, zero_add]
    positivity
  · push_neg at hdeg
    have hg : ∀ p ∈ primesLT z, 0 ≤ (nu3 H K p : ℝ) / p ∧ (nu3 H K p : ℝ) / p < 1 := by
      intro p hp
      have hpp := (mem_primesLT_sv.mp hp).1
      have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      refine ⟨by positivity, ?_⟩
      rw [div_lt_one hpR]; exact_mod_cast hdeg p hp
    have hg5 : ∀ p ∈ primesLT z, (1 - 1 / (p : ℝ)) ^ 5 ≤ 1 - (nu3 H K p : ℝ) / p :=
      fun p hp => pow5_nu (mem_primesLT_sv.mp hp).1 (nu3_le_three H K p) (hdeg p hp)
    obtain ⟨hup, -⟩ := hFL z s hz hs (range (⌊xq q⌋₊ + 1)) (F3 H K)
      (fun p => (nu3 H K p : ℝ) / p) (xq q) hx hg hg5
    rw [Vg3] at hup
    have hVg : 0 ≤ V z ^ 3 * S3 z H K := by
      rw [← Vg3]
      apply Finset.prod_nonneg
      intro p hp
      linarith [(hg p hp).2]
    have hsub : Qtrip q u H K
        ≤ ((range (⌊xq q⌋₊ + 1)).filter (fun n => Nat.Coprime (F3 H K n) (Pz z))).card := by
      rw [hQ]
      apply Finset.card_le_card
      apply Finset.filter_subset_filter
      intro n hn
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_range]; omega
    have hR : Rem z (z ^ s) (range (⌊xq q⌋₊ + 1)) (F3 H K) (fun p => (nu3 H K p : ℝ) / p) (xq q)
        ≤ 2 * (z ^ s) ^ 2 := by
      unfold Rem
      calc _ ≤ ∑ d ∈ (Pz z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ s), 2 * z ^ s := by
            apply Finset.sum_le_sum
            intro d hd
            have hd1 := (Finset.mem_filter.mp hd).1
            have hdD := (Finset.mem_filter.mp hd).2
            have hdpos : 0 < d := Nat.pos_of_mem_divisors hd1
            rw [prod_nu H K d (sqf_of_mem_divisors hd1)]
            refine (count_F3 H K d hdpos hx).trans ?_
            have : (rho H K d : ℝ) ≤ d := by exact_mod_cast rho_le H K d
            linarith
        _ = (((Pz z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ z ^ s)).card : ℝ) * (2 * z ^ s) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ z ^ s * (2 * z ^ s) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact (divisors_filter_card_le z _).trans (Nat.floor_le hD)
        _ = 2 * (z ^ s) ^ 2 := by ring
    have hsub' : (Qtrip q u H K : ℝ)
        ≤ ((range (⌊xq q⌋₊ + 1)).filter (fun n => Nat.Coprime (F3 H K n) (Pz z))).card := by
      exact_mod_cast hsub
    have hm : xq q * (V z ^ 3 * S3 z H K) * (1 + η s) ≤ 2 * xq q * V z ^ 3 * S3 z H K := by
      have : 0 ≤ xq q * (V z ^ 3 * S3 z H K) := mul_nonneg hx hVg
      nlinarith
    linarith


lemma xq_eventually_ge (B : ℝ) : ∀ᶠ q : ℕ in atTop, B ≤ xq q := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.exp B),
    eventually_ge_atTop 1] with q hq hq1
  have hlog : B ≤ Real.log q := by
    rw [← Real.log_exp B]; exact Real.log_le_log (Real.exp_pos B) hq
  have ht : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq1
  have hl0 : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  unfold xq
  nlinarith

lemma zq_ge_two {q u : ℕ} (hu : u ≠ 0) (hx : (2 : ℝ) ^ u ≤ xq q) : 2 ≤ zq q u := by
  unfold zq
  have h := Real.rpow_le_rpow (by positivity) hx (by positivity : (0 : ℝ) ≤ 1 / u)
  rwa [one_div, Real.pow_rpow_inv_natCast (by norm_num) hu, ← one_div] at h

lemma eventually_small {η : ℝ → ℝ} (hη : Tendsto (fun s => s * η s) atTop (𝓝 0)) :
    ∃ s₁ : ℝ, 1 ≤ s₁ ∧ ∀ s, s₁ ≤ s → η s ≤ 1 := by
  have h := hη.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨s₁, hs₁⟩ := Filter.eventually_atTop.mp h
  refine ⟨max s₁ 1, le_max_right _ _, fun s hs => ?_⟩
  have h1 := hs₁ s ((le_max_left _ _).trans hs)
  have h2 : 1 ≤ s := (le_max_right _ _).trans hs
  by_contra hc
  push_neg at hc
  nlinarith

theorem sieve_triple : ∃ u₀ : ℕ, ∀ u : ℕ, u₀ ≤ u → ∀ᶠ q : ℕ in atTop,
    ∀ h k : ℕ, 1 ≤ h → h < k → k ≤ Kq q →
      (Qtrip q u (h * q) (k * q) : ℝ)
        ≤ 2 * xq q * V (zq q u) ^ 3 * S3 (zq q u) (h * q) (k * q) + xq q ^ ((1 : ℝ) / 3) := by
  obtain ⟨η, hη, s₀, hFL⟩ := FL_setup
  obtain ⟨s₁, hs₁, hsm⟩ := eventually_small hη
  refine ⟨⌈8 * max s₀ s₁⌉₊ + 1, fun u hu => ?_⟩
  have hu0 : u ≠ 0 := by omega
  have hsu : max s₀ s₁ ≤ (u : ℝ) / 8 := by
    have h1 := Nat.le_ceil (8 * max s₀ s₁)
    have h2 : ((⌈8 * max s₀ s₁⌉₊ + 1 : ℕ) : ℝ) ≤ u := by exact_mod_cast hu
    push_cast at h2
    linarith
  filter_upwards [xq_eventually_ge ((2 : ℝ) ^ (u + 12))] with q hxq h k _ _ _
  have hx0 := xq_nonneg_sv q
  have hxu : (2 : ℝ) ^ u ≤ xq q :=
    le_trans (pow_le_pow_right₀ (by norm_num) (by omega)) hxq
  have hx12 : (2 : ℝ) ^ 12 ≤ xq q :=
    le_trans (pow_le_pow_right₀ (by norm_num) (by omega)) hxq
  have hz := zq_ge_two hu0 hxu
  have hmain := triple_bound hFL q u (h * q) (k * q) ((u : ℝ) / 8) hz
    ((le_max_left _ _).trans hsu) (hsm _ ((le_max_right _ _).trans hsu))
  have hlev : (zq q u ^ ((u : ℝ) / 8)) ^ 2 = xq q ^ ((1 : ℝ) / 4) := by
    unfold zq
    rw [show (u : ℝ) / 8 = u * (1 / 8) by ring, level_eq hx0 hu0, ← Real.rpow_natCast,
      ← Real.rpow_mul hx0]
    norm_num
  have hxpos : 0 < xq q := lt_of_lt_of_le (by norm_num) hx12
  have hsplit : xq q ^ ((1 : ℝ) / 3) = xq q ^ ((1 : ℝ) / 4) * xq q ^ ((1 : ℝ) / 12) := by
    rw [← Real.rpow_add hxpos]; norm_num
  have h12 : (2 : ℝ) ≤ xq q ^ ((1 : ℝ) / 12) := by
    rw [show (1 : ℝ) / 12 = ((12 : ℕ) : ℝ)⁻¹ by norm_num]
    have := Real.rpow_le_rpow (by positivity) hx12 (by positivity : (0 : ℝ) ≤ ((12 : ℕ) : ℝ)⁻¹)
    rwa [Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)] at this
  have h4 : 0 ≤ xq q ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hx0 _
  rw [hlev] at hmain
  nlinarith


/-- residue for `p + t`. -/
def bplus (t r : ℕ) : ℕ := if r ≠ 0 ∧ Nat.Coprime t r then (r - 1) * t else 1

/-- residue for `p - t`. -/
def bminus (t r : ℕ) : ℕ := if Nat.Coprime t r then t else 1

lemma bplus_coprime (t r : ℕ) : Nat.Coprime (bplus t r) r := by
  unfold bplus
  split_ifs with h
  · apply Nat.Coprime.mul_left _ h.2
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right s)
  · exact Nat.coprime_one_left r

lemma bminus_coprime (t r : ℕ) : Nat.Coprime (bminus t r) r := by
  unfold bminus
  split_ifs with h
  · exact h
  · exact Nat.coprime_one_left r

lemma modEq_bplus_iff {t d : ℕ} (hd : 0 < d) (p : ℕ) :
    p ≡ (d - 1) * t [MOD d] ↔ d ∣ p + t := by
  have e : (d - 1) * t + t = d * t := by
    obtain ⟨s, rfl⟩ : ∃ s, d = s + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  have h0 : d * t ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right d t)
  constructor
  · intro h
    have := (h.add_right t).trans (e ▸ h0 : (d - 1) * t + t ≡ 0 [MOD d])
    exact Nat.modEq_zero_iff_dvd.mp this
  · intro h
    apply Nat.ModEq.add_right_cancel' t
    rw [e]
    exact (Nat.modEq_zero_iff_dvd.mpr h).trans h0.symm

/-- The count behind `M_+`. -/
lemma count_plus (N t d b : ℕ) {z : ℝ} (hz : 0 ≤ z) (hzN : ⌊z⌋₊ ≤ N - t)
    (hb : ∀ p, p ≡ b [MOD d] ↔ d ∣ p + t) :
    (((Icc 1 N).filter (fun p : ℕ => p.Prime ∧ z < (p : ℝ) ∧ p + t ≤ N)).filter
        (fun p : ℕ => d ∣ p + t)).card
      + ((range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ b [MOD d])).card
      = ((range (N - t + 1)).filter (fun p => p.Prime ∧ p ≡ b [MOD d])).card := by
  conv_rhs => rw [← Finset.card_filter_add_card_filter_not (fun p : ℕ => z < (p : ℝ))]
  congr 1
  · apply congrArg Finset.card
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range, hb]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, hp, hzp, hpt⟩, hd⟩; exact ⟨⟨by omega, hp, hd⟩, hzp⟩
    · rintro ⟨⟨h1, hp, hd⟩, hzp⟩
      have := hp.one_le
      exact ⟨⟨⟨hp.one_le, by omega⟩, hp, hzp, by omega⟩, hd⟩
  · apply congrArg Finset.card
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, not_lt]
    constructor
    · rintro ⟨h1, hp, hd⟩
      exact ⟨⟨by omega, hp, hd⟩, (Nat.le_floor_iff hz).mp (by omega)⟩
    · rintro ⟨⟨h1, hp, hd⟩, hzp⟩
      exact ⟨Nat.lt_succ_of_le (Nat.le_floor hzp), hp, hd⟩

/-- The count behind `M_-`. -/
lemma count_minus (N t d : ℕ) (htN : t ≤ N) :
    (((Icc 1 N).filter (fun p => p.Prime ∧ t < p)).filter (fun p => d ∣ p - t)).card
      + ((range (t + 1)).filter (fun p => p.Prime ∧ p ≡ t [MOD d])).card
      = ((range (N + 1)).filter (fun p => p.Prime ∧ p ≡ t [MOD d])).card := by
  conv_rhs => rw [← Finset.card_filter_add_card_filter_not (fun p : ℕ => t < p)]
  congr 1
  · apply congrArg Finset.card
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, hp, htp⟩, hd⟩
      exact ⟨⟨by omega, hp, ((Nat.modEq_iff_dvd' htp.le).mpr hd).symm⟩, htp⟩
    · rintro ⟨⟨h1, hp, hd⟩, htp⟩
      exact ⟨⟨⟨hp.one_le, by omega⟩, hp, htp⟩, (Nat.modEq_iff_dvd' htp.le).mp hd.symm⟩
  · apply congrArg Finset.card
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, not_lt]
    constructor
    · rintro ⟨h1, hp, hd⟩; exact ⟨⟨by omega, hp, hd⟩, by omega⟩
    · rintro ⟨⟨h1, hp, hd⟩, htp⟩; exact ⟨by omega, hp, hd⟩


lemma gpair_ok {t : ℕ} (ht : 2 ∣ t) {p : ℕ} (hp : p.Prime) :
    (0 ≤ gpair t p ∧ gpair t p < 1) ∧ (1 - 1 / (p : ℝ)) ^ 5 ≤ 1 - gpair t p := by
  have h0 := one_sub_inv_pos_sv hp
  have h1 : 1 - 1 / (p : ℝ) ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / p := by have := hp.pos; positivity
    linarith
  have hle1 : (1 - 1 / (p : ℝ)) ^ 5 ≤ 1 := pow_le_one₀ h0.le h1
  unfold gpair
  split_ifs with hpt
  · refine ⟨⟨le_refl 0, by norm_num⟩, by linarith⟩
  · have hp3 : 3 ≤ p := by
      rcases hp.eq_two_or_odd' with h | h
      · exact absurd (h ▸ ht) hpt
      · have := hp.two_le
        rcases h with ⟨k, rfl⟩
        omega
    have hp3' : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have hpm : (0 : ℝ) < p - 1 := by linarith
    refine ⟨⟨by positivity, ?_⟩, pow5_pair hp3⟩
    rw [div_lt_one hpm]; linarith

lemma Vg2 (z : ℝ) (t : ℕ) : ∏ p ∈ primesLT z, (1 - gpair t p) = V z * S2 z t := by
  unfold V S2
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have := one_sub_inv_pos_sv (mem_primesLT_sv.mp hp).1
  field_simp

lemma S2_odd {z : ℝ} (hz : 2 < z) {t : ℕ} (ht : ¬ 2 ∣ t) : S2 z t = 0 := by
  unfold S2
  apply Finset.prod_eq_zero (i := 2) (mem_primesLT_sv.mpr ⟨Nat.prime_two, by exact_mod_cast hz⟩)
  unfold gpair
  rw [if_neg ht]
  norm_num

lemma gpair_prod_coprime {t d : ℕ} (hd : Squarefree d) (hc : Nat.Coprime t d) :
    ∏ p ∈ d.primeFactors, gpair t p = 1 / (d.totient : ℝ) := by
  rw [totient_sqf hd, one_div, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpt : ¬ p ∣ t := by
    intro h
    have h1 : p ∣ 1 := (Nat.Coprime.gcd_eq_one hc) ▸
      Nat.dvd_gcd h (Nat.dvd_of_mem_primeFactors hp)
    exact (Nat.prime_of_mem_primeFactors hp).not_dvd_one h1
  unfold gpair; rw [if_neg hpt, one_div]

lemma gpair_prod_not_coprime {t d : ℕ} (hd0 : d ≠ 0) (hc : ¬ Nat.Coprime t d) :
    ∃ ℓ, ℓ.Prime ∧ ℓ ∣ t ∧ ℓ ∣ d ∧ ∏ p ∈ d.primeFactors, gpair t p = 0 := by
  obtain ⟨ℓ, hℓ, hℓt, hℓd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  refine ⟨ℓ, hℓ, hℓt, hℓd, ?_⟩
  apply Finset.prod_eq_zero (Nat.mem_primeFactors.mpr ⟨hℓ, hℓd, hd0⟩)
  unfold gpair; rw [if_pos hℓt]

/-- One Bombieri–Vinogradov term. -/
noncomputable def bvT (y : ℝ) (b : ℕ → ℕ) (r : ℕ) : ℝ :=
  |(piAP y r (b r) : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ) / (r.totient : ℝ)|

/-- The Bombieri–Vinogradov sum. -/
noncomputable def bvS (x y : ℝ) (b : ℕ → ℕ) : ℝ :=
  ∑ r ∈ Icc 1 ⌊x ^ ((1 : ℝ) / 4)⌋₊, bvT y b r

lemma bvT_nonneg (y : ℝ) (b : ℕ → ℕ) (r : ℕ) : 0 ≤ bvT y b r := abs_nonneg _

lemma rem_plus_term {z x : ℝ} (hz : 0 ≤ z) {t d : ℕ} (hd : d ∈ (Pz z).divisors)
    (hzN : ⌊z⌋₊ ≤ ⌊x⌋₊ - t) :
    |((((Icc 1 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ z < (p : ℝ) ∧ p + t ≤ ⌊x⌋₊)).filter
        (fun p => d ∣ p + t)).card : ℝ)
      - ((Nat.primeCounting ⌊x - t⌋₊ : ℝ) - Nat.primeCounting ⌊z⌋₊) * ∏ p ∈ d.primeFactors, gpair t p|
      ≤ bvT (x - t) (bplus t) d + bvT z (bplus t) d := by
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  by_cases hc : Nat.Coprime t d
  · have hb : bplus t d = (d - 1) * t := by unfold bplus; rw [if_pos ⟨hd0, hc⟩]
    have hcount := count_plus ⌊x⌋₊ t d (bplus t d) hz hzN
      (fun p => by rw [hb]; exact modEq_bplus_iff (Nat.pos_of_ne_zero hd0) p)
    have e1 : (piAP (x - t) d (bplus t d) : ℝ) = ((range (⌊x⌋₊ - t + 1)).filter
        (fun p => p.Prime ∧ p ≡ bplus t d [MOD d])).card := by
      unfold piAP; rw [Nat.floor_sub_natCast]
    have e2 : (piAP z d (bplus t d) : ℝ) = ((range (⌊z⌋₊ + 1)).filter
        (fun p => p.Prime ∧ p ≡ bplus t d [MOD d])).card := rfl
    rw [gpair_prod_coprime (sqf_of_mem_divisors hd) hc]
    unfold bvT
    rw [e1, e2, ← hcount]
    push_cast
    have := abs_sub (((((Icc 1 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ z < (p : ℝ) ∧ p + t ≤ ⌊x⌋₊)).filter
        (fun p => d ∣ p + t)).card : ℝ) +
        (((range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ bplus t d [MOD d])).card : ℝ)
          - (Nat.primeCounting ⌊x - t⌋₊ : ℝ) / d.totient)
      ((((range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ bplus t d [MOD d])).card : ℝ)
          - (Nat.primeCounting ⌊z⌋₊ : ℝ) / d.totient)
    refine le_trans (le_of_eq ?_) this
    congr 1
    ring
  · obtain ⟨ℓ, hℓ, hℓt, hℓd, hprod⟩ := gpair_prod_not_coprime hd0 hc
    rw [hprod, mul_zero, sub_zero]
    have hempty : ((Icc 1 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ z < (p : ℝ) ∧ p + t ≤ ⌊x⌋₊)).filter
        (fun p => d ∣ p + t) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p hp hdp
      obtain ⟨-, hpp, hzp, -⟩ := Finset.mem_filter.mp hp
      have hℓp : ℓ ∣ p := (Nat.dvd_add_left hℓt).mp (hℓd.trans hdp)
      have hℓeq : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hpp).mp hℓp
      have hmem : ℓ ∈ primesLT z := prime_dvd_Pz hℓ (hℓd.trans (Nat.dvd_of_mem_divisors hd))
      have := (mem_primesLT_sv.mp hmem).2
      rw [hℓeq] at this
      linarith
    rw [hempty, Finset.card_empty, Nat.cast_zero, abs_zero]
    exact add_nonneg (bvT_nonneg _ _ _) (bvT_nonneg _ _ _)

lemma rem_minus_term {z x : ℝ} {t d : ℕ} (hd : d ∈ (Pz z).divisors) (ht1 : 1 ≤ t)
    (htN : t ≤ ⌊x⌋₊) :
    |((((Icc 1 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ t < p)).filter
        (fun p => d ∣ p - t)).card : ℝ)
      - ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Nat.primeCounting t) * ∏ p ∈ d.primeFactors, gpair t p|
      ≤ bvT x (bminus t) d + bvT t (bminus t) d := by
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  by_cases hc : Nat.Coprime t d
  · have hb : bminus t d = t := by unfold bminus; rw [if_pos hc]
    have hcount := count_minus ⌊x⌋₊ t d htN
    have e1 : (piAP x d (bminus t d) : ℝ) = ((range (⌊x⌋₊ + 1)).filter
        (fun p => p.Prime ∧ p ≡ t [MOD d])).card := by
      unfold piAP; rw [hb]
    have e2 : (piAP t d (bminus t d) : ℝ) = ((range (t + 1)).filter
        (fun p => p.Prime ∧ p ≡ t [MOD d])).card := by
      unfold piAP; rw [hb, Nat.floor_natCast]
    rw [gpair_prod_coprime (sqf_of_mem_divisors hd) hc]
    unfold bvT
    rw [e1, e2, ← hcount, Nat.floor_natCast]
    push_cast
    have := abs_sub (((((Icc 1 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ t < p)).filter
        (fun p => d ∣ p - t)).card : ℝ) +
        (((range (t + 1)).filter (fun p => p.Prime ∧ p ≡ t [MOD d])).card : ℝ)
          - (Nat.primeCounting ⌊x⌋₊ : ℝ) / d.totient)
      ((((range (t + 1)).filter (fun p => p.Prime ∧ p ≡ t [MOD d])).card : ℝ)
          - (Nat.primeCounting t : ℝ) / d.totient)
    refine le_trans (le_of_eq ?_) this
    congr 1
    ring
  · obtain ⟨ℓ, hℓ, hℓt, hℓd, hprod⟩ := gpair_prod_not_coprime hd0 hc
    rw [hprod, mul_zero, sub_zero]
    have hempty : ((Icc 1 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ t < p)).filter
        (fun p => d ∣ p - t) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p hp hdp
      obtain ⟨-, hpp, htp⟩ := Finset.mem_filter.mp hp
      have hℓp : ℓ ∣ p := by
        have h := Nat.dvd_add (hℓd.trans hdp) hℓt
        rwa [Nat.sub_add_cancel htp.le] at h
      have hℓeq : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hpp).mp hℓp
      have := Nat.le_of_dvd ht1 hℓt
      omega
    rw [hempty, Finset.card_empty, Nat.cast_zero, abs_zero]
    exact add_nonneg (bvT_nonneg _ _ _) (bvT_nonneg _ _ _)


lemma rem_le_bv {ι : Type} {z D x : ℝ} (hlev : D = x ^ ((1 : ℝ) / 4)) (A : Finset ι)
    (f : ι → ℕ) (g : ℕ → ℝ) (X : ℝ) (T : ℕ → ℝ) (hT0 : ∀ r, 0 ≤ T r)
    (hT : ∀ d ∈ (Pz z).divisors,
      |((A.filter (fun i => d ∣ f i)).card : ℝ) - X * ∏ p ∈ d.primeFactors, g p| ≤ T d) :
    Rem z D A f g X ≤ ∑ r ∈ Icc 1 ⌊x ^ ((1 : ℝ) / 4)⌋₊, T r := by
  unfold Rem
  refine (Finset.sum_le_sum fun d hd => hT d (Finset.mem_filter.mp hd).1).trans ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    rw [← hlev]
    exact mem_divisors_filter_le hd
  · intro r _ _; exact hT0 r

lemma Mplus_lower {η : ℝ → ℝ} {s₀ : ℝ}
    (hFL : ∀ z s : ℝ, 2 ≤ z → s₀ ≤ s →
    ∀ {ι : Type} (A : Finset ι) (f : ι → ℕ) (g : ℕ → ℝ) (X : ℝ), 0 ≤ X →
      (∀ p ∈ primesLT z, 0 ≤ g p ∧ g p < 1) →
      (∀ p ∈ primesLT z, (1 - 1 / (p : ℝ)) ^ 5 ≤ 1 - g p) →
      ((A.filter (fun i => Nat.Coprime (f i) (Pz z))).card : ℝ)
          ≤ X * (∏ p ∈ primesLT z, (1 - g p)) * (1 + η s) + Rem z (z ^ s) A f g X ∧
        X * (∏ p ∈ primesLT z, (1 - g p)) * (1 - η s) - Rem z (z ^ s) A f g X
          ≤ ((A.filter (fun i => Nat.Coprime (f i) (Pz z))).card : ℝ))
    (q u h : ℕ) (s : ℝ) (hz : 2 ≤ zq q u) (hs : s₀ ≤ s)
    (hlev : zq q u ^ s = xq q ^ ((1 : ℝ) / 4)) (heven : 2 ∣ h * q)
    (hzt : zq q u ≤ xq q - ((h * q : ℕ) : ℝ)) :
    (1 - η s) * V (zq q u) * S2 (zq q u) (h * q) *
      ((Nat.primeCounting ⌊xq q - ((h * q : ℕ) : ℝ)⌋₊ : ℝ) - Nat.primeCounting ⌊zq q u⌋₊)
      - (bvS (xq q) (xq q - ((h * q : ℕ) : ℝ)) (bplus (h * q))
          + bvS (xq q) (zq q u) (bplus (h * q)))
      ≤ Mplus q u h := by
  set t := h * q with ht
  set z := zq q u with hzdef
  set x := xq q with hxdef
  have hX : 0 ≤ (Nat.primeCounting ⌊x - t⌋₊ : ℝ) - Nat.primeCounting ⌊z⌋₊ :=
    sub_nonneg.mpr (Nat.cast_le.mpr (Nat.monotone_primeCounting (Nat.floor_le_floor hzt)))
  have hzN : ⌊z⌋₊ ≤ ⌊x⌋₊ - t := by
    rw [← Nat.floor_sub_natCast]; exact Nat.floor_le_floor hzt
  obtain ⟨-, hlo⟩ := hFL z s hz hs
    ((Icc 1 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ z < (p : ℝ) ∧ p + t ≤ ⌊x⌋₊))
    (fun p => p + t) (gpair t) ((Nat.primeCounting ⌊x - t⌋₊ : ℝ) - Nat.primeCounting ⌊z⌋₊) hX
    (fun p hp => (gpair_ok heven (mem_primesLT_sv.mp hp).1).1)
    (fun p hp => (gpair_ok heven (mem_primesLT_sv.mp hp).1).2)
  rw [Vg2] at hlo
  have hM : Mplus q u h = (((Icc 1 ⌊x⌋₊).filter
      (fun p : ℕ => p.Prime ∧ z < (p : ℝ) ∧ p + t ≤ ⌊x⌋₊)).filter
      (fun p => Nat.Coprime (p + t) (Pz z))).card := by
    unfold Mplus
    rw [Finset.filter_filter]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro p _
    tauto
  have hR : Rem z (z ^ s) ((Icc 1 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ z < (p : ℝ) ∧ p + t ≤ ⌊x⌋₊))
      (fun p => p + t) (gpair t) ((Nat.primeCounting ⌊x - t⌋₊ : ℝ) - Nat.primeCounting ⌊z⌋₊)
      ≤ bvS x (x - t) (bplus t) + bvS x z (bplus t) := by
    unfold bvS
    rw [← Finset.sum_add_distrib]
    apply rem_le_bv hlev
    · intro r; exact add_nonneg (bvT_nonneg _ _ _) (bvT_nonneg _ _ _)
    · intro d hd
      exact rem_plus_term (by linarith) hd hzN
  rw [hM]
  have e : ((Nat.primeCounting ⌊x - t⌋₊ : ℝ) - Nat.primeCounting ⌊z⌋₊) * (V z * S2 z t) * (1 - η s)
      = (1 - η s) * V z * S2 z t * ((Nat.primeCounting ⌊x - t⌋₊ : ℝ) - Nat.primeCounting ⌊z⌋₊) := by ring
  linarith

lemma Mminus_lower {η : ℝ → ℝ} {s₀ : ℝ}
    (hFL : ∀ z s : ℝ, 2 ≤ z → s₀ ≤ s →
    ∀ {ι : Type} (A : Finset ι) (f : ι → ℕ) (g : ℕ → ℝ) (X : ℝ), 0 ≤ X →
      (∀ p ∈ primesLT z, 0 ≤ g p ∧ g p < 1) →
      (∀ p ∈ primesLT z, (1 - 1 / (p : ℝ)) ^ 5 ≤ 1 - g p) →
      ((A.filter (fun i => Nat.Coprime (f i) (Pz z))).card : ℝ)
          ≤ X * (∏ p ∈ primesLT z, (1 - g p)) * (1 + η s) + Rem z (z ^ s) A f g X ∧
        X * (∏ p ∈ primesLT z, (1 - g p)) * (1 - η s) - Rem z (z ^ s) A f g X
          ≤ ((A.filter (fun i => Nat.Coprime (f i) (Pz z))).card : ℝ))
    (q u h : ℕ) (s : ℝ) (hz : 2 ≤ zq q u) (hs : s₀ ≤ s)
    (hlev : zq q u ^ s = xq q ^ ((1 : ℝ) / 4)) (heven : 2 ∣ h * q)
    (ht2 : (2 : ℝ) ≤ ((h * q : ℕ) : ℝ)) (htx : ((h * q : ℕ) : ℝ) ≤ xq q) :
    (1 - η s) * V (zq q u) * S2 (zq q u) (h * q) *
      ((Nat.primeCounting ⌊xq q⌋₊ : ℝ) - Nat.primeCounting (h * q))
      - (bvS (xq q) (xq q) (bminus (h * q)) + bvS (xq q) ((h * q : ℕ) : ℝ) (bminus (h * q)))
      ≤ Mminus q u h := by
  set t := h * q with ht
  set z := zq q u with hzdef
  set x := xq q with hxdef
  have htN : t ≤ ⌊x⌋₊ := Nat.le_floor htx
  have hX : 0 ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) - Nat.primeCounting t :=
    sub_nonneg.mpr (Nat.cast_le.mpr (Nat.monotone_primeCounting htN))
  have ht1 : 1 ≤ t := by
    have : (1 : ℝ) ≤ t := by linarith
    exact_mod_cast this
  obtain ⟨-, hlo⟩ := hFL z s hz hs
    ((Icc 1 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ t < p))
    (fun p => p - t) (gpair t) ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Nat.primeCounting t) hX
    (fun p hp => (gpair_ok heven (mem_primesLT_sv.mp hp).1).1)
    (fun p hp => (gpair_ok heven (mem_primesLT_sv.mp hp).1).2)
  rw [Vg2] at hlo
  have hM : Mminus q u h = (((Icc 1 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ t < p)).filter
      (fun p => Nat.Coprime (p - t) (Pz z))).card := by
    unfold Mminus
    rw [Finset.filter_filter]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro p _
    tauto
  have hR : Rem z (z ^ s) ((Icc 1 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ t < p))
      (fun p => p - t) (gpair t) ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Nat.primeCounting t)
      ≤ bvS x x (bminus t) + bvS x t (bminus t) := by
    unfold bvS
    rw [← Finset.sum_add_distrib]
    apply rem_le_bv hlev
    · intro r; exact add_nonneg (bvT_nonneg _ _ _) (bvT_nonneg _ _ _)
    · intro d hd
      exact rem_minus_term hd ht1 htN
  rw [hM]
  have e : ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Nat.primeCounting t) * (V z * S2 z t) * (1 - η s)
      = (1 - η s) * V z * S2 z t * ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Nat.primeCounting t) := by ring
  linarith


lemma zq_ge {q u : ℕ} (hu : u ≠ 0) {c : ℝ} (hc : 0 ≤ c) (hx : c ^ u ≤ xq q) : c ≤ zq q u := by
  unfold zq
  have h := Real.rpow_le_rpow (by positivity) hx (by positivity : (0 : ℝ) ≤ 1 / u)
  rwa [one_div, Real.pow_rpow_inv_natCast hc hu, ← one_div] at h

lemma xq_le_sq (q : ℕ) : xq q ≤ (q : ℝ) ^ 2 := by
  unfold xq
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog : Real.log q ≤ q := by linarith [Real.log_le_sub_one_of_pos hq']
  have ht : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hl0 := Real.log_natCast_nonneg q
  have ht0 : (0 : ℝ) ≤ q.totient := Nat.cast_nonneg _
  calc (q.totient : ℝ) * Real.log q ≤ q * q := mul_le_mul ht hlog hl0 hq'.le
    _ = (q : ℝ) ^ 2 := by ring

lemma zq_le_q {q u : ℕ} (hu : 2 ≤ u) (hq : 1 ≤ q) : zq q u ≤ q := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hxu : xq q ≤ (q : ℝ) ^ u :=
    (xq_le_sq q).trans (pow_le_pow_right₀ hq1 hu)
  unfold zq
  have h := Real.rpow_le_rpow (xq_nonneg_sv q) hxu (by positivity : (0 : ℝ) ≤ 1 / u)
  rwa [one_div, Real.pow_rpow_inv_natCast (by linarith) (by omega), ← one_div] at h

lemma xq_div_le_log (q : ℕ) (hq : 0 < q) : xq q / q ≤ Real.log q := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [div_le_iff₀ hq']
  unfold xq
  have ht : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hl0 := Real.log_natCast_nonneg q
  nlinarith

lemma bvS_nonneg (x y : ℝ) (b : ℕ → ℕ) : 0 ≤ bvS x y b :=
  Finset.sum_nonneg fun r _ => bvT_nonneg y b r

lemma err_alg {C L x k : ℝ} (hL : 0 < L) (hx : 0 ≤ x) (hk : k ≤ L) (hC : 4 * C ≤ L)
    (hB : 0 ≤ C * x / L ^ 4) : k * (4 * (C * x / L ^ 4)) ≤ x / L ^ 2 := by
  calc k * (4 * (C * x / L ^ 4)) ≤ L * (4 * (C * x / L ^ 4)) :=
        mul_le_mul_of_nonneg_right hk (by linarith)
    _ = (4 * C * x) / L ^ 3 := by field_simp
    _ ≤ (L * x) / L ^ 3 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC hx) (by positivity)
    _ = x / L ^ 2 := by field_simp

lemma per_h {η : ℝ → ℝ} {s₀ C : ℝ}
    (hFL : ∀ z s : ℝ, 2 ≤ z → s₀ ≤ s →
    ∀ {ι : Type} (A : Finset ι) (f : ι → ℕ) (g : ℕ → ℝ) (X : ℝ), 0 ≤ X →
      (∀ p ∈ primesLT z, 0 ≤ g p ∧ g p < 1) →
      (∀ p ∈ primesLT z, (1 - 1 / (p : ℝ)) ^ 5 ≤ 1 - g p) →
      ((A.filter (fun i => Nat.Coprime (f i) (Pz z))).card : ℝ)
          ≤ X * (∏ p ∈ primesLT z, (1 - g p)) * (1 + η s) + Rem z (z ^ s) A f g X ∧
        X * (∏ p ∈ primesLT z, (1 - g p)) * (1 - η s) - Rem z (z ^ s) A f g X
          ≤ ((A.filter (fun i => Nat.Coprime (f i) (Pz z))).card : ℝ))
    (hC : ∀ x : ℝ, 2 ≤ x → ∀ y : ℝ, 2 ≤ y → y ≤ x → ∀ b : ℕ → ℕ,
      (∀ r, Nat.Coprime (b r) r) →
      ∑ r ∈ Finset.Icc 1 ⌊x ^ ((1 : ℝ) / 4)⌋₊,
          |(piAP y r (b r) : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ) / (r.totient : ℝ)|
        ≤ C * x / (Real.log x) ^ (4 : ℝ))
    (q u h : ℕ) (s : ℝ) (hz3 : 3 ≤ zq q u) (hs : s₀ ≤ s)
    (hlev : zq q u ^ s = xq q ^ ((1 : ℝ) / 4)) (hh1 : 1 ≤ h)
    (hhx : ((h : ℝ) + 1) * q ≤ xq q) (hzq : zq q u ≤ q) :
    (1 - η s) * V (zq q u) * (S2 (zq q u) (h * q) *
        (((Nat.primeCounting ⌊xq q - h * q⌋₊ : ℝ) - Nat.primeCounting ⌊zq q u⌋₊)
              + ((Nat.primeCounting ⌊xq q⌋₊ : ℝ) - Nat.primeCounting (h * q))))
      - 4 * (C * xq q / Real.log (xq q) ^ 4)
      ≤ (Mplus q u h : ℝ) + Mminus q u h := by
  set z := zq q u
  set x := xq q
  have hh1' : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have htc : ((h * q : ℕ) : ℝ) = (h : ℝ) * q := by push_cast; ring
  have ht2 : (2 : ℝ) ≤ (h : ℝ) * q := by nlinarith
  have htx : (h : ℝ) * q ≤ x := by nlinarith
  have hxt : (q : ℝ) ≤ x - h * q := by nlinarith
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have bv : ∀ y : ℝ, 2 ≤ y → y ≤ x → ∀ b : ℕ → ℕ, (∀ r, Nat.Coprime (b r) r) →
      bvS x y b ≤ C * x / Real.log x ^ 4 := by
    intro y hy hyx b hb
    have := hC x hx2 y hy hyx b hb
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    exact this
  have b1 := bv (x - h * q) (by linarith) (by linarith) (bplus (h * q)) (bplus_coprime _)
  have b2 := bv z (by linarith) (by linarith) (bplus (h * q)) (bplus_coprime _)
  have b3 := bv x hx2 le_rfl (bminus (h * q)) (bminus_coprime _)
  have b4 := bv ((h : ℝ) * q) ht2 htx (bminus (h * q)) (bminus_coprime _)
  have n1 := bvS_nonneg x (x - h * q) (bplus (h * q))
  have n2 := bvS_nonneg x z (bplus (h * q))
  have n3 := bvS_nonneg x x (bminus (h * q))
  have n4 := bvS_nonneg x ((h : ℝ) * q) (bminus (h * q))
  have m1 : (0 : ℝ) ≤ Mplus q u h := Nat.cast_nonneg _
  have m2 : (0 : ℝ) ≤ Mminus q u h := Nat.cast_nonneg _
  by_cases heven : 2 ∣ h * q
  · have hp := Mplus_lower hFL q u h s (by linarith) hs hlev heven (by rw [htc]; linarith)
    have hm := Mminus_lower hFL q u h s (by linarith) hs hlev heven (by rw [htc]; exact ht2)
      (by rw [htc]; exact htx)
    rw [htc] at hp hm
    have e : (1 - η s) * V z * (S2 z (h * q) *
          (((Nat.primeCounting ⌊x - h * q⌋₊ : ℝ) - Nat.primeCounting ⌊z⌋₊)
            + ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Nat.primeCounting (h * q))))
        = (1 - η s) * V z * S2 z (h * q) * ((Nat.primeCounting ⌊x - h * q⌋₊ : ℝ) - Nat.primeCounting ⌊z⌋₊)
          + (1 - η s) * V z * S2 z (h * q) * ((Nat.primeCounting ⌊x⌋₊ : ℝ) - Nat.primeCounting (h * q)) := by ring
    rw [e]
    linarith
  · rw [S2_odd (by linarith) heven]
    simp only [zero_mul, mul_zero, zero_sub]
    linarith


theorem sieve_dim1 : ∃ η : ℝ → ℝ, Tendsto (fun s => s * η s) atTop (𝓝 0) ∧
    ∃ u₀ : ℕ, ∀ u : ℕ, u₀ ≤ u →
      (∀ᶠ q : ℕ in atTop,
        (∑ a ∈ reduced q, (Wc q u a : ℝ))
          ≤ (1 + η (u / 4)) * xq q * V (zq q u) + xq q ^ ((1 : ℝ) / 4)) ∧
      (∀ᶠ q : ℕ in atTop,
        (1 - η (u / 4)) * V (zq q u) * ∑ h ∈ Ico 1 (Kq q), S2 (zq q u) (h * q) *
            (((Nat.primeCounting ⌊xq q - h * q⌋₊ : ℝ) - Nat.primeCounting ⌊zq q u⌋₊)
              + ((Nat.primeCounting ⌊xq q⌋₊ : ℝ) - Nat.primeCounting (h * q)))
          - xq q / (Real.log (xq q)) ^ 2
          ≤ ∑ h ∈ Ico 1 (Kq q), ((Mplus q u h : ℝ) + Mminus q u h)) := by
  obtain ⟨η, hη, s₀, hFL⟩ := FL_setup
  obtain ⟨C, hC⟩ := bv_pi 4 (by norm_num)
  refine ⟨η, hη, ⌈4 * s₀⌉₊ + 2, fun u hu => ?_⟩
  have hu0 : u ≠ 0 := by omega
  have hu2 : 2 ≤ u := by omega
  have hs : s₀ ≤ (u : ℝ) / 4 := by
    have h1 := Nat.le_ceil (4 * s₀)
    have h2 : ((⌈4 * s₀⌉₊ + 2 : ℕ) : ℝ) ≤ u := by exact_mod_cast hu
    push_cast at h2
    linarith
  constructor
  · filter_upwards [xq_eventually_ge ((2 : ℝ) ^ u), eventually_ge_atTop 1] with q hx hq
    exact first_moment hFL q u hq hu0 (zq_ge_two hu0 hx) hs
  · set C' := max C 1
    filter_upwards [xq_eventually_ge ((3 : ℝ) ^ u), eventually_ge_atTop 2,
      tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.exp (4 * C'))] with q hx3 hq2 hqe
    have hz3 : 3 ≤ zq q u := zq_ge hu0 (by norm_num) hx3
    have hzq : zq q u ≤ q := zq_le_q hu2 (by omega)
    have hx0 := xq_nonneg_sv q
    have hlev : zq q u ^ ((u : ℝ) / 4) = xq q ^ ((1 : ℝ) / 4) := by
      unfold zq; rw [show (u : ℝ) / 4 = u * (1 / 4) by ring, level_eq hx0 hu0]
    have hq0 : (0 : ℝ) < q := by
      have : (2 : ℝ) ≤ q := by exact_mod_cast hq2
      linarith
    by_cases hK : Kq q ≤ 1
    · rw [Finset.Ico_eq_empty_of_le hK, Finset.sum_empty, Finset.sum_empty, mul_zero, zero_sub]
      have : 0 ≤ xq q / Real.log (xq q) ^ 2 := by positivity
      linarith
    · push_neg at hK
      have hKx : (Kq q : ℝ) ≤ xq q / q := Nat.floor_le (by positivity)
      have hK2 : (2 : ℝ) ≤ Kq q := by exact_mod_cast hK
      have hxq : 2 * (q : ℝ) ≤ xq q := by
        have := (le_div_iff₀ hq0).mp (hK2.trans hKx); linarith
      have hKlog : (Kq q : ℝ) ≤ Real.log q := hKx.trans (xq_div_le_log q (by omega))
      have hlogq : Real.log q ≤ Real.log (xq q) := Real.log_le_log hq0 (by linarith)
      have hL : 0 < Real.log (xq q) := Real.log_pos (by linarith)
      have hC' : 4 * C' ≤ Real.log q := by
        rw [← Real.log_exp (4 * C')]; exact Real.log_le_log (Real.exp_pos _) hqe
      have hper : ∀ h ∈ Ico 1 (Kq q),
          (1 - η (u / 4)) * V (zq q u) * (S2 (zq q u) (h * q) *
            (((Nat.primeCounting ⌊xq q - h * q⌋₊ : ℝ) - Nat.primeCounting ⌊zq q u⌋₊)
              + ((Nat.primeCounting ⌊xq q⌋₊ : ℝ) - Nat.primeCounting (h * q))))
            - 4 * (C * xq q / Real.log (xq q) ^ 4)
          ≤ (Mplus q u h : ℝ) + Mminus q u h := by
        intro h hh
        rw [Finset.mem_Ico] at hh
        have hhK : ((h : ℝ) + 1) ≤ Kq q := by exact_mod_cast hh.2
        have hhx : ((h : ℝ) + 1) * q ≤ xq q := by
          have := hhK.trans hKx
          rwa [le_div_iff₀ hq0] at this
        exact per_h hFL hC q u h ((u : ℝ) / 4) hz3 hs hlev hh.1 hhx hzq
      have hsum := Finset.sum_le_sum hper
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Ico,
        nsmul_eq_mul] at hsum
      -- the error term
      have hB : 0 ≤ C * xq q / Real.log (xq q) ^ 4 := by
        have h1 : bvS (xq q) (xq q) (bminus 2) ≤ C * xq q / Real.log (xq q) ^ 4 := by
          have := hC (xq q) (by linarith) (xq q) (by linarith) le_rfl (bminus 2) (bminus_coprime 2)
          rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
          exact this
        exact (bvS_nonneg _ _ _).trans h1
      have hB' : C * xq q / Real.log (xq q) ^ 4 ≤ C' * xq q / Real.log (xq q) ^ 4 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hx0
      have hcast : ((Kq q - 1 : ℕ) : ℝ) ≤ Real.log (xq q) := by
        have : ((Kq q - 1 : ℕ) : ℝ) ≤ Kq q := by exact_mod_cast Nat.sub_le _ _
        linarith
      have herr := err_alg hL hx0 hcast (hC'.trans hlogq) (hB.trans hB')
      have hmono : ((Kq q - 1 : ℕ) : ℝ) * (4 * (C * xq q / Real.log (xq q) ^ 4))
          ≤ ((Kq q - 1 : ℕ) : ℝ) * (4 * (C' * xq q / Real.log (xq q) ^ 4)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      have e : η (u / 4) = η ((u : ℝ) / 4) := rfl
      linarith

end Erdos971
