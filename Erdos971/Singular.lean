import Erdos971.Defs

/-!
# Finite singular-series estimates (BLUEPRINT §3). No axioms.
-/

open Real Finset Filter Topology

namespace Erdos971

lemma prime_of_mem_primesLT {z : ℝ} {p : ℕ} (hp : p ∈ primesLT z) : p.Prime := by
  unfold primesLT at hp; exact (mem_filter.1 hp).2.1

lemma one_sub_inv_pos {p : ℕ} (hp : p.Prime) : 0 < 1 - 1 / (p : ℝ) := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [sub_pos, div_lt_one (by linarith)]; linarith

theorem S2_nonneg (z : ℝ) (t : ℕ) : 0 ≤ S2 z t := by
  unfold S2
  refine prod_nonneg fun p hp => ?_
  have hpp := prime_of_mem_primesLT hp
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
  refine div_nonneg ?_ (one_sub_inv_pos hpp).le
  unfold gpair
  split_ifs
  · norm_num
  · rw [sub_nonneg, div_le_one (by linarith)]; linarith

theorem S3_nonneg (z : ℝ) (h k : ℕ) : 0 ≤ S3 z h k := by
  unfold S3
  refine prod_nonneg fun p hp => ?_
  have hpp := prime_of_mem_primesLT hp
  have h2 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  refine div_nonneg ?_ (pow_nonneg (one_sub_inv_pos hpp).le _)
  have : nu3 h k p ≤ p := by
    unfold nu3
    calc _ ≤ (range p).card := card_le_card (by
            intro x hx
            simp only [mem_insert, mem_singleton] at hx
            rw [mem_range]
            rcases hx with rfl | rfl | rfl
            · exact hpp.pos
            · exact Nat.mod_lt _ hpp.pos
            · exact Nat.mod_lt _ hpp.pos)
      _ = p := card_range p
  rw [sub_nonneg, div_le_one h2]; exact_mod_cast this


lemma prod_ite_dvd (r : Finset ℕ) (hr : ∀ p ∈ r, p.Prime) (n : ℕ) (x : ℕ → ℝ) :
    ∏ p ∈ r, (if p ∣ n then x p else 0) = if (∏ p ∈ r, p) ∣ n then ∏ p ∈ r, x p else 0 := by
  have key : (∀ p ∈ r, p ∣ n) ↔ (∏ p ∈ r, p) ∣ n :=
    ⟨fun h => Finset.prod_primes_dvd n (fun a ha => (hr a ha).prime) h,
     fun h p hp => (dvd_prod_of_mem _ hp).trans h⟩
  rw [prod_ite_zero]
  by_cases h : (∏ p ∈ r, p) ∣ n
  · rw [if_pos (key.2 h), if_pos h]
  · rw [if_neg (fun h' => h (key.1 h')), if_neg h]

/-- `(p/(p-1))^2`. -/
noncomputable def cfac (p : ℕ) : ℝ := ((p : ℝ) / ((p : ℝ) - 1)) ^ 2

lemma one_le_cfac {p : ℕ} (hp : p.Prime) : 1 ≤ cfac p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold cfac
  have : 1 ≤ (p : ℝ) / ((p : ℝ) - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
  nlinarith

/-- `E n = ∏_{p ∣ n} (p/(p-1))^2`. -/
noncomputable def Efn (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, cfac p

lemma Efn_nonneg (n : ℕ) : 0 ≤ Efn n :=
  prod_nonneg fun _ hp => le_trans zero_le_one (one_le_cfac (Nat.prime_of_mem_primeFactors hp))

lemma S3_factor_nonneg {p : ℕ} (hpp : p.Prime) (h k : ℕ) :
    0 ≤ (1 - (nu3 h k p : ℝ) / p) / (1 - 1 / (p : ℝ)) ^ 3 := by
  have h2 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  refine div_nonneg ?_ (pow_nonneg (one_sub_inv_pos hpp).le _)
  have : nu3 h k p ≤ p := by
    unfold nu3
    calc _ ≤ (range p).card := card_le_card (by
            intro x hx
            simp only [mem_insert, mem_singleton] at hx
            rw [mem_range]
            rcases hx with rfl | rfl | rfl
            · exact hpp.pos
            · exact Nat.mod_lt _ hpp.pos
            · exact Nat.mod_lt _ hpp.pos)
      _ = p := card_range p
  rw [sub_nonneg, div_le_one h2]; exact_mod_cast this

lemma le_prod4 {a b c d x : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hx : x ≤ a ∨ x ≤ b ∨ x ≤ c ∨ x ≤ d) : x ≤ a * b * c * d := by
  have hab : 1 ≤ a * b := one_le_mul_of_one_le_of_one_le ha hb
  have habc : 1 ≤ a * b * c := one_le_mul_of_one_le_of_one_le hab hc
  have h1 : a ≤ a * b * c * d := by
    calc a ≤ a * b := le_mul_of_one_le_right (by linarith) hb
      _ ≤ a * b * c := le_mul_of_one_le_right (by linarith) hc
      _ ≤ _ := le_mul_of_one_le_right (by linarith) hd
  have h2 : b ≤ a * b * c * d := by
    calc b ≤ a * b := le_mul_of_one_le_left (by linarith) ha
      _ ≤ a * b * c := le_mul_of_one_le_right (by linarith) hc
      _ ≤ _ := le_mul_of_one_le_right (by linarith) hd
  have h3 : c ≤ a * b * c * d := by
    calc c ≤ a * b * c := le_mul_of_one_le_left (by linarith) hab
      _ ≤ _ := le_mul_of_one_le_right (by linarith) hd
  have h4 : d ≤ a * b * c * d := le_mul_of_one_le_left (by linarith) habc
  rcases hx with hx | hx | hx | hx <;> linarith

lemma S3_factor_le {p : ℕ} (hp : p.Prime) (q h k : ℕ) (_hhk : h < k) :
    (1 - (nu3 (h * q) (k * q) p : ℝ) / p) / (1 - 1 / (p : ℝ)) ^ 3 ≤
      (if p ∣ q then cfac p else 1) * (if p ∣ h then cfac p else 1) *
        (if p ∣ k then cfac p else 1) * (if p ∣ (k - h) then cfac p else 1) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos := one_sub_inv_pos hp
  have hc := one_le_cfac hp
  have hi : ∀ P : Prop, [Decidable P] → 1 ≤ (if P then cfac p else 1) := by
    intro P _; split_ifs <;> linarith
  by_cases hd : p ∣ q ∨ p ∣ h ∨ p ∣ k ∨ p ∣ (k - h)
  · -- the factor is at most cfac p
    have hnu : 1 ≤ nu3 (h * q) (k * q) p := by
      unfold nu3; exact card_pos.2 ⟨0, mem_insert_self _ _⟩
    have hle : (1 - (nu3 (h * q) (k * q) p : ℝ) / p) / (1 - 1 / (p : ℝ)) ^ 3 ≤ cfac p := by
      have e : cfac p = (1 - 1 / (p : ℝ)) / (1 - 1 / (p : ℝ)) ^ 3 := by
        unfold cfac
        have : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp
      rw [e]
      apply div_le_div_of_nonneg_right _ (pow_nonneg hpos.le _)
      have : (1 : ℝ) ≤ nu3 (h * q) (k * q) p := by exact_mod_cast hnu
      have : (1 : ℝ) / p ≤ (nu3 (h * q) (k * q) p : ℝ) / p :=
        div_le_div_of_nonneg_right this (by linarith)
      linarith
    refine le_prod4 (hi _) (hi _) (hi _) (hi _) ?_
    rcases hd with hd | hd | hd | hd
    · left; rw [if_pos hd]; exact hle
    · right; left; rw [if_pos hd]; exact hle
    · right; right; left; rw [if_pos hd]; exact hle
    · right; right; right; rw [if_pos hd]; exact hle
  · push_neg at hd
    obtain ⟨hq, hh, hk, hkh⟩ := hd
    have hA : (h * q) % p ≠ 0 := by
      intro e
      rcases (Nat.Prime.dvd_mul hp).1 (Nat.dvd_of_mod_eq_zero e) with e' | e'
      · exact hh e'
      · exact hq e'
    have hB : (k * q) % p ≠ 0 := by
      intro e
      rcases (Nat.Prime.dvd_mul hp).1 (Nat.dvd_of_mod_eq_zero e) with e' | e'
      · exact hk e'
      · exact hq e'
    have hAB : (h * q) % p ≠ (k * q) % p := by
      intro e
      have : p ∣ k * q - h * q := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq e.symm)
      rw [← Nat.sub_mul] at this
      rcases (Nat.Prime.dvd_mul hp).1 this with e' | e'
      · exact hkh e'
      · exact hq e'
    have hnu : nu3 (h * q) (k * q) p = 3 := by
      unfold nu3
      rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      · simpa using hAB
      · simp only [mem_insert, mem_singleton, not_or]; exact ⟨fun e => hA e.symm, fun e => hB e.symm⟩
    rw [hnu]
    have hone : (1 - ((3 : ℕ) : ℝ) / p) / (1 - 1 / (p : ℝ)) ^ 3 ≤ 1 := by
      rw [div_le_one (pow_pos hpos _)]
      have hy : 0 < 1 / (p : ℝ) := by positivity
      have hy2 : 1 / (p : ℝ) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      have e3 : ((3 : ℕ) : ℝ) / p = 3 * (1 / (p : ℝ)) := by push_cast; ring
      rw [e3]
      nlinarith [sq_nonneg (1 / (p : ℝ)), mul_pos hy hy, mul_pos (mul_pos hy hy) hy]
    have := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (hi (p ∣ q)) (hi (p ∣ h))) (hi (p ∣ k))) (hi (p ∣ (k - h)))
    linarith

lemma prod_ite_cfac_le (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ A, (if p ∣ n then cfac p else 1) ≤ Efn n := by
  rw [← prod_filter]
  unfold Efn
  apply prod_le_prod_of_subset_of_one_le
  · intro p hp
    rw [mem_filter] at hp
    exact Nat.mem_primeFactors.2 ⟨hA p hp.1, hp.2, hn⟩
  · intro p hp; exact le_trans zero_le_one (one_le_cfac (hA p (mem_filter.1 hp).1))
  · intro p hp _; exact one_le_cfac (Nat.prime_of_mem_primeFactors hp)

lemma S3_le (q : ℕ) (z : ℝ) {h k : ℕ} (hh : 1 ≤ h) (hhk : h < k) :
    S3 z (h * q) (k * q) ≤ Qz q z ^ 2 * Efn h * Efn k * Efn (k - h) := by
  unfold S3
  have hP : ∀ p ∈ primesLT z, p.Prime := fun p hp => prime_of_mem_primesLT hp
  calc _ ≤ ∏ p ∈ primesLT z, ((if p ∣ q then cfac p else 1) * (if p ∣ h then cfac p else 1) *
        (if p ∣ k then cfac p else 1) * (if p ∣ (k - h) then cfac p else 1)) :=
        prod_le_prod (fun p hp => S3_factor_nonneg (hP p hp) _ _)
          (fun p hp => S3_factor_le (hP p hp) q h k hhk)
    _ = (∏ p ∈ primesLT z, (if p ∣ q then cfac p else 1)) *
          (∏ p ∈ primesLT z, (if p ∣ h then cfac p else 1)) *
          (∏ p ∈ primesLT z, (if p ∣ k then cfac p else 1)) *
          (∏ p ∈ primesLT z, (if p ∣ (k - h) then cfac p else 1)) := by
        simp only [prod_mul_distrib]
    _ ≤ Qz q z ^ 2 * Efn h * Efn k * Efn (k - h) := by
        have eq : ∏ p ∈ primesLT z, (if p ∣ q then cfac p else 1) = Qz q z ^ 2 := by
          rw [← prod_filter]; unfold Qz cfac; rw [prod_pow]
        rw [eq]
        have n1 := prod_ite_cfac_le (primesLT z) hP (n := h) (by omega)
        have n2 := prod_ite_cfac_le (primesLT z) hP (n := k) (by omega)
        have n3 := prod_ite_cfac_le (primesLT z) hP (n := k - h) (by omega)
        have z1 : ∀ n, 0 ≤ ∏ p ∈ primesLT z, (if p ∣ n then cfac p else 1) := fun n =>
          prod_nonneg fun p hp => by
            have := one_le_cfac (hP p hp); split_ifs <;> linarith
        have e1 := Efn_nonneg h
        have e2 := Efn_nonneg k
        have q2 : 0 ≤ Qz q z ^ 2 := sq_nonneg _
        exact mul_le_mul (mul_le_mul (mul_le_mul le_rfl n1 (z1 _) q2) n2 (z1 _)
          (mul_nonneg q2 e1)) n3 (z1 _) (mul_nonneg (mul_nonneg q2 e1) e2)

lemma cfac_cube_sub_one_le {p : ℕ} (hp : p.Prime) :
    (cfac p ^ 3 - 1) / p ≤ 126 * (1 / (p : ℝ) ^ 2) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  set y : ℝ := (p : ℝ) / ((p : ℝ) - 1) with hy
  have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ (by linarith)]; linarith
  have hy2 : y ≤ 2 := by rw [hy, div_le_iff₀ (by linarith)]; linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hym : y - 1 = 1 / ((p : ℝ) - 1) := by rw [hy, div_sub_one hp1]; congr 1; ring
  have hc : cfac p ^ 3 = y ^ 6 := by unfold cfac; rw [← hy]; ring
  have h63 : y ^ 6 - 1 ≤ 63 * (y - 1) := by
    have hs : y ^ 5 + y ^ 4 + y ^ 3 + y ^ 2 + y + 1 ≤ 63 := by
      have a1 : y ^ 2 ≤ 4 := by nlinarith
      have a2 : y ^ 3 ≤ 8 := by nlinarith
      have a3 : y ^ 4 ≤ 16 := by nlinarith
      have a4 : y ^ 5 ≤ 32 := by nlinarith
      linarith
    have : y ^ 6 - 1 = (y - 1) * (y ^ 5 + y ^ 4 + y ^ 3 + y ^ 2 + y + 1) := by ring
    rw [this]; nlinarith
  have hq : y - 1 ≤ 2 / p := by
    rw [hym, div_le_div_iff₀ (by linarith) (by linarith)]; linarith
  rw [hc, div_le_iff₀ (by linarith)]
  have : 126 * (1 / (p : ℝ) ^ 2) * p = 126 / p := by field_simp
  rw [this]
  have : 63 * (y - 1) ≤ 126 / p := by
    have := mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 63)
    rw [show (63 : ℝ) * (2 / p) = 126 / p by ring] at this; exact this
  linarith

lemma sum_Efn_cube_le (K : ℕ) :
    ∑ n ∈ Icc 1 K, Efn n ^ 3 ≤ Real.exp (126 * (π ^ 2 / 6)) * K := by
  set P : Finset ℕ := (range (K + 1)).filter Nat.Prime with hPdef
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (mem_filter.1 hp).2
  set g : ℕ → ℝ := fun p => cfac p ^ 3 - 1 with hg
  have hg0 : ∀ p ∈ P, 0 ≤ g p := by
    intro p hp
    have := one_le_cfac (hP p hp)
    simp only [hg]; nlinarith [one_le_pow₀ this (n := 3)]
  -- expansion
  have hexp : ∀ n ∈ Icc 1 K, Efn n ^ 3 =
      ∑ r ∈ P.powerset, if (∏ p ∈ r, p) ∣ n then ∏ p ∈ r, g p else 0 := by
    intro n hn
    rw [mem_Icc] at hn
    have hpf : n.primeFactors = P.filter (· ∣ n) := by
      ext p
      simp only [Nat.mem_primeFactors, hPdef, mem_filter, mem_range]
      constructor
      · rintro ⟨pp, hd, hn0⟩
        exact ⟨⟨by have := Nat.le_of_dvd (by omega) hd; omega, pp⟩, hd⟩
      · rintro ⟨⟨_, pp⟩, hd⟩; exact ⟨pp, hd, by omega⟩
    unfold Efn
    rw [← prod_pow, hpf, prod_filter]
    have : ∀ p ∈ P, (if p ∣ n then cfac p ^ 3 else 1) = (if p ∣ n then g p else 0) + 1 := by
      intro p _; simp only [hg]; split_ifs <;> ring
    rw [prod_congr rfl this, prod_add_one]
    exact sum_congr rfl fun r hr => prod_ite_dvd r (fun p hp => hP p (mem_powerset.1 hr hp)) n g
  rw [sum_congr rfl hexp, sum_comm]
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  calc ∑ r ∈ P.powerset, ∑ n ∈ Icc 1 K, (if (∏ p ∈ r, p) ∣ n then ∏ p ∈ r, g p else 0)
      ≤ ∑ r ∈ P.powerset, (K : ℝ) * ∏ p ∈ r, (g p / p) := by
        apply sum_le_sum
        intro r hr
        have hr' : ∀ p ∈ r, p.Prime := fun p hp => hP p (mem_powerset.1 hr hp)
        have hG : 0 ≤ ∏ p ∈ r, g p := prod_nonneg fun p hp => hg0 p (mem_powerset.1 hr hp)
        have hd0 : (0 : ℝ) < ∏ p ∈ r, (p : ℝ) :=
          prod_pos fun p hp => by exact_mod_cast (hr' p hp).pos
        rw [← sum_filter, sum_const, nsmul_eq_mul]
        have hcard : ((Icc 1 K).filter (fun n => (∏ p ∈ r, p) ∣ n)).card = K / ∏ p ∈ r, p := by
          rw [← Nat.Ioc_filter_dvd_card_eq_div]; rfl
        rw [hcard, prod_div_distrib]
        calc ((K / ∏ p ∈ r, p : ℕ) : ℝ) * ∏ p ∈ r, g p
            ≤ ((K : ℝ) / ((∏ p ∈ r, p : ℕ) : ℝ)) * ∏ p ∈ r, g p :=
              mul_le_mul_of_nonneg_right Nat.cast_div_le hG
          _ = _ := by push_cast; ring
    _ = K * ∏ p ∈ P, (g p / p + 1) := by rw [← mul_sum, prod_add_one]
    _ ≤ K * Real.exp (126 * (π ^ 2 / 6)) := by
        apply mul_le_mul_of_nonneg_left _ hK
        calc ∏ p ∈ P, (g p / p + 1) ≤ ∏ p ∈ P, Real.exp (g p / p) := by
              apply Finset.prod_le_prod
              · intro p hp
                have := hg0 p hp
                have : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
                positivity
              · intro p _; linarith [Real.add_one_le_exp (g p / p)]
          _ = Real.exp (∑ p ∈ P, g p / p) := (Real.exp_sum _ _).symm
          _ ≤ Real.exp (126 * (π ^ 2 / 6)) := by
              apply Real.exp_le_exp.2
              calc ∑ p ∈ P, g p / p ≤ ∑ p ∈ P, 126 * (1 / (p : ℝ) ^ 2) :=
                    sum_le_sum fun p hp => cfac_cube_sub_one_le (hP p hp)
                _ = 126 * ∑ p ∈ P, (1 / (p : ℝ) ^ 2) := by rw [mul_sum]
                _ ≤ 126 * (π ^ 2 / 6) := by
                    apply mul_le_mul_of_nonneg_left _ (by norm_num)
                    exact sum_le_hasSum P (fun n _ => by positivity) hasSum_zeta_two
    _ = _ := by ring

lemma amgm3 {x y w : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hw : 0 ≤ w) :
    x * y * w ≤ (x ^ 3 + y ^ 3 + w ^ 3) / 3 := by
  nlinarith [mul_nonneg (add_nonneg (add_nonneg hx hy) hw)
    (add_nonneg (add_nonneg (sq_nonneg (x - y)) (sq_nonneg (y - w))) (sq_nonneg (w - x)))]

/-- **SS2** (Lemma 3), uniform in `q`, `z`, `K`. -/
theorem lemma3 : ∃ C₃ : ℝ, ∀ (q : ℕ) (z : ℝ) (K : ℕ), 1 ≤ q →
    ∑ k ∈ Icc 1 K, ∑ h ∈ Ico 1 k, S3 z (h * q) (k * q) ≤ C₃ * (Qz q z) ^ 2 * (K : ℝ) ^ 2 := by
  refine ⟨Real.exp (126 * (π ^ 2 / 6)), fun q z K _ => ?_⟩
  set C := Real.exp (126 * (π ^ 2 / 6))
  set S := ∑ n ∈ Icc 1 K, Efn n ^ 3 with hS
  have hSle : S ≤ C * K := sum_Efn_cube_le K
  have hS0 : 0 ≤ S := sum_nonneg fun n _ => pow_nonneg (Efn_nonneg n) 3
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have q2 : 0 ≤ Qz q z ^ 2 := sq_nonneg _
  -- three partial bounds
  have b1 : ∑ k ∈ Icc 1 K, ∑ h ∈ Ico 1 k, Efn h ^ 3 ≤ K * S := by
    calc _ ≤ ∑ k ∈ Icc 1 K, S := by
          apply sum_le_sum; intro k hk
          rw [mem_Icc] at hk
          apply sum_le_sum_of_subset_of_nonneg
          · intro h hh; rw [mem_Ico] at hh; rw [mem_Icc]; omega
          · intro n _ _; exact pow_nonneg (Efn_nonneg n) 3
      _ = K * S := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
  have b2 : ∑ k ∈ Icc 1 K, ∑ h ∈ Ico 1 k, Efn k ^ 3 ≤ K * S := by
    calc _ ≤ ∑ k ∈ Icc 1 K, (K : ℝ) * Efn k ^ 3 := by
          apply sum_le_sum; intro k hk
          rw [mem_Icc] at hk
          rw [sum_const, nsmul_eq_mul, Nat.card_Ico]
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (Efn_nonneg k) 3)
          exact_mod_cast (by omega : k - 1 ≤ K)
      _ = K * S := by rw [mul_sum]
  have b3 : ∑ k ∈ Icc 1 K, ∑ h ∈ Ico 1 k, Efn (k - h) ^ 3 ≤ K * S := by
    have : ∀ k ∈ Icc 1 K, ∑ h ∈ Ico 1 k, Efn (k - h) ^ 3 = ∑ h ∈ Ico 1 k, Efn h ^ 3 := by
      intro k _
      rw [sum_Ico_reflect (fun n => Efn n ^ 3) 1 (Nat.le_succ k)]
      simp
    rw [sum_congr rfl this]; exact b1
  calc ∑ k ∈ Icc 1 K, ∑ h ∈ Ico 1 k, S3 z (h * q) (k * q)
      ≤ ∑ k ∈ Icc 1 K, ∑ h ∈ Ico 1 k,
          Qz q z ^ 2 * ((Efn h ^ 3 + Efn k ^ 3 + Efn (k - h) ^ 3) / 3) := by
        apply sum_le_sum; intro k _
        apply sum_le_sum; intro h hh
        rw [mem_Ico] at hh
        calc S3 z (h * q) (k * q) ≤ Qz q z ^ 2 * Efn h * Efn k * Efn (k - h) :=
              S3_le q z hh.1 hh.2
          _ = Qz q z ^ 2 * (Efn h * Efn k * Efn (k - h)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
              (amgm3 (Efn_nonneg _) (Efn_nonneg _) (Efn_nonneg _)) q2
    _ = Qz q z ^ 2 / 3 * (∑ k ∈ Icc 1 K, ∑ h ∈ Ico 1 k, Efn h ^ 3 +
          ∑ k ∈ Icc 1 K, ∑ h ∈ Ico 1 k, Efn k ^ 3 +
          ∑ k ∈ Icc 1 K, ∑ h ∈ Ico 1 k, Efn (k - h) ^ 3) := by
        simp only [← sum_add_distrib, mul_sum]
        apply sum_congr rfl; intro k _; apply sum_congr rfl; intro h _; ring
    _ ≤ Qz q z ^ 2 / 3 * (K * S + K * S + K * S) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    _ = Qz q z ^ 2 * K * S := by ring
    _ ≤ Qz q z ^ 2 * K * (C * K) := mul_le_mul_of_nonneg_left hSle (mul_nonneg q2 hK)
    _ = C * Qz q z ^ 2 * (K : ℝ) ^ 2 := by ring

/-! ### Lemma 2 -/

/-- `p(p-2)/(p-1)^2`: the local factor of `S2` at a prime not dividing `t`. -/
noncomputable def wf (p : ℕ) : ℝ := (p : ℝ) * ((p : ℝ) - 2) / ((p : ℝ) - 1) ^ 2

/-- `p/(p-1)^2`: the extra local factor at a prime dividing `t`. -/
noncomputable def vf (p : ℕ) : ℝ := (p : ℝ) / ((p : ℝ) - 1) ^ 2

lemma wf_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ wf p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold wf
  exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)

lemma vf_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ vf p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold vf
  exact div_nonneg (by linarith) (sq_nonneg _)

lemma vf_div_add_wf {p : ℕ} (hp : p.Prime) : vf p / p + wf p = 1 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h0 : (p : ℝ) ≠ 0 := by linarith
  unfold vf wf
  field_simp
  ring

lemma S2_factor {p : ℕ} (hp : p.Prime) (q h : ℕ) :
    (1 - gpair (h * q) p) / (1 - 1 / (p : ℝ)) =
      (if p ∣ q then (p : ℝ) / ((p : ℝ) - 1) else 1) *
        (if ¬ p ∣ q then (wf p + if p ∣ h then vf p else 0) else 1) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h0 : (p : ℝ) ≠ 0 := by linarith
  unfold gpair wf vf
  by_cases hq : p ∣ q
  · rw [if_pos (Dvd.dvd.mul_left hq h), if_pos hq, if_neg (not_not.2 hq), sub_zero]
    field_simp
  · by_cases hh : p ∣ h
    · rw [if_pos (Dvd.dvd.mul_right hh q), if_neg hq, if_pos hq, if_pos hh]
      field_simp
      ring
    · have : ¬ p ∣ h * q := fun hd => by
        rcases (Nat.Prime.dvd_mul hp).1 hd with e | e
        · exact hh e
        · exact hq e
      rw [if_neg this, if_neg hq, if_pos hq, if_neg hh]
      have h3 : (p : ℝ) - 1 - 1 = (p : ℝ) - 2 := by ring
      field_simp
      ring

lemma S2_expand (q : ℕ) (z : ℝ) (h : ℕ) :
    S2 z (h * q) = Qz q z * ∑ r ∈ ((primesLT z).filter (fun p => ¬ p ∣ q)).powerset,
      (if (∏ p ∈ r, p) ∣ h then ∏ p ∈ r, vf p else 0) *
        ∏ p ∈ (primesLT z).filter (fun p => ¬ p ∣ q) \ r, wf p := by
  unfold S2
  rw [prod_congr rfl (fun p hp => S2_factor (prime_of_mem_primesLT hp) q h), prod_mul_distrib,
    ← prod_filter, ← prod_filter]
  congr 1
  rw [prod_congr rfl (fun p _ => add_comm _ _), prod_add]
  refine sum_congr rfl fun r hr => ?_
  rw [prod_ite_dvd r (fun p hp => prime_of_mem_primesLT
    (mem_filter.1 (mem_powerset.1 hr hp)).1) h vf]

/-- `T_K(d) = ∑_{1 ≤ h < K, d ∣ h} (K - h)`. -/
noncomputable def Tsum (K d : ℕ) : ℝ := ∑ h ∈ Ico 1 K, if d ∣ h then ((K : ℝ) - h) else 0

lemma Tsum_nonneg (K d : ℕ) : 0 ≤ Tsum K d := by
  unfold Tsum
  refine sum_nonneg fun h hh => ?_
  rw [mem_Ico] at hh
  split_ifs
  · have : (h : ℝ) < K := by exact_mod_cast hh.2
    linarith
  · exact le_rfl

lemma Tsum_succ (K d : ℕ) : Tsum (K + 1) d = Tsum K d + ((K / d : ℕ) : ℝ) := by
  unfold Tsum
  have e : ∀ h ∈ Ico 1 (K + 1), (if d ∣ h then (((K + 1 : ℕ) : ℝ) - h) else 0) =
      (if d ∣ h then ((K : ℝ) - h) else 0) + (if d ∣ h then (1 : ℝ) else 0) := by
    intro h _; split_ifs <;> push_cast <;> ring
  rw [sum_congr rfl e, sum_add_distrib, sum_boole]
  congr 1
  · rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK; simp
    · rw [sum_Ico_succ_top (by omega : 1 ≤ K)]; simp
  · rw [← Nat.Ioc_filter_dvd_card_eq_div]
    congr 3

lemma Tsum_lower {d : ℕ} (hd : 1 ≤ d) (K : ℕ) : (K : ℝ) ^ 2 / (2 * d) - K ≤ Tsum K d := by
  have hD : (1 : ℝ) ≤ d := by exact_mod_cast hd
  induction K with
  | zero => simp [Tsum]
  | succ K ih =>
    rw [Tsum_succ]
    have hX : (K : ℝ) + 1 ≤ d * ((K / d : ℕ) : ℝ) + d := by
      have := Nat.div_add_mod K d
      have := Nat.mod_lt K (by omega : d > 0)
      have : K + 1 ≤ d * (K / d) + d := by omega
      exact_mod_cast this
    have e : ((K + 1 : ℕ) : ℝ) ^ 2 / (2 * d) - (K : ℝ) ^ 2 / (2 * d) = (2 * K + 1) / (2 * d) := by
      push_cast; field_simp; ring
    have e2 : (2 * (K : ℝ) + 1) / (2 * d) ≤ ((K / d : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    push_cast at e ⊢
    linarith

lemma Tsum_lower2 {d : ℕ} (hd : 1 ≤ d) (K : ℕ) {s R : ℝ} (hs : 0 ≤ s) (hsd : s ^ 2 = d)
    (hR : 0 < R) :
    (((K : ℝ) ^ 2 / 2 - K * R) - (K : ℝ) ^ 2 / (2 * √R) * s) / d ≤ Tsum K d := by
  have hD : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hsR : 0 < √R := Real.sqrt_pos.2 hR
  by_cases hDR : (d : ℝ) ≤ R
  · rw [sub_div]
    have h1 : 0 ≤ (K : ℝ) ^ 2 / (2 * √R) * s / d := by positivity
    have h2 : ((K : ℝ) ^ 2 / 2 - K * R) / d ≤ (K : ℝ) ^ 2 / (2 * d) - K := by
      have e : ((K : ℝ) ^ 2 / (2 * d) - K) * d = (K : ℝ) ^ 2 / 2 - K * d := by
        field_simp
      rw [div_le_iff₀ (by linarith), e]
      nlinarith
    linarith [Tsum_lower hd K]
  · push_neg at hDR
    have hlt : √R < s := by
      have : √R < √(d : ℝ) := Real.sqrt_lt_sqrt hR.le hDR
      rwa [← hsd, Real.sqrt_sq hs] at this
    have hnum : ((K : ℝ) ^ 2 / 2 - K * R) - (K : ℝ) ^ 2 / (2 * √R) * s ≤ 0 := by
      have : (K : ℝ) ^ 2 / 2 ≤ (K : ℝ) ^ 2 / (2 * √R) * s := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (K : ℝ)]
      nlinarith [mul_nonneg hK hR.le]
    exact le_trans (div_nonpos_of_nonpos_of_nonneg hnum (by linarith)) (Tsum_nonneg K d)

/-- The summable majorant `n^{-3/2}`. -/
noncomputable def f32 (n : ℕ) : ℝ := ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹

lemma f32_nonneg (n : ℕ) : 0 ≤ f32 n := by unfold f32; positivity

lemma summable_f32 : Summable f32 :=
  Real.summable_nat_rpow_inv.2 (by norm_num)

lemma vf_sqrt_le {p : ℕ} (hp : p.Prime) : vf p * √(p : ℝ) / p ≤ 4 * f32 p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have e : (p : ℝ) ^ ((3 : ℝ) / 2) = p * √(p : ℝ) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hp0, Real.rpow_one,
      Real.sqrt_eq_rpow]
  unfold f32 vf
  rw [e]
  set t := √(p : ℝ) with ht
  have ht0 : 0 < t := Real.sqrt_pos.2 hp0
  have htt : t * t = p := Real.mul_self_sqrt hp0.le
  have h1 : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by nlinarith
  have lhs : (p : ℝ) / ((p : ℝ) - 1) ^ 2 * t / p = t / ((p : ℝ) - 1) ^ 2 := by
    field_simp
  rw [lhs, ← div_eq_mul_inv, div_le_div_iff₀ h1 (by positivity)]
  nlinarith

noncomputable def B0 : ℝ := Real.exp (4 * ∑' n, f32 n)

lemma B_le (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) :
    ∏ p ∈ A, (vf p * √(p : ℝ) / p + wf p) ≤ B0 := by
  calc ∏ p ∈ A, (vf p * √(p : ℝ) / p + wf p) ≤ ∏ p ∈ A, Real.exp (4 * f32 p) := by
        apply Finset.prod_le_prod
        · intro p hp
          have := vf_nonneg (hA p hp); have := wf_nonneg (hA p hp); positivity
        · intro p hp
          have h1 := vf_div_add_wf (hA p hp)
          have h2 := vf_sqrt_le (hA p hp)
          have h3 : 0 ≤ vf p / p := by
            have := vf_nonneg (hA p hp); positivity
          linarith [Real.add_one_le_exp (4 * f32 p)]
    _ = Real.exp (∑ p ∈ A, 4 * f32 p) := (Real.exp_sum _ _).symm
    _ ≤ B0 := by
        unfold B0
        apply Real.exp_le_exp.2
        rw [← mul_sum]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact summable_f32.sum_le_tsum A (fun n _ => f32_nonneg n)

lemma Qz_nonneg (q : ℕ) (z : ℝ) : 0 ≤ Qz q z := by
  unfold Qz
  refine prod_nonneg fun p hp => ?_
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem_primesLT (mem_filter.1 hp).1).two_le
  exact div_nonneg (by linarith) (by linarith)

lemma main_lower (q : ℕ) (z : ℝ) (K : ℕ) {R : ℝ} (hR : 0 < R) :
    Qz q z * (((K : ℝ) ^ 2 / 2 - K * R) - (K : ℝ) ^ 2 / (2 * √R) * B0) ≤
      ∑ h ∈ Ico 1 K, ((K : ℝ) - h) * S2 z (h * q) := by
  set A := (primesLT z).filter (fun p => ¬ p ∣ q) with hAdef
  have hA : ∀ p ∈ A, p.Prime := fun p hp => prime_of_mem_primesLT (mem_filter.1 hp).1
  have hQ := Qz_nonneg q z
  set a : ℝ := (K : ℝ) ^ 2 / 2 - K * R with ha
  set b : ℝ := (K : ℝ) ^ 2 / (2 * √R) with hbdef
  have hb : 0 ≤ b := by positivity
  -- rewrite the sum
  have hsum : ∑ h ∈ Ico 1 K, ((K : ℝ) - h) * S2 z (h * q) =
      Qz q z * ∑ r ∈ A.powerset, (∏ p ∈ r, vf p) * (∏ p ∈ A \ r, wf p) * Tsum K (∏ p ∈ r, p) := by
    have e : ∀ h ∈ Ico 1 K, ((K : ℝ) - h) * S2 z (h * q) = Qz q z * ∑ r ∈ A.powerset,
        (∏ p ∈ r, vf p) * (∏ p ∈ A \ r, wf p) *
          (if (∏ p ∈ r, p) ∣ h then ((K : ℝ) - h) else 0) := by
      intro h _
      rw [S2_expand]
      simp only [mul_sum]
      refine sum_congr rfl fun r _ => ?_
      split_ifs <;> ring
    rw [sum_congr rfl e, ← mul_sum, sum_comm]
    congr 1
    refine sum_congr rfl fun r _ => ?_
    rw [Tsum, mul_sum]
  rw [hsum]
  apply mul_le_mul_of_nonneg_left _ hQ
  have hB := B_le A hA
  have hB0 : 0 ≤ ∏ p ∈ A, (vf p * √(p : ℝ) / p + wf p) := prod_nonneg fun p hp => by
    have := vf_nonneg (hA p hp); have := wf_nonneg (hA p hp); positivity
  calc a - b * B0 ≤ a - b * ∏ p ∈ A, (vf p * √(p : ℝ) / p + wf p) := by
        nlinarith [mul_le_mul_of_nonneg_left hB hb]
    _ = a * ∏ p ∈ A, (vf p / p + wf p) - b * ∏ p ∈ A, (vf p * √(p : ℝ) / p + wf p) := by
        rw [prod_congr rfl (fun p hp => vf_div_add_wf (hA p hp)), prod_const_one, mul_one]
    _ = ∑ r ∈ A.powerset, (a * (∏ p ∈ r, (vf p / p)) * (∏ p ∈ A \ r, wf p) -
          b * (∏ p ∈ r, (vf p * √(p : ℝ) / p)) * (∏ p ∈ A \ r, wf p)) := by
        rw [prod_add, prod_add, sum_sub_distrib, mul_sum, mul_sum]
        congr 1 <;> refine sum_congr rfl fun r _ => ?_ <;> ring
    _ ≤ ∑ r ∈ A.powerset, (∏ p ∈ r, vf p) * (∏ p ∈ A \ r, wf p) * Tsum K (∏ p ∈ r, p) := by
        apply sum_le_sum
        intro r hr
        have hr' : ∀ p ∈ r, p.Prime := fun p hp => hA p (mem_powerset.1 hr hp)
        have hd : 1 ≤ ∏ p ∈ r, p := Nat.one_le_iff_ne_zero.2
          (prod_ne_zero_iff.2 fun p hp => (hr' p hp).ne_zero)
        have hs0 : 0 ≤ ∏ p ∈ r, √(p : ℝ) := prod_nonneg fun p _ => Real.sqrt_nonneg _
        have hsd : (∏ p ∈ r, √(p : ℝ)) ^ 2 = ((∏ p ∈ r, p : ℕ) : ℝ) := by
          rw [← prod_pow, Nat.cast_prod]
          exact prod_congr rfl fun p _ => Real.sq_sqrt (Nat.cast_nonneg _)
        have hT := Tsum_lower2 hd K hs0 hsd hR
        have hVW : 0 ≤ (∏ p ∈ r, vf p) * (∏ p ∈ A \ r, wf p) :=
          mul_nonneg (prod_nonneg fun p hp => vf_nonneg (hr' p hp))
            (prod_nonneg fun p hp => wf_nonneg (hA p (mem_sdiff.1 hp).1))
        have key := mul_le_mul_of_nonneg_left hT hVW
        refine le_trans (le_of_eq ?_) key
        rw [prod_div_distrib, prod_div_distrib, prod_mul_distrib, Nat.cast_prod]
        have hdpos : (0 : ℝ) < ∏ p ∈ r, (p : ℝ) :=
          prod_pos fun p hp => by exact_mod_cast (hr' p hp).pos
        rw [ha, hbdef]
        field_simp

/-- **SS1** (Lemma 2, finite form, lower bound), uniform in `q`, `z`, `K`. -/
theorem lemma2_finite : ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
    ∀ (q : ℕ) (z : ℝ) (K : ℕ), 1 ≤ q →
      (1 - δ K) * Qz q z * (K : ℝ) ^ 2 / 2 ≤ ∑ h ∈ Ico 1 K, ((K : ℝ) - h) * S2 z (h * q) := by
  refine ⟨fun K => 2 / √(K : ℝ) + B0 / √(√(K : ℝ)), ?_, ?_⟩
  · have h1 : Tendsto (fun K : ℕ => √(K : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun K : ℕ => √(√(K : ℝ))) atTop atTop := Real.tendsto_sqrt_atTop.comp h1
    simpa using ((tendsto_const_nhds (x := (2 : ℝ))).div_atTop h1).add
      ((tendsto_const_nhds (x := B0)).div_atTop h2)
  · intro q z K _
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK; simp
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    set u := √(K : ℝ) with hu
    have hu0 : 0 < u := Real.sqrt_pos.2 (by linarith)
    have huu : u ^ 2 = K := Real.sq_sqrt (by linarith)
    have hL := main_lower q z K hu0
    refine le_trans (le_of_eq ?_) hL
    set v := √u
    have hv0 : 0 < v := Real.sqrt_pos.2 hu0
    rw [← huu]
    field_simp
    ring

end Erdos971
