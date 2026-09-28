import Erdos971.Sieve

/-!
# Combinatorial identities and inequalities behind the moment bounds (no axioms)
-/

open Real Finset Filter Topology

namespace Erdos971

/-- `w³ ≤ 24·C(w,3) + 4w` (equivalently `w³ ≤ 4((w)₃ + w)`). -/
lemma cube_le_choose (w : ℕ) : (w : ℝ) ^ 3 ≤ 24 * (w.choose 3 : ℝ) + 4 * w := by
  rcases Nat.lt_or_ge w 3 with hw | hw
  · interval_cases w <;> norm_num [Nat.choose]
  · obtain ⟨m, rfl⟩ : ∃ m, w = m + 3 := ⟨w - 3, by omega⟩
    have h6 : ((m + 3).choose 3 : ℝ) * 6 = (m + 3) * (m + 2) * (m + 1) := by
      have := Nat.descFactorial_eq_factorial_mul_choose (m + 3) 3
      simp [Nat.descFactorial_succ, Nat.factorial] at this
      have e : (m + 3).choose 3 * 6 = (m + 3) * (m + 2) * (m + 1) := by
        rw [mul_comm, ← this]; ring
      exact_mod_cast e
    push_cast
    nlinarith [h6, sq_nonneg ((m : ℝ) + 1)]

/-- Three distinct naturals can be listed in increasing order. -/
lemma exists_sorted3 {x y z : ℕ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ a b c : ℕ, a < b ∧ b < c ∧ ({x, y, z} : Finset ℕ) = {a, b, c} := by
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hyz with h3 | h3
  · exact ⟨x, y, z, h1, h3, rfl⟩
  · exact ⟨x, z, y, h2, h3, by ext n; simp; tauto⟩
  · omega
  · exact ⟨z, x, y, h2, h1, by ext n; simp; tauto⟩
  · exact ⟨y, x, z, h1, h2, by ext n; simp; tauto⟩
  · omega
  · exact ⟨y, z, x, h3, h2, by ext n; simp; tauto⟩
  · exact ⟨z, y, x, h3, h1, by ext n; simp; tauto⟩

/-- The set counted by `Wc q u a`. -/
noncomputable def Wset (q u a : ℕ) : Finset ℕ :=
  (Icc 1 ⌊xq q⌋₊).filter (fun n : ℕ => Nat.Coprime n (Pz (zq q u)) ∧ n ≡ a [MOD q])

lemma Wc_eq_card (q u a : ℕ) : Wc q u a = (Wset q u a).card := rfl

/-- The set counted by `Qtrip q u h k`. -/
noncomputable def Qset (q u h k : ℕ) : Finset ℕ :=
  (Icc 1 ⌊xq q⌋₊).filter (fun n => Nat.Coprime (n * (n + h) * (n + k)) (Pz (zq q u)))

/-- **Triples.** `Σ_a C(W_a, 3) ≤ Σ_{1 ≤ h < k ≤ K} Qtrip(hq, kq)`. -/
lemma sum_choose_three_le (q u : ℕ) (hq : 0 < q) :
    ∑ a ∈ reduced q, (Wc q u a).choose 3
      ≤ ∑ k ∈ Icc 1 (Kq q), ∑ h ∈ Ico 1 k, Qtrip q u (h * q) (k * q) := by
  classical
  set L := (reduced q).sigma (fun a => (Wset q u a).powersetCard 3) with hL
  set Tg := (Icc 1 (Kq q)).sigma (fun k => (Ico 1 k).sigma (fun h => Qset q u (h * q) (k * q)))
    with hTg
  have hLc : L.card = ∑ a ∈ reduced q, (Wc q u a).choose 3 := by
    rw [hL, card_sigma]; simp [Wc_eq_card, card_powersetCard]
  have hTc : Tg.card = ∑ k ∈ Icc 1 (Kq q), ∑ h ∈ Ico 1 k, Qtrip q u (h * q) (k * q) := by
    rw [hTg, card_sigma]; simp [card_sigma, Qtrip, Qset]
  let g : (Σ _ : ℕ, Σ _ : ℕ, ℕ) → (Σ _ : ℕ, Finset ℕ) :=
    fun t => ⟨t.2.2 % q, {t.2.2, t.2.2 + t.2.1 * q, t.2.2 + t.1 * q}⟩
  have hsub : L ⊆ Tg.image g := by
    intro ⟨a, T⟩ hT
    simp only [hL, mem_sigma, mem_powersetCard] at hT
    obtain ⟨ha, hTs, hT3⟩ := hT
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.1 hT3
    obtain ⟨n1, n2, n3, h12, h23, hset⟩ := exists_sorted3 hxy hxz hyz
    rw [hset] at hTs ⊢
    have hm : ∀ n ∈ ({n1, n2, n3} : Finset ℕ), n ∈ Wset q u a := fun n hn => hTs hn
    have h1 := hm n1 (by simp); have h2 := hm n2 (by simp); have h3 := hm n3 (by simp)
    simp only [Wset, mem_filter, mem_Icc] at h1 h2 h3
    have ha' : a < q := by simp [reduced] at ha; exact ha.1
    -- differences are multiples of q
    have hd2 : q ∣ n2 - n1 := (Nat.modEq_iff_dvd' h12.le).1 (h1.2.2.trans h2.2.2.symm)
    have hd3 : q ∣ n3 - n1 := (Nat.modEq_iff_dvd' (h12.trans h23).le).1 (h1.2.2.trans h3.2.2.symm)
    obtain ⟨hh, hhq⟩ := hd2
    obtain ⟨kk, hkq⟩ := hd3
    have hn2 : n2 = n1 + hh * q := by rw [mul_comm]; omega
    have hn3 : n3 = n1 + kk * q := by rw [mul_comm]; omega
    have hhpos : 1 ≤ hh := by
      rcases Nat.eq_zero_or_pos hh with h0 | h0
      · subst h0; omega
      · exact h0
    have hhk : hh < kk := by
      by_contra hc; push_neg at hc
      have : hh * q ≥ kk * q := Nat.mul_le_mul_right q hc
      omega
    have hkK : kk ≤ Kq q := by
      unfold Kq
      apply Nat.le_floor
      rw [le_div_iff₀ (by exact_mod_cast hq)]
      have hx : (n3 : ℝ) ≤ ⌊xq q⌋₊ := by exact_mod_cast h3.1.2
      have hfl : (⌊xq q⌋₊ : ℝ) ≤ xq q := Nat.floor_le (by
        by_contra hneg; push_neg at hneg
        have : ⌊xq q⌋₊ = 0 := Nat.floor_eq_zero.2 (by linarith)
        omega)
      have : ((kk * q : ℕ) : ℝ) ≤ n3 := by exact_mod_cast (show kk * q ≤ n3 by omega)
      push_cast at this; linarith
    refine mem_image.2 ⟨⟨kk, ⟨hh, n1⟩⟩, ?_, ?_⟩
    · simp only [hTg, mem_sigma, mem_Icc, mem_Ico, Qset, mem_filter]
      refine ⟨⟨by omega, hkK⟩, ⟨hhpos, hhk⟩, h1.1, ?_⟩
      rw [← hn2, ← hn3]
      exact Nat.Coprime.mul_left (Nat.Coprime.mul_left h1.2.1 h2.2.1) h3.2.1
    · simp only [g]
      have hmod : n1 % q = a := by
        have := h1.2.2; unfold Nat.ModEq at this; rw [this, Nat.mod_eq_of_lt ha']
      rw [hmod, ← hn2, ← hn3]
  calc ∑ a ∈ reduced q, (Wc q u a).choose 3 = L.card := hLc.symm
    _ ≤ (Tg.image g).card := card_le_card hsub
    _ ≤ Tg.card := card_image_le
    _ = _ := hTc

/-- A prime `p > z` is coprime to `P(z)`. -/
lemma prime_coprime_Pz {p : ℕ} (hp : p.Prime) {z : ℝ} (hz : z < p) : Nat.Coprime p (Pz z) := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hd
  unfold Pz at hd
  obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 hd
  simp only [primesLT, mem_filter, mem_range] at hr
  have := (Nat.prime_dvd_prime_iff_eq hp hr.2.1).1 hpr
  subst this
  linarith [hr.2.2]

lemma coprime_mod_iff_mc (p q : ℕ) : Nat.Coprime (p % q) q ↔ Nat.Coprime p q := by
  unfold Nat.Coprime; rw [← Nat.gcd_rec, Nat.gcd_comm]

/-- The primes counted by `Σ_a N_a`: `z < p ≤ x`, `p` prime, `p ∤ q`. -/
noncomputable def Gset (q u : ℕ) : Finset ℕ :=
  (Icc 1 ⌊xq q⌋₊).filter (fun p : ℕ => p.Prime ∧ zq q u < (p : ℝ) ∧ Nat.Coprime p q)

/-- Fibre decomposition: `Σ_{p ∈ G} F(p mod q) = Σ_{a reduced} N_a F(a)`. -/
lemma sum_Gset_fiber (q u : ℕ) (hq : 0 < q) (F : ℕ → ℝ) :
    ∑ p ∈ Gset q u, F (p % q) = ∑ a ∈ reduced q, (Nc q u a : ℝ) * F a := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Gset q u) (t := reduced q) (g := fun p => p % q)]
  · refine Finset.sum_congr rfl (fun a ha => ?_)
    have ha' : a < q ∧ Nat.Coprime a q := by simpa [reduced] using ha
    have hset : (Gset q u).filter (fun p => p % q = a)
        = (Icc 1 ⌊xq q⌋₊).filter (fun p : ℕ => p.Prime ∧ zq q u < (p : ℝ) ∧ p ≡ a [MOD q]) := by
      ext p
      simp only [Gset, mem_filter, Nat.ModEq, Nat.mod_eq_of_lt ha'.1]
      constructor
      · rintro ⟨⟨h1, h2, h3, _⟩, h5⟩; exact ⟨h1, h2, h3, h5⟩
      · rintro ⟨h1, h2, h3, h5⟩
        refine ⟨⟨h1, h2, h3, ?_⟩, h5⟩
        rw [← coprime_mod_iff_mc, h5]; exact ha'.2
    rw [Finset.sum_congr rfl (fun p hp => by rw [(mem_filter.1 hp).2]), sum_const, hset]
    simp [Nc, nsmul_eq_mul]
  · intro p hp
    simp only [Gset, mem_filter] at hp
    simp only [reduced, mem_filter, mem_range]
    exact ⟨Nat.mod_lt _ hq, (coprime_mod_iff_mc p q).2 hp.2.2.2⟩

/-- Partners of a good prime `p` in its class: `p` itself, `p + hq`, `p - hq`. -/
lemma partners_le (q u p : ℕ) (hq : 0 < q) (hp : p ∈ Gset q u) :
    1 + ((Ico 1 (Kq q)).filter
          (fun h => p + h * q ≤ ⌊xq q⌋₊ ∧ Nat.Coprime (p + h * q) (Pz (zq q u)))).card
      + ((Ico 1 (Kq q)).filter
          (fun h => h * q < p ∧ Nat.Coprime (p - h * q) (Pz (zq q u)))).card
      ≤ Wc q u (p % q) := by
  classical
  set U := (Ico 1 (Kq q)).filter
    (fun h => p + h * q ≤ ⌊xq q⌋₊ ∧ Nat.Coprime (p + h * q) (Pz (zq q u)))
  set L := (Ico 1 (Kq q)).filter
    (fun h => h * q < p ∧ Nat.Coprime (p - h * q) (Pz (zq q u)))
  simp only [Gset, mem_filter, mem_Icc] at hp
  obtain ⟨⟨hp1, hpx⟩, hpp, hpz, hpq⟩ := hp
  have hUi : Set.InjOn (fun h => p + h * q) U := by
    intro a _ b _ hab; simp only at hab
    exact Nat.eq_of_mul_eq_mul_right hq (by omega)
  have hLi : Set.InjOn (fun h => p - h * q) L := by
    intro a ha b hb hab; simp only at hab
    have ha' := (mem_filter.1 ha).2.1; have hb' := (mem_filter.1 hb).2.1
    exact Nat.eq_of_mul_eq_mul_right hq (by omega)
  have hd1 : Disjoint ({p} : Finset ℕ) (U.image (fun h => p + h * q)) := by
    rw [disjoint_singleton_left, mem_image]
    rintro ⟨h, hh, he⟩
    have : 1 ≤ h := (mem_Ico.1 (mem_filter.1 hh).1).1
    have : 1 * q ≤ h * q := Nat.mul_le_mul_right q this
    omega
  have hd2 : Disjoint ({p} ∪ U.image (fun h => p + h * q)) (L.image (fun h => p - h * q)) := by
    rw [disjoint_left]
    intro n hn hn'
    obtain ⟨h, hh, rfl⟩ := mem_image.1 hn'
    have h1 : 1 ≤ h := (mem_Ico.1 (mem_filter.1 hh).1).1
    have h2 := (mem_filter.1 hh).2.1
    have : 1 * q ≤ h * q := Nat.mul_le_mul_right q h1
    rcases mem_union.1 hn with hn | hn
    · rw [mem_singleton] at hn; omega
    · obtain ⟨h', hh', he⟩ := mem_image.1 hn; omega
  have hsub : {p} ∪ U.image (fun h => p + h * q) ∪ L.image (fun h => p - h * q)
      ⊆ Wset q u (p % q) := by
    intro n hn
    simp only [Wset, mem_filter, mem_Icc]
    rcases mem_union.1 hn with hn | hn
    · rcases mem_union.1 hn with hn | hn
      · rw [mem_singleton] at hn; subst hn
        exact ⟨⟨hp1, hpx⟩, prime_coprime_Pz hpp hpz, (Nat.mod_modEq n q).symm⟩
      · obtain ⟨h, hh, rfl⟩ := mem_image.1 hn
        obtain ⟨-, hx, hc⟩ := mem_filter.1 hh
        refine ⟨⟨by omega, hx⟩, hc, ?_⟩
        show (p + h * q) % q = p % q % q
        simp [Nat.add_mul_mod_self_right]
    · obtain ⟨h, hh, rfl⟩ := mem_image.1 hn
      obtain ⟨-, hlt, hc⟩ := mem_filter.1 hh
      refine ⟨⟨by omega, by omega⟩, hc, ?_⟩
      show (p - h * q) % q = p % q % q
      rw [Nat.mod_mod]
      conv_rhs => rw [show p = (p - h * q) + h * q by omega]
      simp [Nat.add_mul_mod_self_right]
  calc 1 + U.card + L.card
      = ({p} ∪ U.image (fun h => p + h * q) ∪ L.image (fun h => p - h * q)).card := by
        rw [card_union_of_disjoint hd2, card_union_of_disjoint hd1, card_singleton,
          card_image_of_injOn hUi, card_image_of_injOn hLi]
    _ ≤ (Wset q u (p % q)).card := card_le_card hsub
    _ = Wc q u (p % q) := rfl

/-- Removing the primes dividing `q` from a filter of primes. -/
lemma card_filter_prime_le (q : ℕ) (hq : 0 < q) (S : Finset ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hS : ∀ p ∈ S, p.Prime) :
    (S.filter P).card ≤ (S.filter (fun p => P p ∧ Nat.Coprime p q)).card + q.primeFactors.card := by
  classical
  have : S.filter P ⊆ S.filter (fun p => P p ∧ Nat.Coprime p q) ∪ q.primeFactors := by
    intro p hp
    obtain ⟨hpS, hP⟩ := mem_filter.1 hp
    by_cases hc : Nat.Coprime p q
    · exact mem_union_left _ (mem_filter.2 ⟨hpS, hP, hc⟩)
    · refine mem_union_right _ (Nat.mem_primeFactors.2 ⟨hS p hpS, ?_, hq.ne'⟩)
      exact (Nat.Prime.coprime_iff_not_dvd (hS p hpS)).not_left.1 hc
  exact (card_le_card this).trans (card_union_le _ _)

/-- **Mixed moment, counting form.** -/
lemma mixed_count (q u : ℕ) (hq : 0 < q) (hzq : zq q u < q) :
    (∑ a ∈ reduced q, (Nc q u a : ℝ))
        + ∑ h ∈ Ico 1 (Kq q), ((Mplus q u h : ℝ) + Mminus q u h)
        - 2 * (Kq q : ℝ) * q.primeFactors.card
      ≤ ∑ a ∈ reduced q, (Nc q u a : ℝ) * Wc q u a := by
  classical
  have hW := sum_Gset_fiber q u hq (fun a => (Wc q u a : ℝ))
  have hN := sum_Gset_fiber q u hq (fun _ => (1 : ℝ))
  simp only [mul_one, sum_const, nsmul_eq_mul] at hN
  rw [← hW, ← hN]
  set G := Gset q u
  set cU := fun p h => p + h * q ≤ ⌊xq q⌋₊ ∧ Nat.Coprime (p + h * q) (Pz (zq q u))
  set cL := fun p h => h * q < p ∧ Nat.Coprime (p - h * q) (Pz (zq q u))
  -- per-prime bound
  have hper : ∀ p ∈ G, (1 : ℝ) + ((Ico 1 (Kq q)).filter (cU p)).card
      + ((Ico 1 (Kq q)).filter (cL p)).card ≤ Wc q u (p % q) := by
    intro p hp; exact_mod_cast partners_le q u p hq hp
  -- swap sums
  have hswap : ∀ c : ℕ → ℕ → Prop, [∀ p h, Decidable (c p h)] →
      ∑ p ∈ G, (((Ico 1 (Kq q)).filter (c p)).card : ℝ)
        = ∑ h ∈ Ico 1 (Kq q), ((G.filter (fun p => c p h)).card : ℝ) := by
    intro c _
    simp only [card_filter]; push_cast
    exact Finset.sum_comm
  -- each shifted count is at least M - ω(q)
  have hM : ∀ h ∈ Ico 1 (Kq q),
      (Mplus q u h : ℝ) + Mminus q u h - 2 * q.primeFactors.card
        ≤ ((G.filter (fun p => cU p h)).card : ℝ) + (G.filter (fun p => cL p h)).card := by
    intro h hh
    have h1 : 1 ≤ h := (mem_Ico.1 hh).1
    set Pr := (Icc 1 ⌊xq q⌋₊).filter (fun p : ℕ => p.Prime ∧ zq q u < (p : ℝ))
    have hPr : ∀ p ∈ Pr, p.Prime := fun p hp => (mem_filter.1 hp).2.1
    have e1 : Mplus q u h = (Pr.filter (fun p => cU p h)).card := by
      unfold Mplus; congr 1; ext p; simp [Pr, cU, and_assoc]
    have e2 : Mminus q u h = (Pr.filter (fun p => cL p h)).card := by
      unfold Mminus; congr 1; ext p
      simp only [Pr, cL, mem_filter]
      constructor
      · rintro ⟨hI, hp, hlt, hc⟩
        refine ⟨⟨hI, hp, ?_⟩, hlt, hc⟩
        have : (q : ℝ) ≤ p := by
          have : 1 * q ≤ h * q := Nat.mul_le_mul_right q h1
          exact_mod_cast (show q ≤ p by omega)
        linarith
      · rintro ⟨⟨hI, hp, -⟩, hlt, hc⟩; exact ⟨hI, hp, hlt, hc⟩
    have g1 : ∀ c : ℕ → Prop, [DecidablePred c] →
        (G.filter c).card = (Pr.filter (fun p => c p ∧ Nat.Coprime p q)).card := by
      intro c _; congr 1; ext p; simp [G, Gset, Pr, and_assoc, and_comm, and_left_comm]
    have b1 := card_filter_prime_le q hq Pr (fun p => cU p h) hPr
    have b2 := card_filter_prime_le q hq Pr (fun p => cL p h) hPr
    rw [← g1] at b1 b2
    rw [e1, e2]
    have : ((Pr.filter (fun p => cU p h)).card : ℝ) ≤ (G.filter (fun p => cU p h)).card
        + q.primeFactors.card := by exact_mod_cast b1
    have : ((Pr.filter (fun p => cL p h)).card : ℝ) ≤ (G.filter (fun p => cL p h)).card
        + q.primeFactors.card := by exact_mod_cast b2
    linarith
  have hsumM := Finset.sum_le_sum hM
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsumM
  have hK : ((Ico 1 (Kq q)).card : ℝ) ≤ Kq q := by
    simp only [Nat.card_Ico]; exact_mod_cast Nat.sub_le _ _
  have hconst : ∑ h ∈ Ico 1 (Kq q), (2 * (q.primeFactors.card : ℝ))
      ≤ 2 * (Kq q : ℝ) * q.primeFactors.card := by
    rw [sum_const, nsmul_eq_mul]
    have : (0 : ℝ) ≤ q.primeFactors.card := by positivity
    nlinarith
  have hsumper := Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_const, nsmul_eq_mul, mul_one,
    hswap cU, hswap cL] at hsumper
  rw [Finset.sum_add_distrib] at hsumM ⊢
  linarith

end Erdos971
