import Erdos971.Moments
import Erdos971.Occupancy
import Erdos971.Statement

/-!
# Erdős #971 — assembly (BLUEPRINT §6)
-/

open Real Finset Filter Topology

namespace Erdos971

lemma card_reduced (q : ℕ) : (reduced q).card = q.totient := by
  rw [Nat.totient_eq_card_coprime, reduced]
  congr 1
  exact Finset.filter_congr (fun a _ => Nat.coprime_comm)

open scoped Classical in
/-- Reduced classes containing a prime in `(lo, Y]` number at most `π(Y) - π(lo)`. -/
lemma card_hit_le (q lo Y : ℕ) (hlo : lo ≤ Y) :
    ((reduced q).filter (fun a => ∃ p, p.Prime ∧ lo < p ∧ p ≤ Y ∧ p ≡ a [MOD q])).card
      ≤ Nat.primeCounting Y - Nat.primeCounting lo := by
  classical
  have hsub : (reduced q).filter (fun a => ∃ p, p.Prime ∧ lo < p ∧ p ≤ Y ∧ p ≡ a [MOD q])
      ⊆ ((Nat.primesBelow (Y + 1)) \ (Nat.primesBelow (lo + 1))).image (· % q) := by
    intro a ha
    simp only [mem_filter, reduced, mem_range] at ha
    obtain ⟨⟨hal, _⟩, p, hp, hlp, hpY, hpa⟩ := ha
    refine mem_image.2 ⟨p, ?_, ?_⟩
    · simp only [Finset.mem_sdiff, Nat.primesBelow, mem_filter, mem_range]
      exact ⟨⟨by omega, hp⟩, fun h => by omega⟩
    · have : p % q = a % q := hpa
      simp only [this, Nat.mod_eq_of_lt hal]
  have hsub2 : Nat.primesBelow (lo + 1) ⊆ Nat.primesBelow (Y + 1) := by
    intro p hp
    simp only [Nat.primesBelow, mem_filter, mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_image_le
    _ = _ := by
      rw [card_sdiff_of_subset hsub2, Nat.primesBelow_card_eq_primeCounting',
        Nat.primesBelow_card_eq_primeCounting']
      rfl

open scoped Classical in
theorem erdos_971 : Erdos971Statement := by
  obtain ⟨u₁, h3⟩ := third_moment
  obtain ⟨u₂, hm⟩ := mixed_moment
  set u := max (max u₁ u₂) 2 with hu
  have hu2 : 2 ≤ u := by omega
  obtain ⟨B, hB, hW3⟩ := h3 u (by omega)
  have hmix := hm u (by omega)
  set c : ℝ := 1 / (32 * B) with hc
  have hc0 : 0 < c := by positivity
  have hε : (0 : ℝ) < 1 / (64 * B) := by positivity
  refine ⟨c, hc0, 1 / (16 * B), by positivity, ?_⟩
  have hN := (avgN_tendsto u hu2).eventually_lt_const
    (show (1 : ℝ) < 1 + 1 / (64 * B) by linarith)
  have hZ := (pi_z_small u hu2).eventually_lt_const hε
  have hWin := (pi_window c hc0).eventually_lt_const (show c < c + 1 / (64 * B) by linarith)
  filter_upwards [hN, hZ, hWin, eventually_ge_atTop 2, hmix, hW3, q_le_xq]
    with q hN hZ hWin hq2 hmix hW3 hqx
  have hq0 : 0 < q := by omega
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq0
  have hcard : ((reduced q).card : ℝ) = q.totient := by rw [card_reduced]
  have hx0 : 0 ≤ xq q := le_trans (Nat.cast_nonneg q) hqx
  -- occupancy
  set Zs := (reduced q).filter (fun a => Nc q u a = 0) with hZs
  have hocc := occupancy971 (reduced q) (Nc q u) (Wc q u) (fun i _ => Nc_le_Wc q u i)
    (1 / 2) B (by norm_num) hB
    (by
      rw [hcard]
      have := hmix; unfold avg at this
      rw [le_div_iff₀ hφ] at this
      simpa [mul_comm] using this)
    (by
      rw [hcard]
      have := hW3; unfold avg at this
      rwa [div_le_iff₀ hφ] at this)
  have hNavg : (∑ i ∈ reduced q, (Nc q u i : ℝ)) / (reduced q).card ≤ 1 + 1 / (64 * B) := by
    rw [hcard]; exact hN.le
  have hZs_lb : (1 / (4 * B) - 1 / (64 * B)) * q.totient ≤ (Zs.card : ℝ) := by
    have h := hocc
    rw [hcard] at h
    have hsum : (∑ i ∈ reduced q, (Nc q u i : ℝ)) / q.totient ≤ 1 + 1 / (64 * B) := by
      rw [← hcard]; exact hNavg
    have : (1 / 2 : ℝ) ^ 2 / B = 1 / (4 * B) := by field_simp; ring
    rw [this] at h
    nlinarith [hsum, hφ]
  -- the classes with no prime up to (1+c)x
  set Y := ⌊(1 + c) * xq q⌋₊ with hY
  set X0 := ⌊xq q⌋₊ with hX0
  set Z0 := ⌊zq q u⌋₊ with hZ0
  have hXY : X0 ≤ Y := Nat.floor_le_floor (by nlinarith)
  set T := (reduced q).filter (fun a => ∀ p, p.Prime → p ≤ Y → ¬ p ≡ a [MOD q]) with hT
  set H1 := (reduced q).filter (fun a => ∃ p, p.Prime ∧ 0 < p ∧ p ≤ Z0 ∧ p ≡ a [MOD q])
  set H2 := (reduced q).filter (fun a => ∃ p, p.Prime ∧ X0 < p ∧ p ≤ Y ∧ p ≡ a [MOD q])
  have hcover : Zs ⊆ T ∪ H1 ∪ H2 := by
    intro a ha
    simp only [hZs, mem_filter] at ha
    obtain ⟨har, hNa⟩ := ha
    by_cases hTa : ∀ p, p.Prime → p ≤ Y → ¬ p ≡ a [MOD q]
    · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨har, hTa⟩))
    · push_neg at hTa
      obtain ⟨p, hp, hpY, hpa⟩ := hTa
      by_cases hpX : X0 < p
      · exact mem_union_right _ (mem_filter.2 ⟨har, p, hp, hpX, hpY, hpa⟩)
      · push_neg at hpX
        have hpz : (p : ℝ) ≤ zq q u := by
          by_contra hlt
          push_neg at hlt
          have : p ∈ (Icc 1 ⌊xq q⌋₊).filter
              (fun p : ℕ => p.Prime ∧ zq q u < (p : ℝ) ∧ p ≡ a [MOD q]) :=
            mem_filter.2 ⟨mem_Icc.2 ⟨hp.one_lt.le, hpX⟩, hp, hlt, hpa⟩
          unfold Nc at hNa
          rw [card_eq_zero] at hNa
          simp [hNa] at this
        have hpZ : p ≤ Z0 := Nat.le_floor hpz
        exact mem_union_left _ (mem_union_right _
          (mem_filter.2 ⟨har, p, hp, hp.pos, hpZ, hpa⟩))
  have hH1 := card_hit_le q 0 Z0 (Nat.zero_le _)
  have hH2 := card_hit_le q X0 Y hXY
  have hTcount : (Zs.card : ℝ) ≤ T.card + Nat.primeCounting Z0
      + ((Nat.primeCounting Y : ℝ) - Nat.primeCounting X0) := by
    have h1 : Zs.card ≤ T.card + H1.card + H2.card :=
      (card_le_card hcover).trans ((card_union_le _ _).trans
        (Nat.add_le_add_right (card_union_le _ _) _))
    have hmono : Nat.primeCounting X0 ≤ Nat.primeCounting Y := Nat.monotone_primeCounting hXY
    have h2 : (H1.card : ℝ) ≤ Nat.primeCounting Z0 := by
      have : H1.card ≤ Nat.primeCounting Z0 := by
        simpa [Nat.primeCounting_zero] using hH1
      exact_mod_cast this
    have h3' : (H2.card : ℝ) ≤ (Nat.primeCounting Y : ℝ) - Nat.primeCounting X0 := by
      rw [← Nat.cast_sub hmono]; exact_mod_cast hH2
    have : (Zs.card : ℝ) ≤ T.card + H1.card + H2.card := by exact_mod_cast h1
    linarith
  have hZ' : (Nat.primeCounting Z0 : ℝ) ≤ 1 / (64 * B) * q.totient := by
    have := hZ; rw [div_lt_iff₀ hφ] at this; linarith
  have hWin' : (Nat.primeCounting Y : ℝ) - Nat.primeCounting X0
      ≤ (c + 1 / (64 * B)) * q.totient := by
    have := hWin; rw [div_lt_iff₀ hφ] at this; linarith
  have hT_lb : 1 / (16 * B) * (q.totient : ℝ) ≤ T.card := by
    have hcB : c = 2 / (64 * B) := by rw [hc]; field_simp; ring
    have e1 : 1 / (4 * B) = 16 / (64 * B) := by field_simp; ring
    have e2 : 1 / (16 * B) = 4 / (64 * B) := by field_simp; ring
    rw [hcB] at hWin'
    rw [e1] at hZs_lb
    rw [e2]
    have hpos : 0 ≤ 1 / (64 * B) * (q.totient : ℝ) := by positivity
    have : (16 / (64 * B) - 1 / (64 * B)) * (q.totient : ℝ)
        - 1 / (64 * B) * q.totient - (2 / (64 * B) + 1 / (64 * B)) * q.totient
        ≥ 4 / (64 * B) * q.totient := by
      have : (16 / (64 * B) - 1 / (64 * B)) * (q.totient : ℝ)
          - 1 / (64 * B) * q.totient - (2 / (64 * B) + 1 / (64 * B)) * q.totient
          = 11 * (1 / (64 * B) * q.totient) := by ring
      have h4 : 4 / (64 * B) * (q.totient : ℝ) = 4 * (1 / (64 * B) * q.totient) := by ring
      rw [this, h4]; linarith
    linarith
  -- T consists of classes whose least prime exceeds (1+c)x
  have hTsub : T ⊆ (Finset.range q).filter (fun a => a.Coprime q ∧
      (leastCongruentPrime a q : ℝ) > (1 + c) * q.totient * Real.log q) := by
    intro a ha
    simp only [hT, mem_filter, reduced, mem_range] at ha
    obtain ⟨⟨hal, hcop⟩, hTa⟩ := ha
    refine mem_filter.2 ⟨mem_range.2 hal, hcop, ?_⟩
    obtain ⟨p, -, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_modEq Y (by omega) hcop
    have hne : ({p : ℕ | p.Prime ∧ p ≡ a [MOD q]} : Set ℕ).Nonempty := ⟨p, hp, hpa⟩
    have hmem := Nat.sInf_mem hne
    have hgt : Y < leastCongruentPrime a q := by
      by_contra hle
      push_neg at hle
      exact hTa _ hmem.1 hle hmem.2
    have : (1 + c) * xq q < (leastCongruentPrime a q : ℝ) := by
      have h1 := Nat.lt_floor_add_one ((1 + c) * xq q)
      have h2 : ((Y : ℕ) : ℝ) + 1 ≤ (leastCongruentPrime a q : ℝ) := by exact_mod_cast hgt
      linarith
    unfold xq at this
    linarith [show (1 + c) * ((q.totient : ℝ) * Real.log q)
      = (1 + c) * q.totient * Real.log q by ring]
  have hfin := card_le_card hTsub
  have : (1 / (16 * B)) * (q.totient : ℝ)
      ≤ (((Finset.range q).filter (fun a => a.Coprime q ∧
          (leastCongruentPrime a q : ℝ) > (1 + c) * q.totient * Real.log q)).card : ℝ) :=
    hT_lb.trans (by exact_mod_cast hfin)
  convert this using 2
  congr 1
  ext a
  simp

end Erdos971
