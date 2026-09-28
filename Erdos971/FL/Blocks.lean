import Erdos971.FL.Bonferroni

/-!
# Fundamental lemma, part B: blocked Bonferroni weights

Primes `P` are split into blocks `B j = {p ∈ P : blk p = j}`, `j < J`. A subset `D ⊆ P` is in the
upper support if `|D ∩ B j| ≤ r j` for all `j`; the lower support adds the pairwise disjoint facets
"`|D ∩ B j| = r j + 1` for exactly one `j`, all others `≤ r i`". Weights are `(-1)^{|D|}` on the support.
-/

open Finset

namespace Erdos971.FL

variable (P : Finset ℕ) (blk : ℕ → ℕ) (J : ℕ) (r : ℕ → ℕ)

/-- Block `j`. -/
def block (j : ℕ) : Finset ℕ := P.filter (fun p => blk p = j)

/-- `|D ∩ B_j|`. -/
def cnt (D : Finset ℕ) (j : ℕ) : ℕ := (D.filter (fun p => blk p = j)).card

/-- Upper support. -/
def inPlus (D : Finset ℕ) : Prop := ∀ j < J, cnt blk D j ≤ r j

/-- The `j`-th lower facet. -/
def inFacet (D : Finset ℕ) (j : ℕ) : Prop :=
  cnt blk D j = r j + 1 ∧ ∀ i < J, i ≠ j → cnt blk D i ≤ r i

open Classical in
/-- Upper weight. -/
noncomputable def lamPlus (D : Finset ℕ) : ℝ :=
  if inPlus blk J r D then (-1 : ℝ) ^ D.card else 0

open Classical in
/-- Lower weight. -/
noncomputable def lamMinus (D : Finset ℕ) : ℝ :=
  if inPlus blk J r D ∨ ∃ j < J, inFacet blk J r D j then (-1 : ℝ) ^ D.card else 0


/-! ### Helper lemmas -/

/-- Split a powerset sum along a predicate. -/
lemma sum_powerset_split (P : Finset ℕ) (q : ℕ → Prop) [DecidablePred q] (F : Finset ℕ → ℝ) :
    ∑ D ∈ P.powerset, F D
      = ∑ S ∈ (P.filter q).powerset, ∑ T ∈ (P.filter (fun x => ¬ q x)).powerset, F (S ∪ T) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun D => (D.filter q, D.filter (fun x => ¬ q x))) (fun x => x.1 ∪ x.2)
    ?_ ?_ ?_ ?_ ?_
  · intro D hD
    simp only [mem_powerset, mem_product] at hD ⊢
    exact ⟨filter_subset_filter _ hD, filter_subset_filter _ hD⟩
  · rintro ⟨S, T⟩ h
    simp only [mem_powerset, mem_product] at h ⊢
    exact union_subset (h.1.trans (filter_subset _ _)) (h.2.trans (filter_subset _ _))
  · intro D _
    simp only [filter_union_filter_not_eq]
  · rintro ⟨S, T⟩ h
    simp only [mem_powerset, mem_product] at h
    have hS : ∀ x ∈ S, q x := fun x hx => (mem_filter.1 (h.1 hx)).2
    have hT : ∀ x ∈ T, ¬ q x := fun x hx => (mem_filter.1 (h.2 hx)).2
    refine Prod.ext ?_ ?_
    · ext x
      simp only [mem_filter, mem_union]
      constructor
      · rintro ⟨hx | hx, hq⟩
        · exact hx
        · exact absurd hq (hT x hx)
      · intro hx; exact ⟨Or.inl hx, hS x hx⟩
    · ext x
      simp only [mem_filter, mem_union]
      constructor
      · rintro ⟨hx | hx, hq⟩
        · exact absurd (hS x hx) hq
        · exact hx
      · intro hx; exact ⟨Or.inr hx, hT x hx⟩
  · intro D _
    simp only [filter_union_filter_not_eq]

/-- Factorization of a blockwise product over subsets. -/
theorem sum_prod_blocks (f : ℕ → Finset ℕ → ℝ) (s : Finset ℕ) :
    ∀ P : Finset ℕ, (∀ p ∈ P, blk p ∈ s) →
      ∑ D ∈ P.powerset, ∏ j ∈ s, f j (D.filter (fun p => blk p = j))
        = ∏ j ∈ s, ∑ S ∈ (P.filter (fun p => blk p = j)).powerset, f j S := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro P hP
    have : P = ∅ := eq_empty_of_forall_notMem (fun p hp => by simpa using hP p hp)
    subst this
    simp
  | insert a s ha ih =>
    intro P hP
    have hB : ∀ p ∈ P.filter (fun x => ¬ blk x = a), blk p ∈ s := by
      intro p hp
      rw [mem_filter] at hp
      rcases mem_insert.1 (hP p hp.1) with h | h
      · exact absurd h hp.2
      · exact h
    have hR : ∏ j ∈ s, ∑ S ∈ (P.filter (fun p => blk p = j)).powerset, f j S
        = ∏ j ∈ s, ∑ S ∈ ((P.filter (fun x => ¬ blk x = a)).filter (fun p => blk p = j)).powerset,
            f j S := by
      apply prod_congr rfl
      intro j hj
      have hja : j ≠ a := fun h => ha (h ▸ hj)
      congr 2
      ext x
      simp only [mem_filter]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ hja⟩, h2⟩
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    rw [prod_insert ha, hR, ← ih _ hB, sum_powerset_split P (fun x => blk x = a), sum_mul_sum]
    apply sum_congr rfl
    intro S hS
    apply sum_congr rfl
    intro T hT
    rw [mem_powerset] at hS hT
    have hSa : ∀ x ∈ S, blk x = a := fun x hx => (mem_filter.1 (hS hx)).2
    have hTa : ∀ x ∈ T, ¬ blk x = a := fun x hx => (mem_filter.1 (hT hx)).2
    rw [prod_insert ha]
    congr 1
    · congr 1
      ext x
      simp only [mem_filter, mem_union]
      constructor
      · rintro ⟨hx | hx, hq⟩
        · exact hx
        · exact absurd hq (hTa x hx)
      · intro hx; exact ⟨Or.inl hx, hSa x hx⟩
    · apply prod_congr rfl
      intro j hj
      have hja : j ≠ a := fun h => ha (h ▸ hj)
      congr 1
      ext x
      simp only [mem_filter, mem_union]
      constructor
      · rintro ⟨hx | hx, hq⟩
        · exact absurd (hq.symm.trans (hSa x hx)) hja
        · exact ⟨hx, hq⟩
      · rintro ⟨hx, hq⟩; exact ⟨Or.inr hx, hq⟩

/-- Blockwise decomposition of a signed product with blockwise conditions. -/
theorem prod_blocks_ite (c : ℕ → ℕ → Prop) [∀ j n, Decidable (c j n)] (g : ℕ → ℝ)
    (D : Finset ℕ) (hD : ∀ p ∈ D, blk p < J) :
    ∏ j ∈ range J, (if c j (D.filter (fun p => blk p = j)).card then
        (-1 : ℝ) ^ (D.filter (fun p => blk p = j)).card * ∏ p ∈ D.filter (fun p => blk p = j), g p
        else 0)
      = if (∀ j ∈ range J, c j (cnt blk D j)) then (-1 : ℝ) ^ D.card * ∏ p ∈ D, g p else 0 := by
  rw [prod_ite_zero]
  have hmap : ∀ p ∈ D, blk p ∈ range J := fun p hp => mem_range.2 (hD p hp)
  congr 1
  rw [prod_mul_distrib, prod_pow_eq_pow_sum, prod_fiberwise_of_maps_to hmap,
    ← card_eq_sum_card_fiberwise hmap]

/-- Truncated sum over a block. -/
theorem sum_le_eq_Utr (g : ℕ → ℝ) (B : Finset ℕ) (k : ℕ) :
    ∑ S ∈ B.powerset, (if S.card ≤ k then (-1 : ℝ) ^ S.card * ∏ p ∈ S, g p else 0)
      = Utr g B k := by
  unfold Utr Esym
  simp_rw [powersetCard_eq_filter, mul_sum, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro S _
  have : ∀ l ∈ range (k + 1), (if S.card = l then (-1 : ℝ) ^ l * ∏ p ∈ S, g p else 0)
      = if S.card = l then (-1 : ℝ) ^ S.card * ∏ p ∈ S, g p else 0 := by
    intro l _; split_ifs with h
    · rw [h]
    · rfl
  rw [sum_congr rfl this, sum_ite_eq]
  simp [mem_range]

/-- Exact-size sum over a block. -/
theorem sum_eq_eq_Esym (g : ℕ → ℝ) (B : Finset ℕ) (m : ℕ) :
    ∑ S ∈ B.powerset, (if S.card = m then (-1 : ℝ) ^ S.card * ∏ p ∈ S, g p else 0)
      = (-1 : ℝ) ^ m * Esym g B m := by
  unfold Esym
  rw [powersetCard_eq_filter, sum_filter, mul_sum]
  apply sum_congr rfl
  intro S _
  split_ifs with h
  · rw [h]
  · simp

open Classical in
/-- Lower weight = upper weight + facet terms. -/
theorem lamMinus_split (D : Finset ℕ) :
    lamMinus blk J r D = lamPlus blk J r D
      + ∑ j ∈ range J, (if inFacet blk J r D j then (-1 : ℝ) ^ D.card else 0) := by
  unfold lamMinus lamPlus
  by_cases h1 : inPlus blk J r D
  · rw [if_pos (Or.inl h1), if_pos h1, sum_eq_zero, add_zero]
    intro j hj
    rw [if_neg]
    intro hf
    have := h1 j (mem_range.1 hj)
    rw [hf.1] at this
    omega
  · rw [if_neg h1, zero_add]
    by_cases h2 : ∃ j < J, inFacet blk J r D j
    · obtain ⟨j, hj, hf⟩ := h2
      rw [if_pos (Or.inr ⟨j, hj, hf⟩), sum_eq_single j, if_pos hf]
      · intro i hi hij
        rw [if_neg]
        intro hfi
        have := hf.2 i (mem_range.1 hi) hij
        rw [hfi.1] at this
        omega
      · intro hj'; exact absurd (mem_range.2 hj) hj'
    · rw [if_neg (fun h => h.elim h1 h2), sum_eq_zero]
      intro j hj
      rw [if_neg]
      intro hf
      exact h2 ⟨j, mem_range.1 hj, hf⟩

theorem abs_lamPlus_le (D : Finset ℕ) : |lamPlus blk J r D| ≤ 1 := by
  unfold lamPlus
  split_ifs
  · rw [abs_pow, abs_neg, abs_one, one_pow]
  · simp

theorem abs_lamMinus_le (D : Finset ℕ) : |lamMinus blk J r D| ≤ 1 := by
  unfold lamMinus
  split_ifs
  · rw [abs_pow, abs_neg, abs_one, one_pow]
  · simp

/-- Support of the weights: at most `r j + 1` elements in each block. -/
theorem cnt_le_of_lam_ne (D : Finset ℕ) (h : lamPlus blk J r D ≠ 0 ∨ lamMinus blk J r D ≠ 0) :
    ∀ j < J, cnt blk D j ≤ r j + 1 := by
  intro j hj
  unfold lamPlus lamMinus at h
  by_cases h1 : inPlus blk J r D
  · exact (h1 j hj).trans (Nat.le_succ _)
  · have h2 : ∃ j < J, inFacet blk J r D j := by
      by_contra h2
      rcases h with h | h
      · exact h (by simp [h1])
      · exact h (by simp [h1, h2])
    obtain ⟨i, hi, hf⟩ := h2
    by_cases hij : j = i
    · subst hij; exact hf.1.le
    · exact (hf.2 j hj hij).trans (Nat.le_succ _)

/-- **B-identity (upper).** For every real `g`, with `P` covered by the blocks `j < J`:
`Σ_{D ⊆ P} λ⁺(D) ∏_{p∈D} g p = ∏_{j<J} U_{B_j, r_j}`. -/
theorem sum_lamPlus_eq (hP : ∀ p ∈ P, blk p < J) (g : ℕ → ℝ) :
    ∑ D ∈ P.powerset, lamPlus blk J r D * ∏ p ∈ D, g p
      = ∏ j ∈ range J, Utr g (block P blk j) (r j) := by
  classical
  have hpt : ∀ D ∈ P.powerset, lamPlus blk J r D * ∏ p ∈ D, g p
      = ∏ j ∈ range J, (if (D.filter (fun p => blk p = j)).card ≤ r j then
          (-1 : ℝ) ^ (D.filter (fun p => blk p = j)).card
            * ∏ p ∈ D.filter (fun p => blk p = j), g p else 0) := by
    intro D hD
    rw [mem_powerset] at hD
    rw [prod_blocks_ite blk J (fun j n => n ≤ r j) g D (fun p hp => hP p (hD hp))]
    unfold lamPlus inPlus
    simp only [mem_range]
    split_ifs <;> simp
  have hfac := sum_prod_blocks blk
    (fun j S => if S.card ≤ r j then (-1 : ℝ) ^ S.card * ∏ p ∈ S, g p else 0) (range J) P
    (fun p hp => mem_range.2 (hP p hp))
  rw [sum_congr rfl hpt, hfac]
  apply prod_congr rfl
  intro j _
  exact sum_le_eq_Utr g _ _

/-- **B-identity (lower).** For even `r j` and every real `g`:
`Σ_{D ⊆ P} λ⁻(D) ∏ g = ∏_j U_j - Σ_j E_{r_j+1}(B_j) ∏_{i ≠ j} U_i`. -/
theorem sum_lamMinus_eq (hP : ∀ p ∈ P, blk p < J) (hr : ∀ j, Even (r j)) (g : ℕ → ℝ) :
    ∑ D ∈ P.powerset, lamMinus blk J r D * ∏ p ∈ D, g p
      = ∏ j ∈ range J, Utr g (block P blk j) (r j)
        - ∑ j ∈ range J, Esym g (block P blk j) (r j + 1)
            * ∏ i ∈ (range J).erase j, Utr g (block P blk i) (r i) := by
  classical
  have hpt : ∀ D ∈ P.powerset, lamMinus blk J r D * ∏ p ∈ D, g p
      = lamPlus blk J r D * ∏ p ∈ D, g p
        + ∑ j ∈ range J, ∏ i ∈ range J,
            (if (if i = j then (D.filter (fun p => blk p = i)).card = r j + 1
                  else (D.filter (fun p => blk p = i)).card ≤ r i) then
              (-1 : ℝ) ^ (D.filter (fun p => blk p = i)).card
                * ∏ p ∈ D.filter (fun p => blk p = i), g p else 0) := by
    intro D hD
    rw [mem_powerset] at hD
    rw [lamMinus_split, add_mul, sum_mul]
    congr 1
    apply sum_congr rfl
    intro j hj
    rw [prod_blocks_ite blk J (fun i n => if i = j then n = r j + 1 else n ≤ r i) g D
      (fun p hp => hP p (hD hp))]
    have hiff : inFacet blk J r D j ↔
        ∀ i ∈ range J, (if i = j then cnt blk D i = r j + 1 else cnt blk D i ≤ r i) := by
      constructor
      · rintro ⟨h1, h2⟩ i hi
        split_ifs with hij
        · subst hij; exact h1
        · exact h2 i (mem_range.1 hi) hij
      · intro h
        refine ⟨?_, fun i hi hij => ?_⟩
        · have := h j hj; simpa using this
        · have := h i (mem_range.2 hi); rwa [if_neg hij] at this
    by_cases hf : inFacet blk J r D j
    · rw [if_pos hf, if_pos (hiff.1 hf)]
    · rw [if_neg hf, if_neg (fun h => hf (hiff.2 h)), zero_mul]
  rw [sum_congr rfl hpt, sum_add_distrib, sum_lamPlus_eq P blk J r hP g, sum_comm, sub_eq_add_neg,
    ← sum_neg_distrib]
  congr 1
  apply sum_congr rfl
  intro j hj
  have hfac := sum_prod_blocks blk
    (fun i S => if (if i = j then S.card = r j + 1 else S.card ≤ r i) then
      (-1 : ℝ) ^ S.card * ∏ p ∈ S, g p else 0) (range J) P
    (fun p hp => mem_range.2 (hP p hp))
  rw [hfac, ← mul_prod_erase _ _ hj]
  simp only [if_true]
  have h1 : ∑ S ∈ (P.filter (fun p => blk p = j)).powerset,
      (if (S.card = r j + 1) then (-1 : ℝ) ^ S.card * ∏ p ∈ S, g p else 0)
        = -Esym g (block P blk j) (r j + 1) := by
    rw [sum_eq_eq_Esym, ((hr j).add_one).neg_one_pow, neg_one_mul]
    rfl
  rw [h1, neg_mul]
  congr 2
  apply prod_congr rfl
  intro i hi
  simp only [if_neg (ne_of_mem_erase hi)]
  exact sum_le_eq_Utr g _ _

/-- **B-sieve.** For even `r j` and every `H ⊆ P`:
`Σ_{D ⊆ H} λ⁻(D) ≤ [H = ∅] ≤ Σ_{D ⊆ H} λ⁺(D)`. -/
theorem lam_sieve (hP : ∀ p ∈ P, blk p < J) (hr : ∀ j, Even (r j)) (H : Finset ℕ) (hH : H ⊆ P) :
    ∑ D ∈ H.powerset, lamMinus blk J r D ≤ (if H = ∅ then 1 else 0) ∧
      (if H = ∅ then (1 : ℝ) else 0) ≤ ∑ D ∈ H.powerset, lamPlus blk J r D := by
  classical
  by_cases hHe : H = ∅
  · subst hHe
    have h0 : inPlus blk J r ∅ := fun j _ => by simp [cnt]
    simp [lamMinus, lamPlus, h0]
  rw [if_neg hHe]
  set g : ℕ → ℝ := fun p => if p ∈ H then 1 else 0 with hgdef
  have hsum : ∀ w : Finset ℕ → ℝ,
      ∑ D ∈ P.powerset, w D * ∏ p ∈ D, g p = ∑ D ∈ H.powerset, w D := by
    intro w
    have hprod : ∀ D : Finset ℕ, ∏ p ∈ D, g p = if D ⊆ H then 1 else 0 := by
      intro D
      split_ifs with h
      · exact prod_eq_one (fun p hp => by simp [g, h hp])
      · obtain ⟨p, hp, hpH⟩ := not_subset.1 h
        exact prod_eq_zero hp (by simp [g, hpH])
    simp_rw [hprod, mul_ite, mul_one, mul_zero]
    rw [← sum_filter]
    congr 1
    ext D
    simp only [mem_filter, mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.trans hH, h⟩⟩
  have hg01 : ∀ p, 0 ≤ g p ∧ g p ≤ 1 := by
    intro p; simp only [g]; split_ifs <;> norm_num
  have hB := fun j => bonferroni_weighted g (block P blk j) (fun p _ => hg01 p) (r j) (hr j)
  have hV0 : ∀ j, 0 ≤ Vp g (block P blk j) := fun j =>
    prod_nonneg (fun p _ => by linarith [hg01 p])
  have hU0 : ∀ j, 0 ≤ Utr g (block P blk j) (r j) := fun j => (hV0 j).trans (hB j).1
  have hE0 : ∀ j m, 0 ≤ Esym g (block P blk j) m := fun j m =>
    sum_nonneg (fun D _ => prod_nonneg (fun p _ => (hg01 p).1))
  obtain ⟨h, hh⟩ := nonempty_iff_ne_empty.2 hHe
  have hj0 : blk h < J := hP h (hH hh)
  have hVz : Vp g (block P blk (blk h)) = 0 :=
    prod_eq_zero (mem_filter.2 ⟨hH hh, rfl⟩) (by simp [g, hh])
  have hUE : Utr g (block P blk (blk h)) (r (blk h)) ≤ Esym g (block P blk (blk h)) (r (blk h) + 1) := by
    have := (hB (blk h)).2; rwa [hVz, zero_add] at this
  rw [← hsum, ← hsum, sum_lamMinus_eq P blk J r hP hr g, sum_lamPlus_eq P blk J r hP g]
  refine ⟨?_, prod_nonneg (fun j _ => hU0 j)⟩
  have hmem : blk h ∈ range J := mem_range.2 hj0
  have hPE : 0 ≤ ∏ i ∈ (range J).erase (blk h), Utr g (block P blk i) (r i) :=
    prod_nonneg (fun i _ => hU0 i)
  have step1 : ∏ j ∈ range J, Utr g (block P blk j) (r j)
      ≤ Esym g (block P blk (blk h)) (r (blk h) + 1)
          * ∏ i ∈ (range J).erase (blk h), Utr g (block P blk i) (r i) := by
    rw [← mul_prod_erase _ _ hmem]
    exact mul_le_mul_of_nonneg_right hUE hPE
  have step2 : Esym g (block P blk (blk h)) (r (blk h) + 1)
          * ∏ i ∈ (range J).erase (blk h), Utr g (block P blk i) (r i)
      ≤ ∑ j ∈ range J, Esym g (block P blk j) (r j + 1)
          * ∏ i ∈ (range J).erase j, Utr g (block P blk i) (r i) :=
    single_le_sum (f := fun j => Esym g (block P blk j) (r j + 1)
          * ∏ i ∈ (range J).erase j, Utr g (block P blk i) (r i))
      (fun j _ => mul_nonneg (hE0 j _) (prod_nonneg (fun i _ => hU0 i))) hmem
  linarith

end Erdos971.FL
