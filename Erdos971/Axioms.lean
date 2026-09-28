import Mathlib

/-!
# Erdős #971 — the analytic inputs, stated as axioms

This file contains the **only** unproved statements of the project. Each is a standard theorem
of analytic number theory, stated in a form that is *weaker than or equal to* the textbook form
(so that the textbook theorem implies the axiom as written). Nothing else in the project uses
`axiom` or `sorry`; `#print axioms Erdos971.erdos_971` must list exactly the four axioms below
together with Lean's standard `propext`, `Classical.choice`, `Quot.sound`.

| axiom | literature |
|---|---|
| `pnt` | Hadamard (1896), de la Vallée Poussin (1896) |
| `mertens_product` | Mertens (1874); e.g. Hardy–Wright Thm 429, or Montgomery–Vaughan Thm 2.7 |
| `bombieri_vinogradov` | Bombieri (1965), A. I. Vinogradov (1965); Iwaniec–Kowalski Thm 17.1, Davenport ch. 28 |
| `fundamental_lemma` | Iwaniec–Kowalski Thm 6.9 / Cor 6.10; Friedlander–Iwaniec, *Opera de Cribro*, §6.5;
  Halberstam–Richert Thm 2.5 / 7.? |
-/

open Real Finset Filter Topology

namespace Erdos971

/-- The primes `p < z`, as a finset of naturals. -/
noncomputable def primesLT (z : ℝ) : Finset ℕ :=
  (Finset.range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) < z)

/-- `P(z) = ∏_{p < z} p`. -/
noncomputable def Pz (z : ℝ) : ℕ := ∏ p ∈ primesLT z, p

/-- `V(z) = ∏_{p < z} (1 - 1/p)`. -/
noncomputable def V (z : ℝ) : ℝ := ∏ p ∈ primesLT z, (1 - 1 / (p : ℝ))

/-- `π(y; r, b)`: the number of primes `p ≤ y` with `p ≡ b (mod r)`. -/
noncomputable def piAP (y : ℝ) (r b : ℕ) : ℕ :=
  ((Finset.range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ b [MOD r])).card

/-- The logarithmic integral `Li(y) = ∫_2^y dt / log t`. -/
noncomputable def Li (y : ℝ) : ℝ := ∫ t in (2 : ℝ)..y, 1 / Real.log t

/-- **Prime number theorem**: `π(x) log x / x → 1`. -/
axiom pnt :
  Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x) atTop (𝓝 1)

/-- **Mertens' product theorem**, in the weak two-sided form `V(z) ≍ 1 / log z`
(Mertens proved the asymptotic `V(z) ∼ e^{-γ} / log z`). -/
axiom mertens_product :
  ∃ c C : ℝ, 0 < c ∧ ∀ z : ℝ, 2 ≤ z → c / Real.log z ≤ V z ∧ V z ≤ C / Real.log z

/-- **Bombieri–Vinogradov**, weak form: moduli only up to `x^{1/4}` (the theorem allows
`x^{1/2} (log x)^{-B}`), maximum over reduced residues `b r` and over `2 ≤ y r ≤ x`
(encoded by letting the residue and the height be arbitrary functions of the modulus). -/
axiom bombieri_vinogradov (A : ℝ) (hA : 0 < A) :
  ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → ∀ (b : ℕ → ℕ) (y : ℕ → ℝ),
    (∀ r, Nat.Coprime (b r) r) → (∀ r, 2 ≤ y r ∧ y r ≤ x) →
    ∑ r ∈ Finset.Icc 1 ⌊x ^ ((1 : ℝ) / 4)⌋₊,
        |(piAP (y r) r (b r) : ℝ) - Li (y r) / (r.totient : ℝ)|
      ≤ C * x / (Real.log x) ^ A

/-- **Fundamental lemma of sieve theory** (upper and lower bound), in consequence form.

A finite family `(f i)_{i ∈ A}` of naturals is sifted by the primes `p < z`. The density `g` on
primes satisfies `0 ≤ g p < 1` and the dimension condition with parameters `κ, K`. With
`g(d) = ∏_{p ∣ d} g p`, level `D = z^s`, and remainders
`r_d = #{i ∈ A : d ∣ f i} - X g(d)`, the sifted count `S = #{i ∈ A : (f i, P(z)) = 1}` satisfies
`S ≤ X V_g (1 + η s) + Σ_{d ∣ P(z), d ≤ D} |r_d|` and `S ≥ X V_g (1 - η s) - Σ …`,
where `η` depends only on `κ, K` and `s · η s → 0` (the proof needs the error to beat a factor
`≍ s`). Iwaniec–Kowalski Cor. 6.10 gives this with `η s = e^{9κ+1-s} K^{10}` for `s ≥ 9κ + 1`. -/
axiom fundamental_lemma (κ K : ℝ) (hκ : 0 < κ) (hK : 1 ≤ K) :
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
      S ≤ X * Vg * (1 + η s) + R ∧ X * Vg * (1 - η s) - R ≤ S

end Erdos971
