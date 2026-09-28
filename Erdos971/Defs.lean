import Erdos971.Axioms

/-!
# Erdős #971 — objects of the proof (see `BLUEPRINT.md` §0)
-/

open Real Finset Filter Topology

namespace Erdos971

/-- `x = φ(q) log q`. -/
noncomputable def xq (q : ℕ) : ℝ := (q.totient : ℝ) * Real.log q

/-- `z = x^{1/u}`. -/
noncomputable def zq (q u : ℕ) : ℝ := xq q ^ ((1 : ℝ) / u)

/-- `K = ⌊x/q⌋`. -/
noncomputable def Kq (q : ℕ) : ℕ := ⌊xq q / q⌋₊

/-- Reduced residues `a < q`. -/
def reduced (q : ℕ) : Finset ℕ := (range q).filter (fun a => Nat.Coprime a q)

/-- `N_a = #{p prime : z < p ≤ x, p ≡ a (mod q)}`. -/
noncomputable def Nc (q u a : ℕ) : ℕ :=
  ((Icc 1 ⌊xq q⌋₊).filter (fun p : ℕ => p.Prime ∧ zq q u < (p : ℝ) ∧ p ≡ a [MOD q])).card

/-- `W_a = #{1 ≤ n ≤ x : gcd(n, P(z)) = 1, n ≡ a (mod q)}`. -/
noncomputable def Wc (q u a : ℕ) : ℕ :=
  ((Icc 1 ⌊xq q⌋₊).filter (fun n : ℕ => Nat.Coprime n (Pz (zq q u)) ∧ n ≡ a [MOD q])).card

/-- `A_q = x V(z) / φ(q)`. -/
noncomputable def Aq (q u : ℕ) : ℝ := xq q * V (zq q u) / q.totient

/-- Average over reduced residues. -/
noncomputable def avg (q : ℕ) (F : ℕ → ℝ) : ℝ := (∑ a ∈ reduced q, F a) / q.totient

/-- Sieve density for `p ± t` with `p` prime: `0` if `p ∣ t`, else `1/(p-1)`. -/
noncomputable def gpair (t p : ℕ) : ℝ := if p ∣ t then 0 else 1 / ((p : ℝ) - 1)

/-- Truncated pair singular series `𝔖_z(t) = ∏_{p<z} (1 - gpair t p)/(1 - 1/p)`. -/
noncomputable def S2 (z : ℝ) (t : ℕ) : ℝ :=
  ∏ p ∈ primesLT z, (1 - gpair t p) / (1 - 1 / (p : ℝ))

/-- Number of distinct residues among `0, h, k` modulo `p`. -/
def nu3 (h k p : ℕ) : ℕ := ({0, h % p, k % p} : Finset ℕ).card

/-- Truncated triple singular series `𝔖_{z,3}(0,h,k)`. -/
noncomputable def S3 (z : ℝ) (h k : ℕ) : ℝ :=
  ∏ p ∈ primesLT z, (1 - (nu3 h k p : ℝ) / p) / (1 - 1 / (p : ℝ)) ^ 3

/-- `Qz q z = ∏_{p<z, p ∣ q} p/(p-1)`. -/
noncomputable def Qz (q : ℕ) (z : ℝ) : ℝ :=
  ∏ p ∈ (primesLT z).filter (· ∣ q), (p : ℝ) / ((p : ℝ) - 1)

end Erdos971
