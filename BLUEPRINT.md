# Blueprint

Conditional proof of Erdős #971 (`Erdos971Statement` in `Erdos971/Statement.lean`) from the single axiom `fundamental_lemma` in
`Erdos971/Axioms.lean` (PNT, Mertens and Bombieri–Vinogradov are proved in `Bridge.lean` from PrimeNumberTheoremAnd and kimihiro64/bombieri-vinogradov). The argument follows the reviewed proof (`attack/971/01_structure.md` in the campaign
repo), re-organised for formalization: **all singular series are finite products over primes `p < z`**
(no infinite products or limits), and every `o(1)` is an explicit `Tendsto … atTop` in `q` with `u` fixed.

## 0. Notation (file `Defs.lean`)

For `q : ℕ` (the modulus) and `u : ℕ` (the fixed sieve parameter, `u ≥ 4`):

| Lean | math |
|---|---|
| `xq q` | `x = φ(q) log q` |
| `zq q u` | `z = x^{1/u}` |
| `Kq q` | `K = ⌊x/q⌋` |
| `reduced q` | `{a < q : gcd(a,q)=1}`, card `φ(q)` |
| `Nc q u a` | `N_a = #{p prime : z < p ≤ x, p ≡ a (q)}` |
| `Wc q u a` | `W_a = #{1 ≤ n ≤ x : gcd(n, P(z)) = 1, n ≡ a (q)}` |
| `A q u` | `A_q = x V(z) / φ(q)` |
| `gpair t p` | `0` if `p ∣ t`, else `1/(p-1)` (density for `p ± t`, `p` prime) |
| `S2 z t` | `∏_{p<z} (1 - gpair t p)/(1 - 1/p)` |
| `nu3 h k p` | number of distinct residues among `0, h, k` mod `p` |
| `S3 z h k` | `∏_{p<z} (1 - nu3 h k p / p)/(1 - 1/p)^3` |
| `Qz q z` | `∏_{p<z, p∣q} p/(p-1)` (`≤ q/φ(q)`) |

Averages are `E F = (1/φ(q)) Σ_{a ∈ reduced q} F a`.

## 1. Occupancy (`Occupancy.lean`, DONE, no axioms)

**L1.** `N ≤ W` integer-valued, `α ≤ E[(N-1)W]`, `E[W³] ≤ B` ⇒ `P(N=0) ≥ α²/B − E N + 1`.

## 2. Scale facts (`Scale.lean`; uses `mertens_product`, `pnt`)

- **S1** `∃ C, ∀ᶠ q, q/φ(q) ≤ C · log(log q)`. Proof: primes `p ∣ q` with `p > log q` number `≤ log q / log log q`,
  their factors multiply to `≤ 2`; primes `≤ log q` give `≤ 1/V(log q + 1) ≤ log(log q + 1)/c` (Mertens lower bound).
- **S2** `Kq q → ∞`; eventually `q ≤ xq q ≤ q log q`; `log q / log (xq q) → 1`.
- **S3** `zq q u / q → 0`, `(π(z) + ω(q)) / φ(q) → 0`, `x^{1/4}·(log x)^5 / φ(q) → 0`.
- **S4** `E N → 1` (PNT + S2 + S3).
- **S5** `A q u ≤ C_M · u` eventually (Mertens upper bound: `V(z) ≤ C_M u / log x`, and `x/(φ log x) ≤ 1`).
- **S6** `Li b − Li a ≥ (b − a)/log b` for `2 ≤ a ≤ b`.
- **S7** `π((1+c)x) − π(x) ≤ (c + o(1)) φ(q)` (PNT).

## 3. Finite singular-series estimates (`Singular.lean`; no axioms)

- **SS1 (Lemma 2, finite, lower bound).** There is `δ : ℕ → ℝ`, `δ K → 0`, such that for all `q ≥ 1`, all `z`, all `K`:
  `Σ_{1 ≤ h < K} (K − h) · S2 z (h q) ≥ (1 − δ K) · Qz q z · K²/2`.
  Proof: exact expansion `S2 z (hq) = Qz q z · b_q · C_{q,z} · 1_{b_q ∣ h} · Σ_{r ∣ h, r ∣ P'(z), gcd(r,q)=1} a(r)`,
  `a(r) = ∏_{ℓ∣r} 1/(ℓ−2)` over odd `ℓ`, `C_{q,z} Σ_r a(r)/r = 1` (finite telescoping identity
  `(1 − 1/(ℓ−1)²)(1 + 1/(ℓ(ℓ−2))) = 1`), `T_K(t) = Σ_{tm<K}(K − tm) ≥ K²/(2t) − K`, tail
  `Σ_{r > R} a(r)/r ≤ √3 Σ_{r>R} r^{−3/2}`, `R = √K`.
- **SS2 (Lemma 3).** `∃ C₃, ∀ q z K, Σ_{1 ≤ h < k ≤ K} S3 z (hq) (kq) ≤ C₃ · (Qz q z)² · K²`.
  Proof: local factor `≤ (1−1/p)^{−2}` at `p ∣ q`; `≤ 1` when residues distinct; `≤ 1 + 3/p` otherwise (`p ≥ 5`);
  `≤ 9` from `p ∈ {2,3}`; `f(n) = ∏_{p∣n}(1 + 3/p)`; AM–GM `f(h)f(k)f(k−h) ≤ (f(h)³ + f(k)³ + f(k−h)³)/3`;
  `Σ_{n ≤ K} f(n)³ ≤ C K`.
- **SS3** For `z > p`, `S2 z t = 0` when `t` odd and `2 < z`; `S2 z t ≤ Qz`-type bounds as needed.

## 4. Sieve applications (`Sieve.lean`; uses `fundamental_lemma`, `mertens_product`, `bombieri_vinogradov`)

Fix `(κ, K) = (1, K₁)` and `(3, K₃)` with absolute `K₁, K₃` (dimension conditions from Mertens + convergent
products); `η₁, η₃` from the axiom; level `z^{u/4} = x^{1/4}`.

- **SV1 (first moment).** `Σ_{a ∈ reduced q} W_a ≤ (1 + η₁(u/4)) x V(z) + x^{1/4}`. (Sift `{1..⌊x⌋}` by `g = 1/p`;
  `|r_d| ≤ 1`.)
- **SV2 (triples).** For `1 ≤ h < k ≤ K`: `#{n ≤ x : n, n+hq, n+kq all z-rough} ≤ (1 + η₃) x V(z)³ S3 z (hq) (kq) + 3·x^{1/4}·(1 + log x)²`
  (empty-set case when some `ν_p = p`).
- **SV3 (prime–rough, lower).** For `t = hq`, `1 ≤ h < K`, `t` even:
  `#{p prime : z < p ≤ x − t, (p + t, P(z)) = 1} ≥ (1 − η₁)(Li(x−t) − Li z) V(z) S2 z t − E_BV(t)` and
  `#{p prime : t < p ≤ x, (p − t, P(z)) = 1} ≥ (1 − η₁)(Li x − Li t) V(z) S2 z t − E_BV(t)`, with
  `Σ_{h<K} E_BV(hq) ≤ 4 K · C_A x (log x)^{−A}` via `bombieri_vinogradov`. For `t` odd both sides are trivial.

## 5. Moments (`Moments.lean`)

- **M1** `E[W³] ≤ B(u)` eventually. (`w³ ≤ 4(6·C(w,3) + w)`; `Σ_a C(W_a, 3) ≤ Σ_{h<k≤K} (SV2)`; SS2; S5; S3.)
- **M2** `E[N W] ≥ E N + (1 − η₁)(1 − o(1)) A − o(1)`. (Diagonal + shifted pairs `(p, p ± hq)`; remove `p ∣ q`;
  SV3; S6 with `x − hq ≥ q(K − h)`; SS1; `Qz ≥ (q/φ)(1 − 1/z)^u`; S2.)
- **M3** `E[(N − 1) W] ≥ 1/2` eventually, for `u` with `2 C_M u · η₁(u/4) ≤ 1/4` (exists since `s η₁(s) → 0`).

## 6. Assembly (`Main.lean`)

L1 with `α = 1/2`, `B = B(u)` ⇒ `#{a : N_a = 0} ≥ (1/(4B) − o(1)) φ`; subtract `π(z)` classes (S3) ⇒ no prime `≤ x`;
subtract `π((1+c)x) − π(x)` (S7) with `c = 1/(32B)` ⇒ no prime `≤ (1+c)x` in `≥ φ/(16B)` classes; Dirichlet
(`Nat.forall_exists_prime_gt_and_eq_mod`) ⇒ `leastCongruentPrime a q > (1+c) φ(q) log q`.

## Changes in v0.2 (Lean 4.33.1)

- `bombieri_vinogradov` (Li main term, variable heights) replaced by the proved `bv_pi`
  (fixed height `y ≤ x`, main term `π(y)/φ(r)`), derived from kimihiro64/bombieri-vinogradov.
- The prime–rough main terms in `sieve_dim1` are now `π(x−hq) − π(z) + π(x) − π(hq)`; `Moments`
  converts them with `pi_Li_close` (PNT + `li_asymp`), paying an error controlled by the new
  `sum_S2_le : Σ_{h<K} S2 z (hq) ≤ Qz · K`.

## Changes in v0.3

- The fundamental lemma is proved (`FL/`), following a logarithmically blocked Bonferroni sieve:
  blocks `B_j = {p : z^{2^{-(j+1)}} ≤ p < z^{2^{-j}}}`, truncation depths `r_j = 2n + 2b(j+1)`,
  upper weights on `{|D ∩ B_j| ≤ r_j ∀j}`, lower weights adding the disjoint one-overflow facets;
  Rankin bound `2^m E_m ≤ ∏(1+2g) ≤ V^{-2}`; η(s) = 8K³e^{-(log 2/4)s}. `erdos_971` now depends only
  on propext, Classical.choice, Quot.sound.
