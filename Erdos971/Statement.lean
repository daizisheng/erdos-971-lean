import Mathlib

/-!
# Erdős #971 — the statement

Copied verbatim (definitions and statement) from
`google-deepmind/formal-conjectures`, `FormalConjectures/ErdosProblems/971.lean`, with
`answer(sorry)` resolved to `True`.
-/

open Filter Finset Real

namespace Erdos971

/-- `leastCongruentPrime a d` is the least prime congruent to `a` modulo `d`. -/
noncomputable def leastCongruentPrime (a d : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ p ≡ a [MOD d]}

/-- The affirmative answer to Erdős #971. -/
def Erdos971Statement : Prop :=
  ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ d in atTop,
    C * (d.totient : ℝ) ≤
      #{a < d | a.Coprime d ∧ (leastCongruentPrime a d : ℝ) > (1 + c) * d.totient * log d}

end Erdos971
