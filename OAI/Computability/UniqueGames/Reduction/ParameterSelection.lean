/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Repetition.AnalyticCheegerLemmas

namespace OAI.UniqueGamesTheorem.ParameterSelection

/-! Fix the repetition exponent and rational noise budget before choosing the
matrix alphabet. The input already has uniform occurrence weights, so there is
no rounding tolerance or copy count to choose. -/

noncomputable section

structure OuterParameters (ε δ : ℝ) where
  epsilon0 : ℚ
  delta0 : ℚ
  epsilon0_pos : 0 < epsilon0
  delta0_pos : 0 < delta0
  epsilon0_le : (epsilon0 : ℝ) ≤ ε
  delta0_le : (delta0 : ℝ) ≤ δ
  repetitions : ℕ
  repetitions_pos : 0 < repetitions
  soundness_rate : (1 - (1 : ℝ) / 10240000) ^ repetitions ≤ delta0
  pStar : ℚ
  pStar_pos : 0 < pStar
  pStar_lt_one : pStar < 1
  noise_budget : pStar ≤ epsilon0 / repetitions

/-- The noise budget is simply the smaller of a fixed constant and the
completeness allowance; it need not be a reciprocal integer. -/
theorem exists_outerParameters (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    Nonempty (OuterParameters ε δ) := by
  obtain ⟨ε₀, hε₀, hεbound⟩ := exists_rat_btwn hε
  obtain ⟨δ₀, hδ₀, hδbound⟩ := exists_rat_btwn hδ
  have hεq : (0 : ℚ) < ε₀ := by exact_mod_cast hε₀
  have hδq : (0 : ℚ) < δ₀ := by exact_mod_cast hδ₀
  obtain ⟨t, ht, hrate⟩ := Repetition.exists_final_repetition_count hδ₀
  let p := min (1 / 2 : ℚ) (ε₀ / t)
  have hp : 0 < p := lt_min (by norm_num)
    (div_pos hεq (by exact_mod_cast ht))
  exact ⟨⟨ε₀, δ₀, hεq, hδq, hεbound.le, hδbound.le,
    t, ht, hrate, p, hp, (min_le_left _ _).trans_lt (by norm_num),
    min_le_right _ _⟩⟩

namespace OuterParameters

variable {ε δ : ℝ} (P : OuterParameters ε δ)

theorem exists_parity_error (k : ℕ) (hk : 0 < k) :
    ∃ ξ : ℚ, 0 < ξ ∧ ξ < 1 / 100 ∧
      ξ < P.epsilon0 / (2 * k * P.repetitions) := by
  have hdenom : (0 : ℚ) < 2 * k * P.repetitions := by
    exact mul_pos (mul_pos (by norm_num) (by exact_mod_cast hk))
      (by exact_mod_cast P.repetitions_pos)
  let ξ := min (1 / 100 : ℚ) (P.epsilon0 / (2 * k * P.repetitions)) / 2
  have hmin : 0 < min (1 / 100 : ℚ) (P.epsilon0 / (2 * k * P.repetitions)) :=
    lt_min (by norm_num) (div_pos P.epsilon0_pos hdenom)
  refine ⟨ξ, div_pos hmin (by norm_num), ?_, ?_⟩
  · have hle := min_le_left (1 / 100 : ℚ) (P.epsilon0 / (2 * k * P.repetitions))
    dsimp [ξ]
    linarith
  · have hle := min_le_right (1 / 100 : ℚ) (P.epsilon0 / (2 * k * P.repetitions))
    dsimp [ξ]
    linarith

/-- Both matrix-test completeness losses fit the fixed rational budget. -/
theorem matrix_error_budget (k : ℕ) (hk : 0 < k) (ξ : ℚ)
    (hξ : ξ ≤ P.epsilon0 / (2 * k * P.repetitions)) :
    (k : ℚ) * ξ + P.pStar / 2 ≤ P.epsilon0 / P.repetitions := by
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have htq : (0 : ℚ) < P.repetitions := by exact_mod_cast P.repetitions_pos
  have hx := (le_div_iff₀ (mul_pos (mul_pos (by norm_num) hkq) htq)).mp hξ
  have hp := (le_div_iff₀ htq).mp P.noise_budget
  apply (le_div_iff₀ htq).mpr
  nlinarith

end OuterParameters
end
end OAI.UniqueGamesTheorem.ParameterSelection
