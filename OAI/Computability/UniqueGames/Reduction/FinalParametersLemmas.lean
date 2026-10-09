/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import OAI.Computability.UniqueGames.Games.Swap
import OAI.Computability.UniqueGames.Repetition.TensorAlgebraLemmas
import OAI.Computability.UniqueGames.Soundness.PartnerLinearLemmas

namespace OAI

section

/-! Rational repetition parameters for the source gap amplification. -/

namespace UniqueGamesTheorem.Integration.SourceParameters

def rate (gap : ℚ) : ℚ := 1 - gap ^ 3 / 100000

theorem rate_bounds {gap : ℚ} (hgap : 0 < gap) (hgap1 : gap ≤ 1) :
    0 < rate gap ∧ rate gap < 1 := by
  have hcube : gap ^ 3 ≤ 1 := pow_le_one₀ hgap.le hgap1
  have hcubePos : 0 < gap ^ 3 := pow_pos hgap _
  constructor <;> unfold rate <;> linarith

/-- Swapped projection games have an alphabet-independent quadratic rate,
which is stronger than the fixed rational rate used by the source search. -/
theorem game_repetition_rate {Q₁ Q₂ A₁ A₂ : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
    [Nonempty A₁] [Nonempty A₂]
    (G : UniqueGamesTheorem.Foundations.Games.Game Q₁ Q₂ A₁ A₂)
    (hG : UniqueGamesTheorem.Repetition.IsProjection G.swap)
    {gap : ℚ} (hgap : 0 < gap) (hgap1 : gap < 1)
    (hvalue : G.value ≤ 1 - (gap : ℝ)) (n : Nat) :
    (G.repetition n).value ≤ (rate gap : ℝ) ^ n := by
  have hg : (0 : ℝ) < gap := by exact_mod_cast hgap
  have hg1 : (gap : ℝ) < 1 := by exact_mod_cast hgap1
  have h := UniqueGamesTheorem.Repetition.projection_repetition_value
    G.swap hG n hg hg1 (by rwa [G.value_swap])
  rw [G.swap_repetition, (G.repetition n).value_swap] at h
  apply h.trans
  apply pow_le_pow_left₀ (by nlinarith [sq_nonneg (gap : ℝ)])
  simp only [rate, Rat.cast_sub, Rat.cast_one, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
  nlinarith [mul_nonneg (sq_nonneg (gap : ℝ)) (show 0 ≤ 1 - (gap : ℝ) by linarith)]

def sourceThreshold (D : Nat) (δ : ℚ) : ℚ := 4 * (D : ℚ)⁻¹ * δ ^ 2

theorem sourceThreshold_pos {D : Nat} (hD : 0 < D) {δ : ℚ} (hδ : 0 < δ) :
    0 < sourceThreshold D δ := by
  unfold sourceThreshold
  positivity

theorem exists_repetition_length {gap δ : ℚ} (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hδ : 0 < δ) {D : Nat} (hD : 0 < D) :
    ∃ u : Nat, 0 < u ∧ (rate gap) ^ u < sourceThreshold D δ :=
  UniqueGamesTheorem.Soundness.RepetitionUpper.exists_power_lt (rate gap) (sourceThreshold D δ)
    (rate_bounds hgap hgap1).1.le (rate_bounds hgap hgap1).2 (sourceThreshold_pos hD hδ)

/-- Exact rational search, independent of the input formula. -/
def repetitionLength (gap δ : ℚ) (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hδ : 0 < δ) (D : Nat) (hD : 0 < D) : Nat :=
  Nat.find (exists_repetition_length hgap hgap1 hδ hD)

theorem repetitionLength_spec (gap δ : ℚ) (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hδ : 0 < δ) (D : Nat) (hD : 0 < D) :
    0 < repetitionLength gap δ hgap hgap1 hδ D hD ∧
      rate gap ^ repetitionLength gap δ hgap hgap1 hδ D hD < sourceThreshold D δ :=
  Nat.find_spec (exists_repetition_length hgap hgap1 hδ hD)

theorem repetitionLength_real_bound (gap δ : ℚ) (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hδ : 0 < δ) (D : Nat) (hD : 0 < D) :
    (rate gap : ℝ) ^ repetitionLength gap δ hgap hgap1 hδ D hD ≤
      4 * (D : ℝ)⁻¹ * (δ : ℝ) ^ 2 := by
  have h := (repetitionLength_spec gap δ hgap hgap1 hδ D hD).2.le
  unfold sourceThreshold at h
  have hr := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hr
  exact hr

end UniqueGamesTheorem.Integration.SourceParameters

end

end OAI
