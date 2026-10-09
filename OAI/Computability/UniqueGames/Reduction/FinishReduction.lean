/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Games.ProductSoundness
import OAI.Computability.UniqueGames.Machines.MachineProductRuntime
import OAI.Computability.UniqueGames.Machines.MachineSubdivisionBodySpecLemmas
import OAI.Computability.UniqueGames.Reduction.ParameterSelection

namespace OAI.UniqueGamesTheorem.FinishReduction

open UniqueGamesTheorem.Foundations Target
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Integration
open Explicit

noncomputable section

/-- Subdivide the uniform matrix instance to make its endpoints simple and
bipartite, then repeat. No occurrence copying or rounding stage is necessary.
All parameters and machines are fixed before the original raw input. -/
def of_matrix_reduction {ε δ : ℝ} (P : ParameterSelection.OuterParameters ε δ)
    {q s : ℕ} (hq : 2 ≤ q) (hs : 1 ≤ s)
    (coordinates : Fin q ≃ BinaryLinear.Vector s)
    (matrix : List Bool → Instance q)
    (translations : ∀ input, TranslationTarget.IsTranslationInstance coordinates (matrix input))
    (computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      gameBits matrix)
    (finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm)
    (d : ℚ) (hd : d ≤ P.epsilon0 / P.repetitions)
    (complete : ∀ input, BinaryLanguage.language input →
      1 - (d : ℝ) ≤ InstanceValue.value (matrix input))
    (sound : ∀ input, ¬BinaryLanguage.language input →
      InstanceValue.value (matrix input) ≤ 99 / 100) :
    MachineOutputContract.BinaryGapReduction ε δ := by
  classical
  have hqpos : 0 < q := by omega
  letI : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
  let base := fun input => SubdivisionTarget.subdivide (matrix input)
  let basePresentation := fun input => SubdivisionTarget.simpleBipartite (matrix input)
  let baseMachine := MachineSubdivisionCompose.translationComputableInPolyTime
    coordinates computation translations
  have baseFinite : MachineFiniteAlphabet.FiniteAlphabet baseMachine.tm :=
    MachineSubdivisionCompose.finiteAlphabet computation
      (fun input => MachineSubdivisionCorrespondence.translations_involutive
        coordinates (matrix input) (translations input)) finiteAlphabet
  let output := fun input => ProductPaddedOutput.output (base input)
    (basePresentation input) P.repetitions P.repetitions_pos
  let outputMachine := MachineProductRuntime.compose baseMachine basePresentation
    P.repetitions P.repetitions_pos
  have hqout : 2 ≤ q ^ P.repetitions :=
    hq.trans (Nat.le_self_pow P.repetitions_pos.ne' q)
  have hqoutpos : 0 < q ^ P.repetitions := by omega
  have baseValue (input : List Bool) :
      InstanceValue.value (base input) =
        1 - (1 - InstanceValue.value (matrix input)) / 4 :=
    SubdivisionTarget.value_eq (matrix input) hqpos
  refine {
    alphabet := q ^ P.repetitions
    alphabetAtLeastTwo := hqout
    dimension := s * P.repetitions
    dimensionPositive := by
      have hpos := Nat.mul_pos (show 0 < s by omega) P.repetitions_pos
      omega
    coordinates := ProductPaddedOutput.finalCoordinates coordinates P.repetitions
    construct := output
    simpleBipartite := fun input => ProductPaddedOutput.simpleBipartite
      (base input) (basePresentation input) P.repetitions P.repetitions_pos
    translations := fun input => ProductPaddedOutput.output_translations
      (base input) (basePresentation input) coordinates
      (SubdivisionTarget.subdivide_translation coordinates (matrix input)
        (translations input)) P.repetitions P.repetitions_pos
    computation := outputMachine
    finiteAlphabet := MachineProductRuntime.compose_finiteAlphabet
      baseMachine basePresentation P.repetitions P.repetitions_pos baseFinite
    completeness := ?_
    soundness := ?_
  }
  · intro input yes
    apply (InstanceValue.exists_rate_ge_iff (output input) hqoutpos (1 - ε)).mpr
    have hproduct := ProductPaddedOutput.output_completeness (base input)
      (basePresentation input) P.repetitions P.repetitions_pos
      (error := 1 - InstanceValue.value (base input)) (by linarith)
    have ht : (0 : ℝ) < P.repetitions := by exact_mod_cast P.repetitions_pos
    have hdreal : (d : ℝ) * P.repetitions ≤ (P.epsilon0 : ℝ) := by
      exact (le_div_iff₀ ht).mp (by exact_mod_cast hd)
    have hloss := mul_le_mul_of_nonneg_left (complete input yes) ht.le
    rw [baseValue input] at hproduct
    have hε0 : (0 : ℝ) ≤ P.epsilon0 := by exact_mod_cast P.epsilon0_pos.le
    have hε := P.epsilon0_le
    nlinarith
  · intro input no
    apply (InstanceValue.forall_rate_le_iff (output input) hqoutpos δ).mpr
    have hbase : InstanceValue.value (base input) ≤ 1 - 1 / 800 := by
      rw [baseValue input]
      linarith [sound input no]
    exact (ProductPaddedOutput.output_soundness (base input) (basePresentation input)
      P.repetitions P.repetitions_pos P.soundness_rate hbase).trans P.delta0_le

end
end OAI.UniqueGamesTheorem.FinishReduction
