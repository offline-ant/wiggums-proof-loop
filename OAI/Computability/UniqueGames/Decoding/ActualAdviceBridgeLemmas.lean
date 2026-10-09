/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Decoding.AnswerBridge
import OAI.Computability.UniqueGames.Decoding.Experiment
import OAI.Computability.UniqueGames.Decoding.IncidenceGap
import OAI.Computability.UniqueGames.Decoding.NativeExperiment
import OAI.Computability.UniqueGames.Repetition.TensorAlgebraLemmas
import OAI.Computability.UniqueGames.Soundness.ActualCanonicalPullbackLemmas

namespace OAI

noncomputable section

namespace UniqueGamesTheorem

namespace Clean.ActualAdviceBridge

open scoped BigOperators
open Foundations.Games Integration.BinaryLinear Reduction
open Soundness Soundness.ConditionalIncidences Soundness.ConditionalGameLaw
open Soundness.RawPartnerTarget Soundness.BinaryRowTransport
open AnswerBridge

attribute [local instance] Classical.propDecidable

variable {k : ℕ} {D Q O N : Type} [AddCommGroup D] [Module F2 D]

def indexSlot (i : Fin 3) : PartnerProjection.Slot :=
  if i = 0 then .first else if i = 1 then .second else .third

@[simp] theorem slotIndex_indexSlot (i : Fin 3) :
    ConcreteExtraction.slotIndex (indexSlot i) = i := by
  fin_cases i <;> rfl

def projection (g : IncidenceExtraction.Incidence O N)
    (J : Finset (Fin k)) (draw : Draw (Fin k) O) :
    ActualHomogeneous.E k →ₗ[F2] RawPoint J :=
  rawProjection (fun j => g.rhs (draw j).1) J (fun j => indexSlot (draw j).2)

def displayedQuestion (g : IncidenceExtraction.Incidence O N)
    (J : Finset (Fin k)) (draw : Draw (Fin k) O) : RawPrivateTable.SupportedV J g.name :=
  RawPrivateTable.supported J g.name (fun j => (draw j).1) (fun j => indexSlot (draw j).2)

def encodedMapCoefficients (coordinates : D ≃ₗ[F2] (Q → F2))
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) :
    RawCoefficients J (ZeroInformation.Bits Q) :=
  rowCoefficients J (gammaOfRawMap J (coordinates.toLinearMap.comp Y))

theorem sample_question [Fintype Q] [DecidableEq Q]
    (g : IncidenceExtraction.Incidence O N) (J : Finset (Fin k))
    (gamma : RawCoefficients J (ZeroInformation.Bits Q)) (draw : Draw (Fin k) O) :
    (actualSecond J g.name gamma draw).question = (displayedQuestion g J draw).val := by
  funext j
  simp [actualSecond, ZeroInformation.secondInput, ZeroInformation.partnerQuestion,
    membershipBool, displayedQuestion, RawPrivateTable.supported,
    RawPrivateTable.displayed]


variable [Fintype Q] [DecidableEq Q] [Fintype O] [DecidableEq O]
  [Fintype N] [DecidableEq N] [Fintype D]


def mapBitsEquiv (coordinates : D ≃ₗ[F2] (Q → F2)) (J : Finset (Fin k)) :
    (RawPoint J →ₗ[F2] D) ≃ RawCoefficients J (ZeroInformation.Bits Q) :=
  (RawMapLaw.rawMapEquiv J D).symm.trans (coefficientsEquiv coordinates J)

theorem uniform_maps_to_bits (coordinates : D ≃ₗ[F2] (Q → F2))
    (J : Finset (Fin k)) (F : RawCoefficients J (ZeroInformation.Bits Q) → ℝ) :
    (FiniteDistribution.uniform (RawPoint J →ₗ[F2] D)).expectation
      (fun Y => F (encodedMapCoefficients coordinates J Y)) =
      (FiniteDistribution.uniform (RawCoefficients J (ZeroInformation.Bits Q))).expectation F := by
  simp only [FiniteDistribution.expectation_uniform, ← Fintype.expect_eq_sum_div_card]
  exact Fintype.expect_equiv (mapBitsEquiv coordinates J) _ F (fun _ => rfl)


theorem expectation_mono {X : Type} [Fintype X] (μ : FiniteDistribution X)
    {f g : X → ℝ} (h : ∀ x, f x ≤ g x) : μ.expectation f ≤ μ.expectation g := by
  unfold FiniteDistribution.expectation
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonnegative x)

end Clean.ActualAdviceBridge

namespace Clean.Bound

open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalSimulation
open Experiment

variable {R O N : Type} [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

omit [DecidableEq O] [DecidableEq N] in
/-- The precise rate is obtained from the proved ordinary projection-game
bound, with no question-set or alphabet parameter in its base. -/
theorem repeated_incidence_value_le
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5) (n : ℕ) :
    ((incidenceGame g ((IncidenceGap.slotLaw ω).pushforward (incidence g.name))).repetition n).value ≤
      (1 - (1 : ℝ) / 3600) ^ n := by
  change ((IncidenceGap.game g ω).repetition n).value ≤ _
  exact Repetition.clean_repetition_value (IncidenceGap.game g ω)
    (IncidenceGap.game_isProjection g ω distinct) n
    (IncidenceGap.game_value_le_fourteen_fifteenths g ω distinct hopt)


/-- A uniform bound on visible advice dimension makes the estimate independent
of the sampled map `A`. Apply with `Coefficient R ≃ W × range A`. -/
theorem clean_success_le_dimension (k : ℕ) (g : IncidenceExtraction.Incidence O N)
    (ω : FiniteDistribution O) (extraLaw : FiniteDistribution (Additional k R))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (strategy : Additional k R → SparseSeed k R → LocalStrategies k R O N)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5)
    (dimW rs : ℕ) (hcard : Fintype.card (Coefficient R) ≤ 2 ^ (dimW + rs)) :
    success k (IncidenceGap.slotLaw ω) g extraLaw β hβ₀ hβ₁ strategy ≤
      (1 - (β / (2 : ℝ) ^ (dimW + rs)) / 3600) ^ k := by
  have comparison := clean_mask_moment_le_dimension β hβ₀ hβ₁
    (ZeroInformation.zero : Coefficient R) k dimW rs hcard
  rw [clean_mask_moment] at comparison
  have estimate := success_le_of_repetition k (IncidenceGap.slotLaw ω) g extraLaw
    β hβ₀ hβ₁ strategy distinct (1 - (1 : ℝ) / 3600)
    (repeated_incidence_value_le g ω distinct hopt)
  exact estimate.trans comparison

theorem native_clean_success_le_dimension (k : ℕ)
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (strategy : NativeExperiment.MaskStrategy k R O N)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5)
    (dimW rs : ℕ) (hcard : Fintype.card (Coefficient R) ≤ 2 ^ (dimW + rs)) :
    NativeExperiment.success k (IncidenceGap.slotLaw ω) g β hβ₀ hβ₁ strategy ≤
      (1 - (β / (2 : ℝ) ^ (dimW + rs)) / 3600) ^ k := by
  rw [NativeExperiment.success_eq_flat]
  exact clean_success_le_dimension k g ω (FiniteDistribution.uniform (Additional k R))
    β hβ₀ hβ₁ (NativeExperiment.liftStrategy strategy) distinct hopt dimW rs hcard

end Clean.Bound

end UniqueGamesTheorem

end

end OAI
