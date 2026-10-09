/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Soundness.ActualCanonicalPullbackLemmas
import OAI.Computability.UniqueGames.Soundness.ActualPointAnswers

namespace OAI

section

namespace UniqueGamesTheorem.Clean.AnswerBridge

open Integration.BinaryLinear
open Reduction
open Soundness
open Soundness.RepeatedGameBounds
open Soundness.RawPartnerTarget

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : ℕ} {Q Id Name : Type}

abbrev FirstInput := ZeroInformation.FirstInput (Fin k) Q Id
abbrev SecondInput := ZeroInformation.SecondInput (Fin k) Q Id Name

abbrev SourceAnswer (k : ℕ) := {x : ActualHomogeneous.E k // ActualHomogeneous.tau x = 1}
abbrev TargetAnswer (J : Finset (Fin k)) := {v : RawPoint J // v none = 1}

abbrev PointStrategies (J : Finset (Fin k)) := IncidenceExtraction.Strategies
  (FirstInput (k := k) (Q := Q) (Id := Id))
  (SecondInput (k := k) (Q := Q) (Id := Id) (Name := Name))
  (SourceAnswer k) (TargetAnswer J)


/-- Convert a pair of genuine local point strategies into the ordinary answer
type used by the clean-coordinate local simulation. -/
def toOuterStrategy (J : Finset (Fin k)) (g : IncidenceExtraction.Incidence Id Name)
    (strategy : PointStrategies (Q := Q) (Id := Id) (Name := Name) J) :
    IncidenceExtraction.Strategies
      (FirstInput (k := k) (Q := Q) (Id := Id))
      (SecondInput (k := k) (Q := Q) (Id := Id) (Name := Name))
      (ActualProjection.FirstAnswer (Fin k)) (ActualProjection.SecondAnswer (Fin k)) where
  first qa := ActualPointAnswers.firstAnswer (fun j => g.rhs (qa.question j))
    (strategy.first qa).val
  second qb := ActualPointAnswers.secondAnswer
    (ActualPointAnswers.displayedRhs g.rhs qb.question) J (strategy.second qb).val


section RowEncoding

open Soundness.ConditionalIncidences Soundness.BinaryRowTransport
open scoped BigOperators

variable {D : Type} [AddCommGroup D] [Module F2 D]

/-- A basis supplies the required coordinates for every finite-dimensional
combined advice space; this choice is independent of the equation questions. -/
def finiteCoordinates [FiniteDimensional F2 D] :
    D ≃ₗ[F2] (Fin (Module.finrank F2 D) → F2) :=
  (Module.finBasis F2 D).equivFun

/-- The coordinate map is a bijection all the way to the actual bit-row type. -/
def bitsCoordinatesEquiv (coordinates : D ≃ₗ[F2] (Q → F2)) :
    D ≃ ZeroInformation.Bits Q :=
  coordinates.toEquiv.trans rowBitsEquiv


def coefficientsEquiv (coordinates : D ≃ₗ[F2] (Q → F2)) (J : Finset (Fin k)) :
    RawCoefficients J D ≃ RawCoefficients J (ZeroInformation.Bits Q) :=
  Equiv.piCongrRight (fun _ => bitsCoordinatesEquiv coordinates)


/-- Transport a local strategy on genuine row maps to the complete bit-row
input type. The same fixed public data may be closed over in both policies.
All remaining inputs are private to the respective prover. -/
def rowPointStrategies (coordinates : D ≃ₗ[F2] (Q → F2))
    (J : Finset (Fin k)) (rhs : Id → Bool)
    (first : (Fin k → Id) → (ActualHomogeneous.E k →ₗ[F2] D) → SourceAnswer k)
    (second : (Fin k → Sum Id Name) → (RawPoint J →ₗ[F2] D) → TargetAnswer J) :
    PointStrategies (Q := Q) (Id := Id) (Name := Name) J where
  first qa := first qa.question
    (coordinates.symm.toLinearMap.comp (ActualInputRows.firstMap rhs qa))
  second qb := second qb.question
    (coordinates.symm.toLinearMap.comp (ActualInputRows.secondMap J qb))


/-- A default actual target answer is used only for unsupported displayed
questions, which never occur in the experiment. -/
def defaultTargetAnswer (J : Finset (Fin k)) : TargetAnswer J :=
  ⟨Pi.single none 1, by simp⟩

/-- Extend a policy defined on supported private questions to a total local
answer function. The support decision uses only the displayed question. -/
def extendSupportedPolicy (J : Finset (Fin k)) (names : Id → Fin 3 → Name)
    (policy : RawPrivateTable.SupportedV J names → (RawPoint J →ₗ[F2] D) → TargetAnswer J)
    (question : Fin k → Sum Id Name) (Y : RawPoint J →ₗ[F2] D) : TargetAnswer J :=
  if h : question ∈ Set.range
      (fun e : RawPrivateTable.Extension k Id => RawPrivateTable.displayed J names e.1 e.2)
  then policy ⟨question, h⟩ Y else defaultTargetAnswer J


end RowEncoding

end
end UniqueGamesTheorem.Clean.AnswerBridge

end

end OAI
