/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Foundations.FiniteTrialsLemmas
import OAI.Computability.UniqueGames.Soundness.ActualCanonicalPullbackLemmas
import OAI.Computability.UniqueGames.Soundness.ExpectationComparisonLemmas
import OAI.Computability.UniqueGames.Foundations.CoordinateSampling
import OAI.Computability.UniqueGames.Soundness.ZeroInformationLemmas

namespace OAI

section

/-!
# Exact partner-map laws in shared raw target coordinates

Inactive positions do not use a retained slot. Replacing their slots leaves
both the concrete partner projection and the shared raw projection unchanged.

The row/column expectation identity below transports the two actual uniform
map samples through the target coordinate equivalence independently. It is an
exact identity for every observable of the pulled-back maps; it requires no
trace, character, or naturality hypotheses.
-/

namespace UniqueGamesTheorem.Soundness.RawTargetLaw

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Reduction
open PartnerProjection PartnerMapCoordinates RawPartnerTarget


end UniqueGamesTheorem.Soundness.RawTargetLaw

end

section

/-!
# Concrete finite averaging for the projection upper bound

The coefficient samples here are actual functions `Fin t → (Fin m → ZMod 2)`.
Their law is the normalized finite uniform sum over all such functions. The
binomial moment formula is proved from this sum, without an independence or
binomial-distribution premise.
-/

namespace UniqueGamesTheorem.Soundness.RepeatedGameBounds

open scoped BigOperators

noncomputable section


/-! ## Actual weighted winning probabilities under a local simulation -/

open Foundations.Games

namespace Simulation

abbrev PredicateGame := IncidenceExtraction.Game
abbrev PredicateStrategies := IncidenceExtraction.Strategies

variable {QA QB A B OA OB X Y : Type}
  [Fintype QA] [Fintype QB] [Fintype A] [Fintype B]
  [Fintype OA] [Fintype OB] [Fintype X] [Fintype Y]

/-- Pass a Boolean verifier predicate to the already checked deterministic
local-reconstruction and incidence-extraction interface. -/
def predicateGame (G : Game QA QB A B) : PredicateGame QA QB A B :=
  ⟨fun qa qb a b => G.accepts qa qb a b = true⟩

def strategyPair (s : PredicateStrategies QA QB A B) : Strategy QA QB A B :=
  (s.first, s.second)

/-- Interpret a concrete predicate and a normalized finite question law as a
game with the common foundation interface. -/
def weightedGame (G : PredicateGame QA QB A B)
    (questions : FiniteDistribution (QA × QB)) : Game QA QB A B := by
  classical
  exact ⟨questions, fun qa qb a b => decide (G.accepts qa qb a b)⟩


end Simulation

/-! ## The actual named projection predicate -/

namespace ActualProjection

open IncidenceExtraction

abbrev FirstAnswer (P : Type) := Bool × (P → Triple)
abbrev SecondAnswer (P : Type) := Bool × (P → Triple) × (P → Bool)

/-- Ambient coordinate form of the actual retained-coordinate projection. -/
def project {P : Type} (single : P → Bool) (indices : P → Fin 3)
    (answer : FirstAnswer P) : SecondAnswer P :=
  (answer.1, ZeroInformation.projectFull single answer.2,
    ZeroInformation.projectSingles single indices answer.2)

/-- A verifier using only the two displayed questions. The retained indices are
verifier witnesses compatible with the displayed names, never player inputs.
The output equality is the actual projection on all ambient coordinates. -/
def accepts {P R O N : Type} (g : Incidence O N) (single : P → Bool)
    (qa : ZeroInformation.FirstInput P R O)
    (qb : ZeroInformation.SecondInput P R O N)
    (answerA : FirstAnswer P) (answerB : SecondAnswer P) : Prop :=
  (∀ j, xorTriple (answerA.2 j) = (g.rhs (qa.question j) && answerA.1)) ∧
  answerA.1 = true ∧ ∃ indices : P → Fin 3,
    qb.question = ZeroInformation.partnerQuestion single qa.question
      (fun j => g.name (qa.question j) (indices j)) ∧
    answerB = project single indices answerA

def predicateGame {P R O N : Type} (g : Incidence O N) (single : P → Bool) :
    IncidenceExtraction.Game
      (ZeroInformation.FirstInput P R O) (ZeroInformation.SecondInput P R O N)
      (FirstAnswer P) (SecondAnswer P) :=
  ⟨accepts g single⟩


/-- At a single coordinate, actual projection acceptance supplies an accepted
named-incidence answer with no access to the retained index. -/
theorem accepts_implies_named_incidence
    {P R O N : Type} (g : Incidence O N) (single : P → Bool)
    (qa : ZeroInformation.FirstInput P R O)
    (qb : ZeroInformation.SecondInput P R O N)
    (answerA : FirstAnswer P) (answerB : SecondAnswer P)
    (h : accepts g single qa qb answerA answerB)
    (j : P) (hj : single j = true) (name : N)
    (hname : qb.question j = Sum.inr name) :
    g.namedAccepts (qa.question j) name (answerA.2 j) (answerB.2.2 j) := by
  obtain ⟨hvalid, hone, indices, hquestions, hproject⟩ := h
  refine ⟨indices j, ?_, ?_, ?_⟩
  · have hq := congrFun hquestions j
    simp [ZeroInformation.partnerQuestion, hj, hname] at hq
    exact hq.symm
  · simpa [hone] using hvalid j
  · subst answerB
    simp [project, ZeroInformation.projectSingles, hj]

end ActualProjection

end
end UniqueGamesTheorem.Soundness.RepeatedGameBounds

end

end OAI
