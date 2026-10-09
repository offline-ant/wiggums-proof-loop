/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Foundations.ValueLemmas
import OAI.Computability.UniqueGames.Soundness.ConditionalLocality
import OAI.Computability.UniqueGames.Soundness.ConditionalReindex
import OAI.Computability.UniqueGames.Soundness.RawTargetLawLemmas

namespace OAI

section

/-!
The actual local simulation in Lemma 6.8 after fixing H. These reconstruction
maps consume only the first player's occurrence tuple or the second player's
name tuple. Its winning-event containment is proved from the concrete equation
and named-projection predicates.
-/

namespace UniqueGamesTheorem.Soundness.ConditionalSimulation

open Foundations.Games ConditionalIncidences IncidenceExtraction
open RepeatedGameBounds

noncomputable section

instance firstInputFintype {P R O : Type} [Fintype P] [Fintype R] [Fintype O] :
    Fintype (ZeroInformation.FirstInput P R O) := by
  classical
  exact Fintype.ofEquiv ((P → O) × ZeroInformation.FirstRow P R)
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun q => (q.question, q.row)
      left_inv := fun p => by cases p; rfl
      right_inv := fun q => by cases q; rfl }

instance secondInputFintype {P R O N : Type}
    [Fintype P] [Fintype R] [Fintype O] [Fintype N] :
    Fintype (ZeroInformation.SecondInput P R O N) := by
  classical
  exact Fintype.ofEquiv ((P → Sum O N) × ZeroInformation.SecondRow P R)
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun q => (q.question, q.row)
      left_inv := fun p => by cases p; rfl
      right_inv := fun q => by cases q; rfl }

def incidenceGame {O N : Type} [Fintype O] [Fintype N]
    (g : Incidence O N) (mu : FiniteDistribution (O × N)) :
    Foundations.Games.Game O N Triple Bool :=
  Simulation.weightedGame ⟨g.namedAccepts⟩ mu

def actualLocalSimulation
    {P R O N : Type} [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
    [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (mu : FiniteDistribution (O × N))
    (enumerate : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma)) :
    IncidenceExtraction.LocalSimulation
      (Simulation.predicateGame ((incidenceGame g mu).repetition (zeroSet J gamma).card))
      (ActualProjection.predicateGame (R := R) g (membershipBool J)) where
  questionA qa := localFirstFromH J g.name gamma observed reference
    (fun j => qa (enumerate.symm j))
  questionB qb := localSecondFromH J g.name gamma observed reference
    (fun j => qb (enumerate.symm j))
  answerA _ answer i := answer.2 (enumerate i).val
  answerB _ answer i := answer.2.2 (enumerate i).val
  sound := by
    classical
    intro qa qb answerA answerB haccept
    change ((incidenceGame g mu).repetition (zeroSet J gamma).card).accepts _ _ _ _ = true
    rw [Foundations.Games.Game.repetition_accepts_iff]
    intro i
    change decide (g.namedAccepts (qa i) (qb i)
      (answerA.2 (enumerate i).val) (answerB.2.2 (enumerate i).val)) = true
    rw [decide_eq_true_eq]
    have hj : (enumerate i).val ∈ J := zeroSet_subset J gamma (enumerate i).property
    have hsingle : membershipBool J (enumerate i).val = true := by
      simp [membershipBool, hj]
    have hname : (localSecondFromH J g.name gamma observed reference
        (fun j => qb (enumerate.symm j))).question (enumerate i).val = Sum.inr (qb i) := by
      simpa using localSecondFromH_question_inside J g.name gamma observed reference
        (fun j => qb (enumerate.symm j)) (enumerate i)
    have h := ActualProjection.accepts_implies_named_incidence g (membershipBool J)
      _ _ answerA answerB haccept (enumerate i).val hsingle (qb i) hname
    simpa only [localFirstFromH_question_inside, Equiv.symm_apply_apply] using h


end
end UniqueGamesTheorem.Soundness.ConditionalSimulation

end

section

/-! The genuine conditional experiment is the reconstructed repeated-game law. -/

namespace UniqueGamesTheorem.Soundness.ConditionalGameLaw
open scoped BigOperators
open Foundations.Games
open ConditionalIncidences ConditionalSimulation IncidenceExtraction RepeatedGameBounds

noncomputable section
attribute [local instance] Classical.propDecidable


variable {P R O N : Type}
  [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

abbrev OuterStrategy := IncidenceExtraction.Strategies
  (ZeroInformation.FirstInput P R O) (ZeroInformation.SecondInput P R O N)
  (ActualProjection.FirstAnswer P) (ActualProjection.SecondAnswer P)

def actualWin (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N)) (draw : Draw P O) : Prop :=
  strategy.wins (ActualProjection.predicateGame (R := R) g (membershipBool J))
    (actualFirst J gamma draw) (actualSecond J g.name gamma draw)


def reconstructedEvent (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (questions : Fin (zeroSet J gamma).card → O × N) : Prop :=
  strategy.wins (ActualProjection.predicateGame (R := R) g (membershipBool J))
    (localFirstFromH J g.name gamma observed reference (fun j => (questions (e.symm j)).1))
    (localSecondFromH J g.name gamma observed reference (fun j => (questions (e.symm j)).2))

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] in
theorem actualWin_iff_reconstructedEvent (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (sample : RawObservationFibre J g.name gamma observed) :
    actualWin J g gamma strategy sample.val.2 ↔
      reconstructedEvent J g gamma observed reference e strategy
        (fun i => incidence g.name (sample.val.2 (e i).val)) := by
  unfold actualWin reconstructedEvent
  simp only [incidence, Equiv.apply_symm_apply]
  rw [localFirstFromH_correct J g.name gamma observed distinct reference sample,
    localSecondFromH_correct J g.name gamma observed reference sample]


end
end UniqueGamesTheorem.Soundness.ConditionalGameLaw

end

end OAI
