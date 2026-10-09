/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Soundness.RawPrivateTable
import OAI.Computability.UniqueGames.Soundness.RawTargetLawLemmas

namespace OAI

section

/-! Conversion of actual binary linear points to the named projection answers. -/

namespace UniqueGamesTheorem.Soundness.ActualPointAnswers
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open PartnerProjection PartnerMapCoordinates RawPartnerTarget
open RepeatedGameBounds

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat}

def sourceTau : ActualHomogeneous.E k →ₗ[F2] F2 := LinearMap.fst F2 F2 _


def firstAnswer (rhs : Fin k → Bool) (x : ActualHomogeneous.E k) :
    ActualProjection.FirstAnswer (Fin k) :=
  let p := (PartnerLinear.sourceLinearEquiv rhs).symm x
  (p.homogeneous, fun j => ConcreteExtraction.tripleCoordinates (p.coordinates j))

def secondAnswer (rhs : Fin k → Bool) (J : Finset (Fin k)) (v : RawPoint J) :
    ActualProjection.SecondAnswer (Fin k) :=
  let y := (pointEquiv rhs J).symm v
  (y.homogeneous, (fun j => ConcreteExtraction.tripleCoordinates (y.full j)), y.single)

/-- Inactive occurrences determine every full triple. The active right-hand
sides never enter the partner answer. -/
theorem secondAnswer_projection (rhs rhs' : Fin k → Bool) (J : Finset (Fin k))
    (slot : Fin k → Slot) (x : ActualHomogeneous.E k)
    (hout : ∀ j, j ∉ J → rhs' j = rhs j) :
    secondAnswer rhs' J (rawProjection rhs J slot x) =
      ActualProjection.project (activeOf J) (fun j => ConcreteExtraction.slotIndex (slot j))
        (firstAnswer rhs x) := by
  let p := (PartnerLinear.sourceLinearEquiv rhs).symm x
  let y := PartnerLinear.partnerFromCoordinates rhs' (activeOf J)
    (PartnerLinear.partnerCoordinates rhs (activeOf J) (project rhs (activeOf J) slot p))
  change (y.homogeneous, (fun j => ConcreteExtraction.tripleCoordinates (y.full j)), y.single) = _
  apply Prod.ext
  · exact toBit_ofBit _
  · apply Prod.ext
    · funext j i
      have hc := complete_coordinates .first (p.coordinates j)
      simp only [retained, freeBit] at hc
      by_cases hj : j ∈ J <;>
        simp [y, PartnerLinear.partnerFromCoordinates, PartnerLinear.partnerCoordinates,
          project, ActualProjection.project, ZeroInformation.projectFull, activeOf, hj,
          toBit_ofBit, hout, ← p.valid j, hc,
          ConcreteExtraction.tripleCoordinates, zeroTriple, firstAnswer, p]
    · funext j
      by_cases hj : j ∈ J <;>
        simp [y, PartnerLinear.partnerFromCoordinates, PartnerLinear.partnerCoordinates,
          project, ActualProjection.project, ZeroInformation.projectSingles, activeOf, hj,
          toBit_ofBit, ConcreteExtraction.retained_coordinates, firstAnswer, p]

def displayedRhs {Id Name : Type} (rhs : Id → Bool) (question : Fin k → Sum Id Name) :
    Fin k → Bool := fun j => match question j with
  | .inl o => rhs o
  | .inr _ => false

theorem displayedRhs_full {Id Name : Type} (rhs : Id → Bool)
    (J : Finset (Fin k)) (names : Id → Fin 3 → Name)
    (occ : Fin k → Id) (slot : Fin k → Slot) (j : Fin k) (hj : j ∉ J) :
    displayedRhs rhs (RawPrivateTable.displayed J names occ slot) j = rhs (occ j) := by
  simp [displayedRhs, RawPrivateTable.displayed, hj]

/-- Actual point equality gives acceptance in the named verifier on complete
private inputs, with local answer conversions. -/
theorem actual_accepts {Q Id Name : Type} (J : Finset (Fin k))
    (g : IncidenceExtraction.Incidence Id Name)
    (qa : ZeroInformation.FirstInput (Fin k) Q Id)
    (qb : ZeroInformation.SecondInput (Fin k) Q Id Name)
    (slot : Fin k → Slot)
    (hquestion : qb.question = RawPrivateTable.displayed J g.name qa.question slot)
    (x : ActualHomogeneous.E k) (v : RawPoint J)
    (hone : sourceTau x = 1)
    (hprojection : rawProjection (fun j => g.rhs (qa.question j)) J slot x = v) :
    ActualProjection.accepts g (activeOf J) qa qb
      (firstAnswer (fun j => g.rhs (qa.question j)) x)
      (secondAnswer (displayedRhs g.rhs qb.question) J v) := by
  let p := (PartnerLinear.sourceLinearEquiv (fun j => g.rhs (qa.question j))).symm x
  have hp : p.homogeneous = true := by
    change toBit x.1 = true
    change x.1 = 1 at hone
    rw [hone]
    decide
  refine ⟨?_, hp, (fun j => ConcreteExtraction.slotIndex (slot j)), ?_, ?_⟩
  · intro j
    exact (ConcreteExtraction.parity_coordinates _).trans (p.valid j)
  · rw [hquestion]
    funext j
    by_cases hj : j ∈ J <;>
      simp [RawPrivateTable.displayed, ZeroInformation.partnerQuestion, activeOf, hj]
  · rw [← hprojection]
    exact secondAnswer_projection _ _ J slot x (fun j hj => by
      rw [hquestion]
      exact displayedRhs_full g.rhs J g.name qa.question slot j hj)

end
end UniqueGamesTheorem.Soundness.ActualPointAnswers

end

end OAI
