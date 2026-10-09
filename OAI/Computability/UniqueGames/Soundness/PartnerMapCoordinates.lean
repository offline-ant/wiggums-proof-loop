/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Tactic.FinCases
import OAI.Computability.UniqueGames.Soundness.PartnerLinearLemmas
import OAI.Computability.UniqueGames.Soundness.ZeroInformationLemmas

namespace OAI

section

/-!
# Every partner linear map has independent raw coefficient coordinates

The coefficient index is exactly `ConditionalIncidences.RawSlot`: one global
coefficient, two coefficients at every full position, and one at every single
position.  The coordinate bijection below is for every actual partner linear
map, and its finite-uniform-law theorem has no distributional hypothesis.
-/

open scoped BigOperators

namespace UniqueGamesTheorem.Soundness.PartnerMapCoordinates

open PartnerProjection
open ConditionalIncidences (PositionInside PositionOutside RawSlot RawCoefficients average)
open UniqueGamesTheorem.Integration.BinaryLinear (F2 ofBit toBit)

noncomputable section

variable {P : Type} [DecidableEq P] (rhs : P → Bool) (J : Finset P)

def activeOf (J : Finset P) (j : P) : Bool := decide (j ∈ J)

def inactiveOfOutside (j : PositionOutside J) : PartnerLinear.Inactive (activeOf J) :=
  ⟨j.val, by simp [activeOf, j.property]⟩

def activeOfInside (j : PositionInside J) : PartnerLinear.Active (activeOf J) :=
  ⟨j.val, by simp [activeOf, j.property]⟩

def outsideOfInactive (j : PartnerLinear.Inactive (activeOf J)) : PositionOutside J :=
  ⟨j.val, by simpa [activeOf] using j.property⟩

def insideOfActive (j : PartnerLinear.Active (activeOf J)) : PositionInside J :=
  ⟨j.val, by simpa [activeOf] using j.property⟩

def tupleToRaw (v : PartnerLinear.PartnerCoordinates (activeOf J)) : RawSlot J → F2
  | none => v.1
  | some (.inl (j, i)) =>
      if i = 0 then (v.2.1 (inactiveOfOutside J j)).1
      else (v.2.1 (inactiveOfOutside J j)).2
  | some (.inr j) => v.2.2 (activeOfInside J j)

def tupleFromRaw (f : RawSlot J → F2) : PartnerLinear.PartnerCoordinates (activeOf J) :=
  (f none,
    (fun j => (f (some (.inl (outsideOfInactive J j, 0))),
      f (some (.inl (outsideOfInactive J j, 1)))),
      fun j => f (some (.inr (insideOfActive J j)))))

def tupleRawEquiv : PartnerLinear.PartnerCoordinates (activeOf J) ≃ₗ[F2] (RawSlot J → F2) where
  toFun := tupleToRaw J
  invFun := tupleFromRaw J
  left_inv v := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext j
        apply Prod.ext <;> rfl
      · funext j
        rfl
  right_inv f := by
    funext s
    rcases s with _ | (⟨j, i⟩ | j)
    · rfl
    · fin_cases i <;> rfl
    · rfl
  map_add' x y := by
    funext s
    rcases s with _ | (⟨j, i⟩ | j)
    · rfl
    · fin_cases i <;> rfl
    · rfl
  map_smul' c x := by
    funext s
    rcases s with _ | (⟨j, i⟩ | j)
    · rfl
    · fin_cases i <;> rfl
    · rfl

/-- Free coordinates of the actual partner, indexed by the exact raw coefficient slots. -/
def pointEquiv : PartnerPoint rhs (activeOf J) ≃ₗ[F2] (RawSlot J → F2) :=
  (PartnerLinear.partnerLinearEquiv rhs (activeOf J)).trans (tupleRawEquiv J)

@[simp] theorem pointEquiv_none (y : PartnerPoint rhs (activeOf J)) :
    pointEquiv rhs J y none = ofBit y.homogeneous := rfl

@[simp] theorem pointEquiv_full_first (y : PartnerPoint rhs (activeOf J))
    (j : PositionOutside J) :
    pointEquiv rhs J y (some (.inl (j, 0))) = ofBit (y.full j.val).first := rfl

@[simp] theorem pointEquiv_full_second (y : PartnerPoint rhs (activeOf J))
    (j : PositionOutside J) :
    pointEquiv rhs J y (some (.inl (j, 1))) = ofBit (y.full j.val).second := rfl

@[simp] theorem pointEquiv_single (y : PartnerPoint rhs (activeOf J))
    (j : PositionInside J) :
    pointEquiv rhs J y (some (.inr j)) = ofBit (y.single j.val) := rfl

variable [Fintype P]

def partnerBasis : Module.Basis (RawSlot J) F2 (PartnerPoint rhs (activeOf J)) :=
  Module.Basis.ofEquivFun (pointEquiv rhs J)

variable (R : Type) [AddCommGroup R] [Module F2 R]

/-- Arbitrary independent raw coefficients bijectively specify an actual linear map. -/
def mapEquiv : RawCoefficients J R ≃ₗ[F2] (PartnerPoint rhs (activeOf J) →ₗ[F2] R) :=
  (partnerBasis rhs J).constr F2


theorem mapEquiv_apply (gamma : RawCoefficients J R) (y : PartnerPoint rhs (activeOf J)) :
    mapEquiv rhs J R gamma y = ∑ s, pointEquiv rhs J y s • gamma s := by
  rw [mapEquiv, Module.Basis.constr_apply_fintype]
  simp only [partnerBasis, Module.Basis.equivFun_ofEquivFun]

/-- The raw-coefficient formula for every partner point. -/
theorem mapEquiv_expansion (gamma : RawCoefficients J R) (y : PartnerPoint rhs (activeOf J)) :
    mapEquiv rhs J R gamma y =
      ofBit y.homogeneous • gamma none +
        (∑ j : PositionOutside J,
          (ofBit (y.full j.val).first • gamma (some (.inl (j, 0))) +
            ofBit (y.full j.val).second • gamma (some (.inl (j, 1))))) +
        ∑ j : PositionInside J, ofBit (y.single j.val) • gamma (some (.inr j)) := by
  rw [mapEquiv_apply, Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, pointEquiv_none, pointEquiv_full_first,
    pointEquiv_full_second, pointEquiv_single]
  simp only [add_assoc]


theorem pullback_expansion (gamma : RawCoefficients J R) (slot : P → Slot)
    (x : SourcePoint rhs) :
    mapEquiv rhs J R gamma (PartnerLinear.projection rhs (activeOf J) slot x) =
      ofBit x.homogeneous • gamma none +
        (∑ j : PositionOutside J,
          (ofBit (x.coordinates j.val).first • gamma (some (.inl (j, 0))) +
            ofBit (x.coordinates j.val).second • gamma (some (.inl (j, 1))))) +
        ∑ j : PositionInside J,
          ofBit (retained (slot j.val) (x.coordinates j.val)) • gamma (some (.inr j)) := by
  rw [mapEquiv_expansion]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp [PartnerLinear.projection_apply, project, activeOf, j.property]
  · apply Finset.sum_congr rfl
    intro j _
    simp [PartnerLinear.projection_apply, project, activeOf, j.property]

instance partnerMapsFintype [Fintype R] :
    Fintype (PartnerPoint rhs (activeOf J) →ₗ[F2] R) := by
  classical
  exact Fintype.ofEquiv (RawCoefficients J R) (mapEquiv rhs J R).toEquiv


end

end UniqueGamesTheorem.Soundness.PartnerMapCoordinates

end

end OAI
