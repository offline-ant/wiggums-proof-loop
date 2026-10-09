/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Soundness.ActualCanonicalPullbackLemmas

namespace OAI

section

/-! The private Fourier table is defined from displayed data alone. Compatibility
with every hidden extension follows from the proved canonical locality theorem. -/

namespace UniqueGamesTheorem.Soundness.RawPrivateTable
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction
open PartnerProjection RawPartnerTarget

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat} {Id Name : Type}

abbrev Extension (k : Nat) (Id : Type) := (Fin k → Id) × (Fin k → Slot)

def displayed (J : Finset (Fin k)) (names : Id → Fin 3 → Name)
    (occ : Fin k → Id) (slot : Fin k → Slot) : Fin k → Sum Id Name :=
  fun j => if j ∈ J then
    Sum.inr (names (occ j) (ConcreteExtraction.slotIndex (slot j)))
  else Sum.inl (occ j)

theorem full_occurrence_eq_of_displayed_eq
    {J : Finset (Fin k)} {names : Id → Fin 3 → Name}
    {occ occ' : Fin k → Id} {slot slot' : Fin k → Slot}
    (h : displayed J names occ slot = displayed J names occ' slot')
    (j : Fin k) (hj : j ∉ J) : occ j = occ' j := by
  simpa [displayed, hj] using congrFun h j

theorem single_name_eq_of_displayed_eq
    {J : Finset (Fin k)} {names : Id → Fin 3 → Name}
    {occ occ' : Fin k → Id} {slot slot' : Fin k → Slot}
    (h : displayed J names occ slot = displayed J names occ' slot')
    (j : Fin k) (hj : j ∈ J) :
    names (occ j) (ConcreteExtraction.slotIndex (slot j)) =
      names (occ' j) (ConcreteExtraction.slotIndex (slot' j)) := by
  simpa [displayed, hj] using congrFun h j


def SupportedV (J : Finset (Fin k)) (names : Id → Fin 3 → Name) : Type :=
  { V : Fin k → Sum Id Name //
      V ∈ Set.range (fun e : Extension k Id => displayed J names e.1 e.2) }

def representative {J : Finset (Fin k)} {names : Id → Fin 3 → Name}
    (V : SupportedV J names) : Extension k Id := Classical.choose V.property

theorem representative_display {J : Finset (Fin k)} {names : Id → Fin 3 → Name}
    (V : SupportedV J names) :
    displayed J names (representative V).1 (representative V).2 = V.val :=
  Classical.choose_spec V.property

def supported (J : Finset (Fin k)) (names : Id → Fin 3 → Name)
    (occ : Fin k → Id) (slot : Fin k → Slot) : SupportedV J names :=
  ⟨displayed J names occ slot, ⟨(occ, slot), rfl⟩⟩

variable (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (rhs : Id → F2)
  {R D C Label : Type} [AddCommGroup R] [Module F2 R] [DecidableEq R]
  [AddCommGroup D] [Module F2 D] [AddCommGroup C] [Module F2 C]
  [DecidableEq Id] [DecidableEq Name]

def projection (occ : Fin k → Id) (slot : Fin k → Slot) :
    ActualHomogeneous.E k →ₗ[F2] RawPoint J :=
  rawProjection (fun j => toBit (rhs (occ j))) J slot


theorem canonical_same_display (occ occ' : Fin k → Id) (slot slot' : Fin k → Slot)
    (Y : RawPoint J →ₗ[F2] R)
    (h : displayed J names occ slot = displayed J names occ' slot') :
    ActualCanonical.canonical occ names rhs (Y.comp (projection J rhs occ slot)) =
      ActualCanonical.canonical occ' names rhs (Y.comp (projection J rhs occ' slot')) := by
  unfold projection
  rw [rawMap_pullback, rawMap_pullback]
  exact ActualCanonicalPullback.canonical_private_input_locality J R names rhs
    occ occ' slot slot' (gammaOfRawMap J Y)
    (full_occurrence_eq_of_displayed_eq h) (single_name_eq_of_displayed_eq h)


end
end UniqueGamesTheorem.Soundness.RawPrivateTable

end

end OAI
