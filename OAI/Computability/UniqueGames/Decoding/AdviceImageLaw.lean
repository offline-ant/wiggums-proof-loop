/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Algebra.BigOperators.Expect
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas
import OAI.Computability.UniqueGames.Soundness.PartnerMapCoordinates

namespace OAI

section

/-!
# The exact visible-advice law for a fixed latent map

For every fixed binary-linear map `A`, including rank-deficient maps, a uniform
latent column has a uniform image in `range A`.  An explicit range/kernel
bijection proves the assertion simultaneously for every intercept and slope.
The final theorem starts with the actual pair of independently uniform linear
maps on the partner answer space and pushes it to independent uniform visible
coefficients in `W × range A`.  No full-rank or independence premise is assumed.
-/

namespace UniqueGamesTheorem.Clean.AdviceImageLaw

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Soundness.ConditionalIncidences
open UniqueGamesTheorem.Soundness.PartnerMapCoordinates
open UniqueGamesTheorem.Foundations.Games

noncomputable section

attribute [local instance] Classical.propDecidable

variable {K S W : Type} [AddCommGroup K] [Module F2 K]
  [AddCommGroup S] [Module F2 S]

def rangePoint (A : K →ₗ[F2] S) (m : K) : A.range :=
  ⟨A m, ⟨m, rfl⟩⟩

def selectedLift (A : K →ₗ[F2] S) (z : A.range) : K :=
  Classical.choose z.property

theorem selectedLift_spec (A : K →ₗ[F2] S) (z : A.range) :
    A (selectedLift A z) = (z : S) :=
  Classical.choose_spec z.property

theorem rangePoint_lift_add_kernel (A : K →ₗ[F2] S) (z : A.range) (k : A.ker) :
    rangePoint A (selectedLift A z + (k : K)) = z := by
  apply Subtype.ext
  change A (selectedLift A z + (k : K)) = (z : S)
  rw [map_add, selectedLift_spec, k.property, add_zero]

/-- Every range fibre is one translate of the same kernel. -/
def imageKernelEquiv (A : K →ₗ[F2] S) : K ≃ A.range × A.ker where
  toFun m := (rangePoint A m,
    ⟨m - selectedLift A (rangePoint A m), by
      change A (m - selectedLift A (rangePoint A m)) = 0
      rw [map_sub, selectedLift_spec]
      exact sub_self _⟩)
  invFun p := selectedLift A p.1 + (p.2 : K)
  left_inv m := by
    change selectedLift A (rangePoint A m) + (m - selectedLift A (rangePoint A m)) = m
    rw [add_comm, sub_add_cancel]
  right_inv p := by
    apply Prod.ext
    · exact rangePoint_lift_add_kernel A p.1 p.2
    · apply Subtype.ext
      change selectedLift A p.1 + (p.2 : K) -
        selectedLift A (rangePoint A (selectedLift A p.1 + (p.2 : K))) = (p.2 : K)
      rw [rangePoint_lift_add_kernel]
      exact add_sub_cancel_left _ _

def columnImage (A : K →ₗ[F2] S) (column : W × K) : W × A.range :=
  (column.1, rangePoint A column.2)

def columnSplitEquiv (A : K →ₗ[F2] S) : (W × K) ≃ (W × A.range) × A.ker :=
  (Equiv.prodCongr (Equiv.refl W) (imageKernelEquiv A)).trans
    (Equiv.prodAssoc W A.range A.ker).symm

def visibleCoefficients {I : Type} (A : K →ₗ[F2] S)
    (columns : I → W × K) : I → W × A.range :=
  fun i => columnImage A (columns i)

def coefficientsSplitEquiv (I : Type) (A : K →ₗ[F2] S) :
    (I → W × K) ≃ (I → W × A.range) × (I → A.ker) :=
  (Equiv.piCongrRight fun _ : I => columnSplitEquiv (W := W) A).trans
    (Equiv.arrowProdEquivProdArrow I (fun _ => W × A.range) (fun _ => A.ker))

instance rangeFintype [Fintype S] (A : K →ₗ[F2] S) : Fintype A.range :=
  Fintype.ofFinite _

instance kernelFintype [Fintype K] (A : K →ₗ[F2] S) : Fintype A.ker :=
  Fintype.ofFinite _

/-- Exact pushforward law for all columns jointly, including the original
intercept. This implies every event identity, not just individual marginals. -/
theorem uniform_visible_coefficients {I : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [Fintype K] [Fintype S]
    (A : K →ₗ[F2] S) (F : (I → W × A.range) → ℝ) :
    (𝔼 columns : I → W × K, F (visibleCoefficients A columns)) =
      𝔼 visible : I → W × A.range, F visible := by
  calc
    (𝔼 columns : I → W × K, F (visibleCoefficients A columns)) =
        𝔼 pieces : (I → W × A.range) × (I → A.ker), F pieces.1 :=
      Fintype.expect_equiv (coefficientsSplitEquiv I A) _ _ (fun _ => rfl)
    _ = _ := by
      simpa only [Finset.univ_product_univ, Fintype.expect_const] using
        (Finset.expect_product (Finset.univ : Finset (I → W × A.range))
          (Finset.univ : Finset (I → A.ker)) (fun pieces => F pieces.1))


/-- The worst-case codomain cardinality suffices; no rank estimate is needed. -/
theorem visible_card_le [Fintype W] [Fintype K] [Fintype S] (A : K →ₗ[F2] S) :
    Fintype.card (W × A.range) ≤ Fintype.card W * Fintype.card S := by
  rw [Fintype.card_prod]
  exact Nat.mul_le_mul_left _
    (Fintype.card_le_of_injective (fun z : A.range => (z : S)) Subtype.val_injective)

theorem visible_card_binary_le [Fintype K] (w r : Nat)
    (A : K →ₗ[F2] (Fin r → F2)) :
    Fintype.card ((Fin w → F2) × A.range) ≤ 2 ^ (w + r) := by
  calc
    Fintype.card ((Fin w → F2) × A.range) ≤
        Fintype.card (Fin w → F2) * Fintype.card (Fin r → F2) :=
      visible_card_le A
    _ = 2 ^ (w + r) := by simp [F2, pow_add]

section ActualMaps

variable {P : Type} [Fintype P] [DecidableEq P]
  [AddCommGroup W] [Module F2 W]
  (rhs : P → Bool) (J : Finset P)


end ActualMaps

end

end UniqueGamesTheorem.Clean.AdviceImageLaw

end

end OAI
