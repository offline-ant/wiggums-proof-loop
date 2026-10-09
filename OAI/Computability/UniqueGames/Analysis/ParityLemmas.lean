/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.LinearAlgebra.Prod
import Std

namespace OAI

section

namespace UniqueGamesTheorem.Fourier.Parity


end UniqueGamesTheorem.Fourier.Parity

end

section

/-! Actual splitting of linear-map questions and their uniform laws. -/

noncomputable section

open scoped BigOperators

namespace UniqueGamesTheorem.Fourier.SplitMaps

variable {K E C D : Type*} [CommSemiring K]
    [AddCommMonoid E] [Module K E]
    [AddCommMonoid C] [Module K C]
    [AddCommMonoid D] [Module K D]

/-- A question into the symbol/perpendicular product is exactly a pair of
independent coordinate questions. -/
def codomainSplit : (E →ₗ[K] C × D) ≃ₗ[K] (E →ₗ[K] C) × (E →ₗ[K] D) :=
  (LinearMap.prodEquiv K).symm


@[simp] theorem codomainSplit_symm_apply (X : E →ₗ[K] C) (Z : E →ₗ[K] D) :
    codomainSplit.symm (X, Z) = X.prod Z := rfl


theorem expect_codomain_product
    [Fintype (E →ₗ[K] C × D)] [Fintype (E →ₗ[K] C)] [Fintype (E →ₗ[K] D)]
    {A : Type*} [AddCommMonoid A] [Module ℚ≥0 A]
    (f : (E →ₗ[K] C × D) → A) :
    (𝔼 X, f X) = 𝔼 (X : E →ₗ[K] C), 𝔼 (Z : E →ₗ[K] D), f (X.prod Z) := by
  classical
  rw [Fintype.expect_equiv codomainSplit.toEquiv f
    (fun p => f (p.1.prod p.2)) (by intro X; rfl)]
  rw [← Finset.univ_product_univ, Finset.expect_product]


end UniqueGamesTheorem.Fourier.SplitMaps

end

end

end OAI
