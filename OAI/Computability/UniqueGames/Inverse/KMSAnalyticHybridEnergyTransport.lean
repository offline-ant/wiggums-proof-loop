/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Analysis.HybridCompositionLemmas
import OAI.Computability.UniqueGames.Inverse.KMSAffineRestrictionPresentationLemmas

namespace OAI

section

/-!
# Exact coordinate transport of hybrid derivative energy

Both ambient spaces, both selector subspaces, and the affine translate are
transported together. The actual Fourier selector and the actual affine
restriction then have the same normalized squared norm.
-/

noncomputable section

namespace UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Appendix
open UniqueGamesTheorem.Inverse.KMSAnalytic

variable {E F E' F' : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup E'] [Module F2 E'] [AddCommGroup F'] [Module F2 F']

/-- The two clauses of the actual Hybrid selector are coordinate invariant. -/
theorem hybrid_arrowCongr (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (S : F →ₗ[F2] E) (A : Submodule F2 E) (B : Submodule F2 F) :
    LinearIdentities.Hybrid (LinearEquiv.arrowCongr b a S)
      (A.map a.toLinearMap) (B.map b.toLinearMap) ↔
      LinearIdentities.Hybrid S A B := by
  change (A.map a.toLinearMap ≤
      ((a.toLinearMap.comp S).comp b.symm.toLinearMap).range ∧
      (A.map a.toLinearMap).comap
        (a.toLinearMap.comp (S.comp b.symm.toLinearMap)) ≤ B.map b.toLinearMap) ↔ _
  rw [LinearEquiv.range_comp]
  simp only [LinearMap.range_comp, Submodule.comap_comp,
    Submodule.comap_map_eq_of_injective a.injective,
    Submodule.comap_equiv_eq_map_symm, LinearEquiv.symm_symm,
    Submodule.map_le_map_iff_of_injective a.injective,
    Submodule.map_le_map_iff_of_injective b.injective, LinearIdentities.Hybrid]

/-- The actual vanishing and range constraints of an affine perturbation
transport to the mapped subspaces. -/
theorem restriction_admissible_arrowCongr
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (M : E →ₗ[F2] F) (A : Submodule F2 E) (B : Submodule F2 F) :
    (A.map a.toLinearMap ≤ (LinearEquiv.arrowCongr a b M).ker ∧
      (LinearEquiv.arrowCongr a b M).range ≤ B.map b.toLinearMap) ↔
      (A ≤ M.ker ∧ M.range ≤ B) := by
  change (A.map a.toLinearMap ≤
      (b.toLinearMap.comp (M.comp a.symm.toLinearMap)).ker ∧
      ((b.toLinearMap.comp M).comp a.symm.toLinearMap).range ≤ B.map b.toLinearMap) ↔ _
  rw [LinearEquiv.ker_comp, LinearEquiv.range_comp]
  simp only [LinearMap.ker_comp, LinearMap.range_comp,
    Submodule.comap_equiv_eq_map_symm, LinearEquiv.symm_symm,
    Submodule.map_le_map_iff_of_injective a.injective,
    Submodule.map_le_map_iff_of_injective b.injective]

/-- Transported quotient parameters give exactly the directly transported
affine perturbations; no multiplicity or normalization factor occurs. -/
theorem hybrid_embedding_range (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (A : Submodule F2 E) (B : Submodule F2 F) :
    ((LinearEquiv.arrowCongr a b).toLinearMap.comp (embedding A B)).range =
      (embedding (A.map a.toLinearMap) (B.map b.toLinearMap)).range := by
  rw [LinearMap.range_comp]
  apply Submodule.comap_injective_of_surjective (LinearEquiv.arrowCongr a b).surjective
  rw [Submodule.comap_map_eq_of_injective (LinearEquiv.arrowCongr a b).injective]
  ext M
  change (∃ N, embed A B N = M) ↔
    (∃ N, embed (A.map a.toLinearMap) (B.map b.toLinearMap) N =
      LinearEquiv.arrowCongr a b M)
  rw [exists_embed_iff, exists_embed_iff, restriction_admissible_arrowCongr]

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [FiniteDimensional F2 E'] [FiniteDimensional F2 F']
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Fintype (E' →ₗ[F2] F')] [Fintype (F' →ₗ[F2] E')]

/-- The actual Fourier Hybrid projector commutes with coordinate pullback. -/
theorem hybridProjector_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (A : Submodule F2 E) (B : Submodule F2 F) :
    hybridProjector A B (fun M => f (LinearEquiv.arrowCongr a b M)) =
      fun M => hybridProjector (A.map a.toLinearMap) (B.map b.toLinearMap) f
        (LinearEquiv.arrowCongr a b M) := by
  apply function_eq_of_linearCoeff_eq
  intro Y
  simp only [hybridProjector, linearCoeff_spectralProjector,
    NaturalTransport.linearCoeff_pullback, hybrid_arrowCongr]

/-- The actual pure-rank Fourier component commutes with coordinate pullback. -/
theorem rankComponent_pullback (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (i : ℕ) :
    rankComponent i (fun M => f (LinearEquiv.arrowCongr a b M)) =
      fun M => rankComponent i f (LinearEquiv.arrowCongr a b M) := by
  apply function_eq_of_linearCoeff_eq
  intro Y
  simp only [rankComponent, coeff_component,
    NaturalTransport.linearCoeff_pullback, NaturalTransport.rank_arrowCongr]

variable [Finite E] [Finite F] [Finite E'] [Finite F']

/-- Exact normalized energy transport, with the actual Hybrid selector,
quotient restriction, and affine translate transported together. -/
theorem hybridDerivative_energy_pullback
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (A : Submodule F2 E) (B : Submodule F2 F)
    (T : E →ₗ[F2] F) :
    (𝔼 N, hybridDerivative A B T
      (fun M => f (LinearEquiv.arrowCongr a b M)) N ^ 2) =
      𝔼 N, hybridDerivative (A.map a.toLinearMap) (B.map b.toLinearMap)
        (LinearEquiv.arrowCongr a b T) f N ^ 2 := by
  simp only [hybridDerivative, restrict, Fourier.MatrixRestrictions.translate,
    hybridProjector_pullback, map_add]
  exact RestrictionTransport.expect_eq_of_same_range
    ((LinearEquiv.arrowCongr a b).toLinearMap.comp (embedding A B))
    (embedding (A.map a.toLinearMap) (B.map b.toLinearMap))
    ((LinearEquiv.arrowCongr a b).injective.comp (embed_injective A B))
    (embed_injective _ _) (hybrid_embedding_range a b A B)
    (fun M => hybridProjector (A.map a.toLinearMap) (B.map b.toLinearMap) f
      (LinearEquiv.arrowCongr a b T + M) ^ 2)

/-- Pure-rank derivative energy is invariant under both coordinate changes. -/
theorem hybridDerivative_rankComponent_energy_pullback
    (a : E ≃ₗ[F2] E') (b : F ≃ₗ[F2] F')
    (f : (E' →ₗ[F2] F') → ℝ) (i : ℕ)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F) :
    (𝔼 N, hybridDerivative A B T
      (rankComponent i (fun M => f (LinearEquiv.arrowCongr a b M))) N ^ 2) =
      𝔼 N, hybridDerivative (A.map a.toLinearMap) (B.map b.toLinearMap)
        (LinearEquiv.arrowCongr a b T) (rankComponent i f) N ^ 2 := by
  rw [rankComponent_pullback]
  exact hybridDerivative_energy_pullback a b (rankComponent i f) A B T

end UniqueGamesTheorem.Inverse.KMSAnalyticHybridEnergy

end

end

end OAI
