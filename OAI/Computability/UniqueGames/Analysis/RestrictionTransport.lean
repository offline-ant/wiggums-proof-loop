/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Analysis.Identities
import OAI.Computability.UniqueGames.Analysis.MatrixRestrictions
import OAI.Computability.UniqueGames.Analysis.RestrictionLemmas

namespace OAI

namespace UniqueGamesTheorem

/-!
# Exact transport of nested affine restrictions

The nested quotient-domain/range inclusion has exactly the effective
annihilator and target obtained by comap and map. Its parameterization is
linearly equivalent to the direct effective restriction, independently of
any Fourier frequency. Thus normalized second moments and the outer average
of their squares agree while retaining the full affine translate.
-/

noncomputable section

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixRestrictions

section Nested

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

namespace Appendix.RestrictionTransport

/-- Compose the two actual quotient-domain and target-subspace embeddings. -/
def nestedEmbedding (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    Parameter C D →ₗ[F2] (E →ₗ[F2] F) :=
  (embedding A B).comp (embedding C D)

theorem nestedEmbedding_injective (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    Function.Injective (nestedEmbedding A B C D) := by
  intro N N' h
  apply embed_injective C D
  apply embed_injective A B
  exact h

end Appendix.RestrictionTransport

namespace Appendix.NaturalTransport

def quotientFactor (A : Submodule F2 E) (C : Submodule F2 (E ⧸ A)) :
    (E ⧸ C.comap A.mkQ) ≃ₗ[F2] ((E ⧸ A) ⧸ C) :=
  (Submodule.quotEquivOfEq (C.comap A.mkQ) (C.mkQ.comp A.mkQ).ker
    (by rw [LinearMap.ker_comp, Submodule.ker_mkQ])).trans
      ((C.mkQ.comp A.mkQ).quotKerEquivOfSurjective
        (C.mkQ_surjective.comp A.mkQ_surjective))

@[simp] theorem quotientFactor_mkQ (A : Submodule F2 E)
    (C : Submodule F2 (E ⧸ A)) (x : E) :
    quotientFactor A C ((C.comap A.mkQ).mkQ x) = C.mkQ (A.mkQ x) := by
  simp [quotientFactor]

def outputFactor (B : Submodule F2 F) (D : Submodule F2 B) :
    D ≃ₗ[F2] (D.map B.subtype) :=
  Submodule.equivMapOfInjective B.subtype Subtype.val_injective D

@[simp] theorem outputFactor_val (B : Submodule F2 F) (D : Submodule F2 B) (x : D) :
    ((outputFactor B D x : D.map B.subtype) : F) = ((x : B) : F) := rfl

def parameterFactor (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    Parameter C D ≃ₗ[F2] Parameter (C.comap A.mkQ) (D.map B.subtype) :=
  LinearEquiv.arrowCongr (quotientFactor A C).symm (outputFactor B D)

theorem parameterFactor_embedding (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) (N : Parameter C D) :
    embed (C.comap A.mkQ) (D.map B.subtype) (parameterFactor A B C D N) =
      RestrictionTransport.nestedEmbedding A B C D N := by
  ext x
  change ((outputFactor B D (N (quotientFactor A C ((C.comap A.mkQ).mkQ x)))) : F) =
    ((N (C.mkQ (A.mkQ x)) : B) : F)
  rw [quotientFactor_mkQ]
  rfl

end Appendix.NaturalTransport

namespace Appendix.RestrictionTransport

open NaturalTransport

/-- Exact effective annihilator and target of a nested restriction. -/
theorem exists_nested_embed_iff (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) (M : E →ₗ[F2] F) :
    (∃ N : Parameter C D, nestedEmbedding A B C D N = M) ↔
      C.comap A.mkQ ≤ M.ker ∧ M.range ≤ D.map B.subtype := by
  rw [← exists_embed_iff]
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨parameterFactor A B C D N, (parameterFactor_embedding A B C D N).trans hN⟩
  · rintro ⟨N, hN⟩
    refine ⟨(parameterFactor A B C D).symm N, ?_⟩
    rw [← parameterFactor_embedding, LinearEquiv.apply_symm_apply]
    exact hN

/-- Nested and effective direct restrictions describe exactly the same perturbations. -/
theorem nested_range_eq (A : Submodule F2 E) (B : Submodule F2 F)
    (C : Submodule F2 (E ⧸ A)) (D : Submodule F2 B) :
    (nestedEmbedding A B C D).range =
      (embedding (C.comap A.mkQ) (D.map B.subtype)).range := by
  ext M
  change (∃ N, nestedEmbedding A B C D N = M) ↔
    (∃ N, embed (C.comap A.mkQ) (D.map B.subtype) N = M)
  rw [exists_nested_embed_iff, exists_embed_iff]

end Appendix.RestrictionTransport

end Nested

namespace Appendix.RestrictionTransport

section SameRange

variable {K : Type*} {G : Type*} {P : Type*} {Q : Type*} [Field K]
  [AddCommGroup G] [Module K G] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]

/-- The actual linear change of parameters between two injective presentations. -/
def sameRangeEquiv (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) : P ≃ₗ[K] Q :=
  (LinearEquiv.ofInjective f hf).trans
    ((LinearEquiv.ofEq _ _ h).trans (LinearEquiv.ofInjective g hg).symm)

theorem sameRangeEquiv_commutes (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (x : P) :
    g (sameRangeEquiv f g hf hg h x) = f x := by
  simp [sameRangeEquiv]

variable [Fintype P] [Fintype Q]

/-- Injective parameter changes preserve normalized uniform expectations. -/
theorem expect_eq_of_same_range (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (observable : G → ℝ) :
    (𝔼 x, observable (f x)) = 𝔼 y, observable (g y) := by
  exact Fintype.expect_equiv (sameRangeEquiv f g hf hg h).toEquiv _ _
    (fun x => congrArg observable (sameRangeEquiv_commutes f g hf hg h x).symm)

/-- Preserve second moments at the same full ambient translate. -/
theorem restriction_secondMoment_eq_of_same_range
    (f : P →ₗ[K] G) (g : Q →ₗ[K] G)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : f.range = g.range) (observable : G → ℝ) (T : G) :
    (𝔼 x, observable (T + f x) ^ 2) = 𝔼 y, observable (T + g y) ^ 2 :=
  expect_eq_of_same_range f g hf hg h (fun z => observable (T + z) ^ 2)


end SameRange

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F] [Finite E] [Finite F]

local instance (A : Submodule F2 E) : Finite (E ⧸ A) :=
  Finite.of_surjective A.mkQ A.mkQ_surjective


end Appendix.RestrictionTransport

namespace Appendix.LinearIdentities

variable {K : Type*} {W : Type*} {V : Type*} [Field K]
  [AddCommGroup W] [AddCommGroup V] [Module K W] [Module K V]

/-- A subspace disjoint from the image has exactly the original kernel as preimage. -/
theorem a5_preimage_eq_ker (X : W →ₗ[K] V) (A₀ : Submodule K V)
    (hd : Disjoint A₀ (LinearMap.range X)) : A₀.comap X = LinearMap.ker X := by
  ext w
  constructor
  · intro hw
    exact Submodule.disjoint_def.mp hd (X w) hw ⟨w, rfl⟩
  · intro hw
    change X w ∈ A₀
    rw [show X w = 0 from hw]
    exact A₀.zero_mem

/-- Restricting to a subspace that covers the domain modulo the kernel preserves the image. -/
theorem a5_range_domRestrict_eq_of_cover (X : W →ₗ[K] V) (B₀ : Submodule K W)
    (hc : B₀ ⊔ LinearMap.ker X = ⊤) :
    LinearMap.range (X.domRestrict B₀) = LinearMap.range X := by
  rw [LinearMap.range_domRestrict, Submodule.map_eq_range_iff]
  exact codisjoint_iff.mpr hc

/-- The A.5 compressed image pulls back to its exact effective annihilator. -/
theorem a5_effective_annihilator (X : W →ₗ[K] V)
    (A₀ A : Submodule K V) (B₀ : Submodule K W)
    (hA : A₀ ⊔ LinearMap.range X = A)
    (hc : B₀ ⊔ LinearMap.ker X = ⊤) :
    (LinearMap.range (compress X A₀ B₀)).comap A₀.mkQ = A := by
  rw [compress, LinearMap.range_comp, a5_range_domRestrict_eq_of_cover X B₀ hc,
    Submodule.comap_map_mkQ, hA]

/-- The A.5 compressed kernel maps to its exact effective codomain. -/
theorem a5_effective_codomain (X : W →ₗ[K] V)
    (A₀ : Submodule K V) (B B₀ : Submodule K W)
    (hd : Disjoint A₀ (LinearMap.range X))
    (hB : B₀ ⊓ LinearMap.ker X = B) :
    (LinearMap.ker (compress X A₀ B₀)).map B₀.subtype = B := by
  rw [compress, LinearMap.ker_comp, Submodule.ker_mkQ]
  change ((A₀.comap X).comap B₀.subtype).map B₀.subtype = B
  rw [a5_preimage_eq_ker X A₀ hd, Submodule.map_comap_subtype, hB]

end Appendix.LinearIdentities

end

end UniqueGamesTheorem

end OAI
