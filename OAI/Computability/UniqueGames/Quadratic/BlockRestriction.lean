/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Quadratic.BlockKernelLemmas
import OAI.Computability.UniqueGames.Quadratic.TraceDual

namespace OAI

section

/-!
# Actual child restriction maps

A common-parent lift `g` gives a binary linear map from its logical character
space into the dual of each quadratic block.  Its kernel is literal character
annihilation, so the trace calculation and the all-lifts genericity predicate
apply directly to this map.
-/

namespace UniqueGamesTheorem.Quadratic

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

/-- Restriction to one block of the two trace pairings, linear in the
logical character through the common lift and subspace inclusion. -/
def blockRestriction (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (v : Vec F) :
    S →ₗ[ZMod 2] ((U v) →ₗ[ZMod 2] ZMod 2) :=
  let B : S →ₗ[ZMod 2] ((U v) →ₗ[ZMod 2] ZMod 2) :=
    ((traceDotForm.compl₁₂ g (LinearMap.fst _ _ _)) +
    (traceDotForm.compl₁₂ S.subtype (LinearMap.snd _ _ _))).compl₂ (U v).subtype
  -- Consumers unfold restriction to the literal character, so retain that `toFun`.
  B.copy (fun z => (B z).copy (fun p => blockCharacter (g z) z p)
    (by funext p; simp [B, blockCharacter]))
    (by funext z; exact LinearMap.copy_eq _ _ _)

omit [Fintype F] in
@[simp] theorem blockRestriction_apply (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (v : Vec F) (z : S) (p : U v) :
    blockRestriction S g v z p = blockCharacter (g z) z p := rfl

omit [Fintype F] in
/-- Equality to zero is exactly annihilation of the underlying block. -/
theorem blockRestriction_eq_zero_iff (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) (v : Vec F) (z : S) :
    blockRestriction S g v z = 0 ↔ BlockAnnihilates (g z) z v := by
  constructor
  · intro h p hp
    exact LinearMap.congr_fun h ⟨p, hp⟩
  · intro h
    ext p
    exact h p p.property

/-- The exact kernel formula for a nonzero logical character. -/
theorem mem_ker_blockRestriction_iff (S : Submodule (ZMod 2) (Vec F))
    (g : S →ₗ[ZMod 2] Vec F) {v : Vec F} (hv : v ≠ 0)
    {z : S} (hz : z ≠ 0) :
    z ∈ (blockRestriction S g v).ker ↔
      (z : Vec F) ∈ line v ∧
        dot (g z) z = squareRoot (z.val 0 * z.val 1 * z.val 2) := by
  have hz' : (z : Vec F) ≠ 0 := fun h => hz (Subtype.ext h)
  rw [LinearMap.mem_ker, blockRestriction_eq_zero_iff, blockAnnihilates_iff hv hz']

/-- Nonproportionality of a generic space makes every actual block kernel
contain at most one nonzero character. -/
theorem blockRestriction_nonzero_kernel_unique
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    {v : Vec F} (hv : v ≠ 0) (hS : IsGeneric S)
    (z w : S) (hz : z ≠ 0) (hw : w ≠ 0)
    (hgz : blockRestriction S g v z = 0)
    (hgw : blockRestriction S g v w = 0) : z = w := by
  have hzline := mem_line_of_blockAnnihilates hv
    ((blockRestriction_eq_zero_iff S g v z).mp hgz)
  have hwline := mem_line_of_blockAnnihilates hv
    ((blockRestriction_eq_zero_iff S g v w).mp hgw)
  obtain ⟨t, ht⟩ := (mem_line_iff v z).mp hzline
  obtain ⟨s, hs⟩ := (mem_line_iff v w).mp hwline
  have hsne : s ≠ 0 := by
    intro hzero
    apply hw
    apply Subtype.ext
    simpa [hzero] using hs.symm
  apply hS.1 z w hz hw
  refine ⟨t / s, ?_⟩
  rw [← ht, ← hs, smul_smul, div_mul_cancel₀ _ hsne]

/-- Every actual child restriction map loses at most one binary dimension. -/
theorem finrank_ker_blockRestriction_le_one
    (S : Submodule (ZMod 2) (Vec F)) (g : S →ₗ[ZMod 2] Vec F)
    {v : Vec F} (hv : v ≠ 0) (hS : IsGeneric S) :
    Module.finrank (ZMod 2) (blockRestriction S g v).ker ≤ 1 :=
  finrank_ker_le_one_of_nonzero_unique (blockRestriction S g v)
    (blockRestriction_nonzero_kernel_unique S g hv hS)


end

end UniqueGamesTheorem.Quadratic

end

end OAI
