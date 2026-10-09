/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import OAI.Computability.UniqueGames.Quadratic.AlignmentCertificateLemmas
import OAI.Computability.UniqueGames.Quadratic.Block

namespace OAI

section

/-!
# Trace coordinates for families of binary characters

The trace pairing identifies the binary dual of `F³` with `F³` itself.  Its
inverse is linear, so a common-parent family of binary functionals produces
one binary-linear lift `g`, as required by the all-lifts genericity theorem.
-/

namespace UniqueGamesTheorem.Quadratic

noncomputable section

variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

/-- Restrict the standard field dot product to binary scalars and apply the trace. -/
def traceDotForm : LinearMap.BilinForm (ZMod 2) (Vec F) :=
  traceBinary.compBilinForm (dotProductBilin F F)

omit [Finite F] in
@[simp] theorem traceDotForm_apply (z y : Vec F) :
    traceDotForm z y = traceBinary (dot z y) := by
  simp [traceDotForm, dotProduct, Fin.sum_univ_three, dot]

/-- Nondegeneracy holds coordinate by coordinate over the finite field. -/
theorem traceDotForm_nondegenerate :
    (traceDotForm (F := F)).Nondegenerate := by
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro z hz
  ext i
  apply (trace_mul_vanish_iff (z i)).mp
  intro t
  have h := hz (Pi.single i t)
  have hd : dot z (Pi.single i t) = t * z i := by
    fin_cases i <;> simp [dot, mul_comm]
  simpa only [traceDotForm_apply, hd] using h

/-- The exact binary trace-pairing identification. -/
def traceDualEquiv : Vec F ≃ₗ[ZMod 2] (Vec F →ₗ[ZMod 2] ZMod 2) :=
  traceDotForm.toDual traceDotForm_nondegenerate

@[simp] theorem traceDualEquiv_apply (z y : Vec F) :
    traceDualEquiv z y = traceBinary (dot z y) := traceDotForm_apply z y

@[simp] theorem traceDualEquiv_symm_apply
    (γ : Vec F →ₗ[ZMod 2] ZMod 2) (y : Vec F) :
    traceBinary (dot (traceDualEquiv.symm γ) y) = γ y := by
  rw [← traceDualEquiv_apply, LinearEquiv.apply_symm_apply]

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- Taking trace coordinates preserves linear dependence on the family index. -/
def representTraceFamily (γ : W →ₗ[ZMod 2] (Vec F →ₗ[ZMod 2] ZMod 2)) :
    W →ₗ[ZMod 2] Vec F :=
  traceDualEquiv.symm.toLinearMap.comp γ

theorem representTraceFamily_spec
    (γ : W →ₗ[ZMod 2] (Vec F →ₗ[ZMod 2] ZMod 2)) (z : W) (y : Vec F) :
    traceBinary (dot (representTraceFamily γ z) y) = γ z y :=
  traceDualEquiv_symm_apply (γ z) y

end

end UniqueGamesTheorem.Quadratic

end

end OAI
