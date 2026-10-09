/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.Linarith
import OAI.Computability.UniqueGames.Analysis.MatrixCharactersLemmas
import OAI.Computability.UniqueGames.Analysis.MatrixRestrictions

namespace OAI

section

/-! Fourier expansion of actual affine restrictions and parity extraction. -/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixParityRow

open MatrixCharacters MatrixFourier MatrixParity
open scoped BigOperators Classical

variable {E C V : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C] [AddCommGroup V] [Module F2 V]

theorem traceCharacter_comp (Q : E →ₗ[F2] V) (A : V →ₗ[F2] C)
    (T : C →ₗ[F2] E) :
    linearTraceCharacter T (A.comp Q) = linearTraceCharacter (Q.comp T) A := by
  simp only [linearTraceCharacter_apply, linearTracePair, LinearMap.comp_assoc]

theorem traceCharacter_re_add (T : C →ₗ[F2] E) (X Y : E →ₗ[F2] C) :
    (linearTraceCharacter T (X + Y)).re =
      (linearTraceCharacter T X).re * (linearTraceCharacter T Y).re := by
  rw [AddChar.map_add_eq_mul, Complex.mul_re]
  simp [linearTraceCharacter_apply, binarySign_im]

variable [FiniteDimensional F2 E] [FiniteDimensional F2 C] [FiniteDimensional F2 V]
  [Fintype (E →ₗ[F2] C)] [Fintype (C →ₗ[F2] E)] [Fintype (V →ₗ[F2] C)]

omit [FiniteDimensional F2 E] [Fintype (E →ₗ[F2] C)] [Fintype (C →ₗ[F2] E)] in
/-- Characters restricted to the row vanish unless the dual map lands in the
kernel of `Q`. For `Q = W.mkQ` this is precisely `range T ≤ W`. -/
theorem row_character_average (Q : E →ₗ[F2] V) (T : C →ₗ[F2] E) :
    (𝔼 A : V →ₗ[F2] C, (linearTraceCharacter T (A.comp Q)).re) =
      if Q.comp T = 0 then 1 else 0 := by
  have hcomplex : (𝔼 A : V →ₗ[F2] C,
      linearTraceCharacter T (A.comp Q)) = if Q.comp T = 0 then 1 else 0 := by
    simp only [traceCharacter_comp, Fintype.expect_eq_sum_div_card,
      sum_linearTraceCharacter]
    split <;> simp [Fintype.card_ne_zero]
  have h := congrArg Complex.re hcomplex
  simpa only [Complex.re_expect, apply_ite, Complex.one_re, Complex.zero_re] using h


end UniqueGamesTheorem.Fourier.MatrixParityRow

end

end

end OAI
