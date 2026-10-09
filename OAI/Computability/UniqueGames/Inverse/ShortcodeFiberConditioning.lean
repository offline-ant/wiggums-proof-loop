/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Inverse.ShortcodeFiberLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode

private theorem card_nonzero_real {T : Type*} [Fintype T] [Zero T] :
    (Fintype.card {x : T // x ≠ 0} : ℝ) = (Fintype.card T : ℝ) - 1 := by
  have hs := Fintype.sum_eq_add_sum_subtype_ne (fun _ : T => (1 : ℝ)) 0
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
  linarith

/-- Exact decomposition of a uniform two-factor law with a self-loop on either
zero factor. No nonemptiness is required of the nonzero subtypes. -/
theorem uniform_pair_mixture {A B : Type*} [Fintype A] [Fintype B]
    [Zero A] [Zero B] (h : A → B → ℝ)
    (hleft : ∀ b, h 0 b = 1) (hright : ∀ a, h a 0 = 1) :
    (𝔼 a, 𝔼 b, h a b) =
      (Fintype.card A : ℝ)⁻¹ + (Fintype.card B : ℝ)⁻¹ -
        (Fintype.card A : ℝ)⁻¹ * (Fintype.card B : ℝ)⁻¹ +
      (1 - ((Fintype.card A : ℝ)⁻¹ + (Fintype.card B : ℝ)⁻¹ -
        (Fintype.card A : ℝ)⁻¹ * (Fintype.card B : ℝ)⁻¹)) *
        (𝔼 p : {a : A // a ≠ 0} × {b : B // b ≠ 0}, h p.1.val p.2.val) := by
  let R : ℝ := 𝔼 p : {a : A // a ≠ 0} × {b : B // b ≠ 0},
    h p.1.val p.2.val
  have hNZ : (∑ a : {a : A // a ≠ 0}, ∑ b : {b : B // b ≠ 0}, h a.val b.val) =
      ((Fintype.card A : ℝ) - 1) * ((Fintype.card B : ℝ) - 1) * R := by
    simpa only [Fintype.card_prod, Nat.cast_mul, card_nonzero_real, Fintype.sum_prod_type]
      using (Fintype.card_mul_expect
        (fun p : {a : A // a ≠ 0} × {b : B // b ≠ 0} => h p.1.val p.2.val)).symm
  have hsum : (∑ a : A, ∑ b : B, h a b) =
      (Fintype.card A : ℝ) + (Fintype.card B : ℝ) - 1 +
        ((Fintype.card A : ℝ) - 1) * ((Fintype.card B : ℝ) - 1) * R := by
    rw [Fintype.sum_eq_add_sum_subtype_ne (fun a : A => ∑ b : B, h a b) 0]
    simp only [hleft, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    simp_rw [Fintype.sum_eq_add_sum_subtype_ne (h _) 0, hright]
    rw [Finset.sum_add_distrib, hNZ]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, card_nonzero_real]
    ring
  have hA : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  change (𝔼 a, 𝔼 b, h a b) = _ + (1 - _) * R
  simp only [Fintype.expect_eq_sum_div_card, div_eq_mul_inv, ← Finset.sum_mul]
  rw [hsum]
  field_simp [hA, hB]
  ring

private theorem vector_card_real (n : ℕ) :
    (Fintype.card (Vector n) : ℝ) = (2 : ℝ) ^ n := by
  simp [Shortcode.Vector, F2]

private theorem binary_zero_mass_nonneg (ell m : ℕ) :
    0 ≤ ((2 : ℝ) ^ ell)⁻¹ + ((2 : ℝ) ^ m)⁻¹ -
      ((2 : ℝ) ^ (ell + m))⁻¹ := by
  have ha : 0 ≤ ((2 : ℝ) ^ ell)⁻¹ := by positivity
  have hb : 0 ≤ ((2 : ℝ) ^ m)⁻¹ := by positivity
  have hb1 : ((2 : ℝ) ^ m)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [pow_add, mul_inv]
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hb1)]

/-- The actual equality test has a nonempty output fiber retaining at least
`η/2` after both factors are conditioned to be nonzero. The displayed order
samples a uniform matrix in that fiber first, as required by the Grassmann
neighbor correspondence. -/
theorem conditioned_output_fiber {ell m : ℕ}
    (f : Mat ell m → Vector ell) {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hzero : ((2 : ℝ) ^ ell)⁻¹ + ((2 : ℝ) ^ m)⁻¹ -
      ((2 : ℝ) ^ (ell + m))⁻¹ ≤ η / 2)
    (haccept : η ≤ equalityAcceptance f) :
    ∃ y, (matrixFiber f y).Nonempty ∧
      η / 2 ≤ (matrixFiber f y).expect (fun M =>
        𝔼 p : {a : Vector ell // a ≠ 0} × {l : Vector m // l ≠ 0},
          if f (M + rankOne p.1.val p.2.val) = y then (1 : ℝ) else 0) := by
  obtain ⟨y, hy, hret⟩ := exists_output_fiber_factor_retention f haccept
  refine ⟨y, hy, ?_⟩
  have hmix := uniform_pair_mixture (fiberFactorRetention f y)
    (fiberFactorRetention_zero_left f y hy) (fiberFactorRetention_zero_right f y hy)
  simp only [vector_card_real, ← mul_inv, ← pow_add] at hmix
  have hconditioned := EqualityFiber.nonzero_retention_ge_half hη hη1
    (binary_zero_mass_nonneg ell m) hzero (hmix ▸ hret)
  apply hconditioned.trans
  apply le_of_eq
  unfold fiberFactorRetention
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro M _
  apply Finset.expect_congr (by ext p; simp)
  intro p _
  rfl

end
end UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

end

end OAI
