/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace OAI.UniqueGamesTheorem.Inverse.EqualityFiber

open scoped BigOperators Classical

/-- A finite average is bounded by the average on some nonempty output fiber.
Apply weighted pigeonhole to the centered summands, using only attained outputs
as pigeonholes. No transition kernel or probability-weight representation is needed. -/
theorem exists_fiber_expect_ge {X Y : Type*} [Fintype X] [Nonempty X]
    (f : X → Y) (g : X → ℝ) {η : ℝ} (h : η ≤ 𝔼 x, g x) :
    ∃ y, (Finset.univ.filter fun x => f x = y).Nonempty ∧
      η ≤ (Finset.univ.filter fun x => f x = y).expect g := by
  classical
  have hsum : 0 ≤ ∑ x, (g x - η) := by
    rw [Fintype.expect_eq_sum_div_card] at h
    have hc : (0 : ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
    have h' := (le_div_iff₀ hc).mp h
    simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, sub_nonneg, mul_comm] using h'
  obtain ⟨y, hy, hfiber⟩ := Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
    (f := f) (w := fun x => g x - η) (b := (0 : ℝ))
    (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    (Finset.univ_nonempty.image f) (by simpa using hsum)
  obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
  have hne : (Finset.univ.filter fun x => f x = y).Nonempty :=
    ⟨x, Finset.mem_filter.mpr ⟨hx, hxy⟩⟩
  refine ⟨y, hne, ?_⟩
  rw [Finset.expect_eq_sum_div_card, le_div_iff₀ (Nat.cast_pos.mpr hne.card_pos)]
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    sub_nonneg, mul_comm] using hfiber

/-- Removing a self-loop mass `p₀ ≤ η/2` leaves retention at least `η/2`.
This is the precise algebra needed when one or both rank-one factors may be
zero in the unconditioned test. -/
theorem nonzero_retention_ge_half {η p₀ R : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hp₀ : 0 ≤ p₀) (hp₀η : p₀ ≤ η / 2)
    (haccept : η ≤ p₀ + (1 - p₀) * R) : η / 2 ≤ R := by
  have hp₀1 : p₀ < 1 := by linarith
  have hden : 0 < 1 - p₀ := by linarith
  have hprod : η / 2 * (1 - p₀) ≤ (1 - p₀) * R := by nlinarith
  nlinarith

end OAI.UniqueGamesTheorem.Inverse.EqualityFiber
