/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Algebra.Order.BigOperators.Expect
import OAI.Computability.UniqueGames.Inverse.EqualityFiber
import OAI.Computability.UniqueGames.Inverse.MatrixChartLemmas
import OAI.Computability.UniqueGames.Inverse.ShortcodeInterfaceLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode MatrixChart

def matrixFiber {ell m : ℕ} (f : Mat ell m → Vector ell) (y : Vector ell) :
    Finset (Mat ell m) := Finset.univ.filter fun M => f M = y

def liftedFiber {ell m : ℕ} (f : Mat ell m → Vector ell) (y : Vector ell) :
    Finset (KMS.Vertex (ell + m) ell) := (matrixFiber f y).image matrixVertex

theorem liftedFiber_subset_chart {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    liftedFiber f y ⊆ matrixChart ell m := by
  intro L hL
  obtain ⟨M, _, rfl⟩ := Finset.mem_image.mp hL
  exact (mem_matrixChart _).mpr ⟨M, rfl⟩

@[simp] theorem matrixVertex_mem_liftedFiber {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) (M : Mat ell m) :
    matrixVertex M ∈ liftedFiber f y ↔ f M = y := by
  constructor
  · intro h
    obtain ⟨N, hN, hNM⟩ := Finset.mem_image.mp h
    have : N = M := matrixVertex_injective hNM
    subst N
    exact (Finset.mem_filter.mp hN).2
  · intro h
    exact Finset.mem_image.mpr ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

/-- The slice and the interval intersected with the chart correspond exactly.
The hypothesis states equality of the actual membership predicates. -/
theorem image_slice_points {ell m : ℕ} (S : Slice ell m)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I) :
    S.points.image matrixVertex = I ∩ matrixChart ell m := by
  ext L
  constructor
  · intro h
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_inter.mpr ⟨(hS M).mp (Finset.mem_filter.mp hM).2,
      (mem_matrixChart _).mpr ⟨M, rfl⟩⟩
  · intro h
    obtain ⟨hI, hC⟩ := Finset.mem_inter.mp h
    obtain ⟨M, rfl⟩ := (mem_matrixChart _).mp hC
    exact Finset.mem_image.mpr ⟨M,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hS M).mpr hI⟩, rfl⟩

theorem image_slice_fiber {ell m : ℕ} (S : Slice ell m)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I)
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    (S.points.filter fun M => f M = y).image matrixVertex =
      liftedFiber f y ∩ (I ∩ matrixChart ell m) := by
  ext L
  constructor
  · intro h
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hpoints, hfy⟩ := Finset.mem_filter.mp hM
    refine Finset.mem_inter.mpr ⟨(matrixVertex_mem_liftedFiber f y M).mpr hfy, ?_⟩
    rw [← image_slice_points S I hS]
    exact Finset.mem_image.mpr ⟨M, hpoints, rfl⟩
  · intro h
    obtain ⟨hf, hIC⟩ := Finset.mem_inter.mp h
    rw [← image_slice_points S I hS] at hIC
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hIC
    exact Finset.mem_image.mpr ⟨M, Finset.mem_filter.mpr
      ⟨hM, (matrixVertex_mem_liftedFiber f y M).mp hf⟩, rfl⟩

/-- Uniform agreement on a slice is the actual Grassmann fiber density in the
chart-intersected interval.  Empty sets are allowed on both sides of this
identity, with the standard zero-denominator convention. -/
theorem constantAgreement_eq_chart_density {ell m : ℕ} (S : Slice ell m)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I)
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    S.constantAgreement f y =
      KMS.relativeDensity (liftedFiber f y) (I ∩ matrixChart ell m) := by
  unfold Slice.constantAgreement KMS.relativeDensity
  rw [Finset.expect_eq_sum_div_card, Finset.sum_boole]
  rw [← image_slice_fiber S I hS f y, ← image_slice_points S I hS]
  simp only [Finset.card_image_of_injective _ matrixVertex_injective]

theorem hasAffineSlice_of_dense_interval {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell)
    (I : Finset (KMS.Vertex (ell + m) ell))
    (S : Slice ell m) (hS : ∀ M, S.Contains M ↔ matrixVertex M ∈ I)
    {α : ℝ} {r : ℕ} (hrows : S.rows ≤ r) (hcolumns : S.columns ≤ r)
    (hne : (liftedFiber f y ∩ I).Nonempty)
    (hdense : α ≤ KMS.relativeDensity (liftedFiber f y) I) :
    HasAffineSlice f α r := by
  obtain ⟨hIC, hα⟩ := KMS.density_bound_passes_to_chart
    (liftedFiber f y) I (matrixChart ell m)
    (liftedFiber_subset_chart f y) hne hdense
  have hpoints : S.points.Nonempty := by
    rw [← image_slice_points S I hS] at hIC
    exact Finset.image_nonempty.mp hIC
  apply hasAffineSlice_of_constant f α r S hrows hcolumns hpoints y
  rw [constantAgreement_eq_chart_density S I hS f y]
  exact hα

end
end UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

end

section

/-! Extract a nonempty output fiber directly from the finite equality-test
average, retaining the actual full uniform factor law. -/

namespace UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode

def fiberFactorRetention {ell m : ℕ} (f : Mat ell m → Vector ell)
    (y : Vector ell) (a : Vector ell) (l : Vector m) : ℝ :=
  (matrixFiber f y).expect fun M => if f (M + rankOne a l) = y then 1 else 0

theorem fiberFactorRetention_zero_left {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell)
    (hne : (matrixFiber f y).Nonempty) (l : Vector m) :
    fiberFactorRetention f y 0 l = 1 := by
  unfold fiberFactorRetention
  have hpoint (M : Mat ell m) (hM : M ∈ matrixFiber f y) :
      (if f (M + rankOne (0 : Vector ell) l) = y then (1 : ℝ) else 0) = 1 := by
    have hy := (Finset.mem_filter.mp hM).2
    simp [hy]
  rw [Finset.expect_congr rfl hpoint, Finset.expect_const hne]

theorem fiberFactorRetention_zero_right {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell)
    (hne : (matrixFiber f y).Nonempty) (a : Vector ell) :
    fiberFactorRetention f y a 0 = 1 := by
  unfold fiberFactorRetention
  have hpoint (M : Mat ell m) (hM : M ∈ matrixFiber f y) :
      (if f (M + rankOne a (0 : Vector m)) = y then (1 : ℝ) else 0) = 1 := by
    have hy := (Finset.mem_filter.mp hM).2
    simp [hy]
  rw [Finset.expect_congr rfl hpoint, Finset.expect_const hne]

/-- A nonempty actual output fiber whose retention under the full factor law
is at least the original equality acceptance threshold. -/
theorem exists_output_fiber_factor_retention {ell m : ℕ}
    (f : Mat ell m → Vector ell) {η : ℝ} (haccept : η ≤ equalityAcceptance f) :
    ∃ y, (matrixFiber f y).Nonempty ∧ η ≤ 𝔼 a, 𝔼 l, fiberFactorRetention f y a l := by
  obtain ⟨y, hy, hret⟩ := EqualityFiber.exists_fiber_expect_ge f
    (fun M => 𝔼 a, 𝔼 l, if f M = f (M + rankOne a l) then 1 else 0) haccept
  refine ⟨y, by simpa [matrixFiber, Finset.filter_nonempty_iff] using hy, hret.trans_eq ?_⟩
  calc
    _ = (matrixFiber f y).expect (fun M =>
        𝔼 a, 𝔼 l, if f (M + rankOne a l) = y then (1 : ℝ) else 0) := by
      apply Finset.expect_congr (by ext M; simp [matrixFiber])
      intro M hM
      simp only [(Finset.mem_filter.mp hM).2, eq_comm]
    _ = _ := by
      unfold fiberFactorRetention
      rw [Finset.expect_comm]
      apply Finset.expect_congr rfl
      intro a _
      rw [Finset.expect_comm]

end
end UniqueGamesTheorem.Inverse.ShortcodeFromGrassmann

end

end OAI
