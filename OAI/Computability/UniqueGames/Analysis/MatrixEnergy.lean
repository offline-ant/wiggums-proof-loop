/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Analysis.MatrixCharactersLemmas
import OAI.Computability.UniqueGames.Analysis.MatrixRestrictions
import OAI.Computability.UniqueGames.Analysis.MatrixSubspaceCount

namespace OAI

section

namespace UniqueGamesTheorem.Fourier.MatrixEnergy

open scoped BigOperators

variable {Q : Type*} {I : Q → Type*} [Fintype Q] [∀ q, Fintype (I q)]

/-- Squared coefficient energy, averaged using the supplied question weights. -/
noncomputable def energy (weight : Q → ℝ) (a : (q : Q) → I q → ℝ) : ℝ :=
  ∑ q, weight q * ∑ i, a q i ^ 2

/-- Squared energy retained by a coordinate projection. -/
noncomputable def cutoffEnergy (weight : Q → ℝ) (keep : (q : Q) → I q → Prop)
    (a : (q : Q) → I q → ℝ) : ℝ := by
  classical
  exact ∑ q, weight q * ∑ i, if keep q i then a q i ^ 2 else 0

/-- Diagonal spectral quadratic form. -/
noncomputable def spectralEnergy (weight : Q → ℝ) (eigen a : (q : Q) → I q → ℝ) : ℝ :=
  ∑ q, weight q * ∑ i, eigen q i * a q i ^ 2


section LinearMaps

open MatrixCharacters MatrixFourier

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]


/-- Color indicator of one actual labeling. -/
noncomputable def colorIndicator {X Y : Type*} (label : X → Y) (y : Y) : X → ℝ := by
  classical
  exact fun x => if label x = y then 1 else 0

theorem colorIndicator_partition {X Y : Type*} [Fintype Y]
    (label : X → Y) (x : X) : ∑ y, colorIndicator label y x ^ 2 = 1 := by
  classical
  simp [colorIndicator, eq_comm]

/-- Parseval for all color indicators sums to exactly one, with the correct
uniform primal normalization and counting measure on Fourier indices. -/
theorem colorIndicator_parseval {Y : Type*} [Fintype Y]
    (label : (E →ₗ[F2] F) → Y) :
    (∑ y, ∑ S : F →ₗ[F2] E, linearCoeff (colorIndicator label y) S ^ 2) = 1 := by
  simp_rw [linear_parseval]
  rw [← Finset.expect_sum_comm]
  simp_rw [colorIndicator_partition]
  exact Fintype.expect_const 1

/-- Fourier coefficient array for a family of labelings, including color as
part of the component index. -/
noncomputable def labelingCoeff {Y : Type*}
    (label : Q → (E →ₗ[F2] F) → Y) (qy : Q × Y) (S : F →ₗ[F2] E) : ℝ :=
  linearCoeff (colorIndicator (label qy.1) qy.2) S

theorem labelingCoeff_energy_one {Y : Type*} [Fintype Y]
    (weight : Q → ℝ) (label : Q → (E →ₗ[F2] F) → Y)
    (hnorm : ∑ q, weight q = 1) :
    energy (fun qy : Q × Y => weight qy.1) (labelingCoeff label) = 1 := by
  classical
  calc
    energy (fun qy : Q × Y => weight qy.1) (labelingCoeff label) =
        ∑ q, weight q * (∑ y, ∑ S : F →ₗ[F2] E,
          linearCoeff (colorIndicator (label q) y) S ^ 2) := by
      simp only [energy, labelingCoeff, Fintype.sum_prod_type, Finset.mul_sum]
    _ = ∑ q, weight q := by simp only [colorIndicator_parseval, mul_one]
    _ = 1 := hnorm


end LinearMaps

section DependentLinearMaps

open MatrixCharacters MatrixFourier

variable {J : Type*} [Fintype J] {E : J → Type*} {F : Type*}
    [∀ j, AddCommGroup (E j)] [∀ j, Module F2 (E j)]
    [AddCommGroup F] [Module F2 F]
    [∀ j, FiniteDimensional F2 (E j)] [FiniteDimensional F2 F]
    [∀ j, Fintype (E j →ₗ[F2] F)] [∀ j, Fintype (F →ₗ[F2] E j)]


end DependentLinearMaps


section QuestionProbabilities

variable {Ω : Q → Type*} [∀ q, Fintype (Ω q)]
variable {Y A : Type*} [Fintype Y] [Fintype A]


end QuestionProbabilities

section ActualBadRows

open MatrixCharacters

variable {C : Type*} [AddCommGroup C] [Module F2 C]
    [FiniteDimensional F2 C] [Fintype C]
    {E : Q → Type*} [∀ q, AddCommGroup (E q)] [∀ q, Module F2 (E q)]
    [∀ q, Finite (E q)] [∀ q, Fintype (E q →ₗ[F2] C)]


end ActualBadRows

end UniqueGamesTheorem.Fourier.MatrixEnergy

end

end OAI
