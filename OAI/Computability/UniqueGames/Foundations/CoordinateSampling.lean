import OAI.Computability.UniqueGames.Foundations.SamplingLemmas

namespace OAI.UniqueGamesTheorem.Foundations.Games
open scoped BigOperators
noncomputable section

/-- Reconstruct a function from its restrictions inside and outside a set. -/
def restrictionProductEquiv {P X : Type*} [DecidableEq P] (J : Finset P) :
    (P → X) ≃ ((↥J → X) × ({j : P // j ∉ J} → X)) where
  toFun indices := (fun j => indices j.val, fun j => indices j.val)
  invFun parts := fun j =>
    if hj : j ∈ J then parts.1 ⟨j, hj⟩ else parts.2 ⟨j, hj⟩
  left_inv indices := by
    funext j
    by_cases hj : j ∈ J <;> simp [hj]
  right_inv parts := by
    apply Prod.ext <;> funext j <;> simp [j.property]

theorem expect_restrictIndices {P X : Type*} [Fintype P] [DecidableEq P]
    [Fintype X] [Nonempty X] (J : Finset P) (h : (↥J → X) → ℝ) :
    (𝔼 indices : P → X, h (fun j => indices j.val)) =
      𝔼 activeIndices : ↥J → X, h activeIndices := by
  calc
    _ = 𝔼 parts : (↥J → X) × ({j : P // j ∉ J} → X), h parts.1 :=
      Fintype.expect_equiv (restrictionProductEquiv J) _ _ (fun _ => rfl)
    _ = _ := by
      simpa only [Finset.univ_product_univ, Fintype.expect_const] using
        (Finset.expect_product (Finset.univ : Finset (↥J → X))
          (Finset.univ : Finset ({j : P // j ∉ J} → X)) (fun parts => h parts.1))


end
end OAI.UniqueGamesTheorem.Foundations.Games
