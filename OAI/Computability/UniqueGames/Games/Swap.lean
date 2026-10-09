import OAI.Computability.UniqueGames.Foundations.ValueLemmas

namespace OAI.UniqueGamesTheorem.Foundations.Games.Game

open scoped BigOperators
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

/-- Exchange players without changing their joint question distribution. -/
def swap (G : Game Q₁ Q₂ A₁ A₂) : Game Q₂ Q₁ A₂ A₁ where
  questions :=
    { weight := fun q => G.questions.weight (q.2, q.1)
      nonnegative := fun q => G.questions.nonnegative (q.2, q.1)
      normalized := by
        rw [Fintype.sum_prod_type, Finset.sum_comm, ← Fintype.sum_prod_type]
        exact G.questions.normalized }
  accepts y x b a := G.accepts x y a b

@[simp] theorem success_swap (G : Game Q₁ Q₂ A₁ A₂)
    (s : Strategy Q₂ Q₁ A₂ A₁) : G.swap.success s = G.success (s.2, s.1) := by
  unfold success FiniteDistribution.probability
  rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_prod_type]
  rfl

@[simp] theorem value_swap [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂) : G.swap.value = G.value := by
  apply le_antisymm
  · apply (G.swap.value_le_iff _).mpr
    intro s
    rw [success_swap]
    exact G.success_le_value _
  · apply (G.value_le_iff _).mpr
    intro s
    simpa only [success_swap] using G.swap.success_le_value (s.2, s.1)

/-- Exchanging the players commutes with every finite repetition. -/
theorem swap_repetition (G : Game Q₁ Q₂ A₁ A₂) (n : Nat) :
    G.swap.repetition n = (G.repetition n).swap := by
  have hq : (G.swap.repetition n).questions = ((G.repetition n).swap).questions :=
    FiniteDistribution.eq_of_weight_eq (fun _ => rfl)
  exact congrArg (fun μ => Game.mk μ (G.swap.repetition n).accepts) hq

end
end OAI.UniqueGamesTheorem.Foundations.Games.Game
