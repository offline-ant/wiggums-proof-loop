/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Machines.Runtime

namespace OAI

/-!
# Literal-word emission

Push a fixed word as one finite statement, preserving the ambient state and
all other tapes. Stateful symbol substitution is handled by `MachineTransducer`;
this module supplies its literal-emission primitive and push bound.
-/

namespace UniqueGamesTheorem.Reduction.MachineSubstitution

open Turing

open UniqueGamesTheorem.Foundations.Complexity

section PushWord

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

/-- Push a fixed word in its listed order, then execute the continuation. -/
def pushWord (dst : K) : List (Γ dst) → TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ σ
  | [], continuation => continuation
  | symbol :: word, continuation =>
      .push dst (fun _ => symbol) (pushWord dst word continuation)

/-- Literal pushes preserve the state and every other tape. -/
theorem stepAux_pushWord (dst : K) (word : List (Γ dst))
    (continuation : TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (pushWord dst word continuation) state tapes =
      TM2.stepAux continuation state
        (Function.update tapes dst (word.reverse ++ tapes dst)) := by
  induction word generalizing tapes with
  | nil => simp [pushWord]
  | cons symbol word ih =>
    simp only [pushWord, TM2.stepAux]
    rw [ih]
    simp only [Function.update_self, Function.update_idem, List.reverse_cons,
      List.append_assoc, List.singleton_append]

omit [DecidableEq K] in
theorem statementPushBound_pushWord (dst : K) (word : List (Γ dst))
    (continuation : TM2.Stmt Γ Λ σ) :
    Runtime.statementPushBound (pushWord dst word continuation) =
      word.length + Runtime.statementPushBound continuation := by
  induction word with
  | nil => simp [pushWord]
  | cons symbol word ih =>
    simp only [pushWord, Runtime.statementPushBound, ih, List.length_cons]
    omega

end PushWord

end UniqueGamesTheorem.Reduction.MachineSubstitution

end OAI
