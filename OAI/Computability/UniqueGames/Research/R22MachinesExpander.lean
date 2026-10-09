import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineControlLemmas
import OAI.Computability.UniqueGames.Reduction.MachineTransfer

namespace OAI.UniqueGamesTheorem.Foundations.Complexity.MachineControl

open Turing MachineComposition

/-! Shared conjugation of actual traces into finite state coordinates. -/

theorem statement_symm_roundtrip {K Λ σ τ : Type} {Γ : K → Type}
    (states : σ ≃ τ) (q : TM2.Stmt Γ Λ σ) :
    MachineControl.statement id states.symm (MachineControl.statement id states q) = q := by
  induction q <;>
    simp_all only [MachineControl.statement, Equiv.apply_symm_apply,
      Equiv.symm_apply_apply, id_eq]

/-- Static state-coordinate transport preserves every actual transition. -/
theorem pulledTrace {K Λ σ τ : Type} {Γ : K → Type} [DecidableEq K]
    (states : σ ≃ τ) (target : Λ → TM2.Stmt Γ Λ τ)
    (n : Nat) (start finish : TM2.Cfg Γ Λ σ)
    (run : (advance (TM2.step (MachineControl.program (Equiv.refl Λ) states.symm target)))^[n]
      (some start) = some finish) :
    (advance (TM2.step target))^[n]
      (some (MachineControl.configuration id states start)) =
      some (MachineControl.configuration id states finish) := by
  let source := MachineControl.program (Equiv.refl Λ) states.symm target
  have roundtrip : MachineControl.program (Equiv.refl Λ) states source = target := by
    funext label
    change MachineControl.statement id states
      (MachineControl.statement id states.symm (target label)) = target label
    exact statement_symm_roundtrip states.symm _
  have simulation : ∀ a b, TM2.step source a = some b →
      TM2.step target (MachineControl.configuration id states a) =
        some (MachineControl.configuration id states b) := by
    intro a b hab
    have h := MachineControl.step_simulation (Equiv.refl Λ) states source a
    rw [roundtrip, hab] at h
    exact h
  exact liftSuccessfulTrace (TM2.step source) (TM2.step target)
    (MachineControl.configuration id states) simulation n start finish run

theorem transferTrace {K Λ σ τ : Type} {Γ : K → Type} [DecidableEq K]
    (source destination : K) (states : (σ × Option (Γ destination)) ≃ τ)
    (distinct : source ≠ destination) (convert : Γ source → Γ destination)
    (fallback : Γ destination) (again : Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt Γ Λ τ)
    (code : target again = MachineControl.statement id states
      (Reduction.MachineTransfer.loopAt source destination convert fallback again exit))
    (base : (k : K) → List (Γ k)) (ambient : σ) (register : Option (Γ destination)) :
    (advance (TM2.step target))^[(base source).length + 1]
      (some ⟨some again, states (ambient, register), base⟩) =
      some ⟨exit, states (ambient, none),
        Reduction.MachineTransfer.tapesAt source destination base []
          ((base source).reverse.map convert ++ base destination)⟩ := by
  let raw := MachineControl.program (Equiv.refl Λ) states.symm target
  have atRaw : raw again = Reduction.MachineTransfer.loopAt source destination convert fallback again exit := by
    change MachineControl.statement id states.symm (target again) = _
    rw [code]
    exact statement_symm_roundtrip states _
  have run := Reduction.MachineTransfer.transferAt_fromTapes source destination distinct convert fallback
    again exit raw atRaw base ambient register
  unfold Reduction.MachineTransfer.nextAt at run
  simpa only [MachineControl.configuration, Option.map_some, id_eq, Option.map_id] using
    pulledTrace states target ((base source).length + 1) _ _ run

end OAI.UniqueGamesTheorem.Foundations.Complexity.MachineControl
