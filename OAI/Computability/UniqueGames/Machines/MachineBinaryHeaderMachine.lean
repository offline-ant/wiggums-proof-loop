/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.Reduction.MachineTransfer

namespace OAI

/-!
An actual finite Boolean-stack routine prepending two unary header words to an
already restored serialized body. It consumes counters containing `n` and `m`
true bits, respectively, in exactly `n + m + 4` transitions. All ambient stacks
and the finite ambient state are preserved. The input counters need no separate
counting pass: a caller can accumulate them while constructing the body.

A single-header routine is composed twice, using four displayed instruction
equations. This is a staged configuration computation, not a single-input
`initList` assertion that silently assumes two extra inputs.
-/

namespace UniqueGamesTheorem.BinaryHeaderMachine

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool

section Placement

variable {K Λ A : Type} [DecidableEq K]

/-- A fixed one-bit push; the finite register is cleared before continuation. -/
def delimiter (destination : K) (next : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .push destination (fun _ => false)
    (.load (fun state => (state.1, none)) (.goto fun _ => next))

def tapes (variableTape clauses destination : K) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base variableTape variableCounter)
    clauses clauseCounter) destination output

/-- Push the delimiter and transfer a unary counter, preserving all other tapes. -/
theorem prependTrace (source destination : K) (distinct : source ≠ destination)
    (start loop : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atStart : program start = delimiter destination loop)
    (atLoop : program loop = loopAt source destination id false loop exit)
    (base : K → List Bool) (ambient : A) (n : Nat)
    (counter : base source = List.replicate n true) (register : Option Bool) :
    (advance (TM2.step program))^[n + 2]
      (some ⟨some start, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        tapesAt source destination base [] (encodeWord n ++ base destination)⟩ := by
  let pushed := Function.update base destination (false :: base destination)
  have first : (advance (TM2.step program))^[1]
      (some ⟨some start, (ambient, register), base⟩) =
      some ⟨some loop, (ambient, none), pushed⟩ := by
    change some (TM2.stepAux (program start) _ _) = _
    rw [atStart]
    rfl
  have rest := transferAt_fromTapes (Γ := Alphabet) source destination distinct id false
    loop exit program atLoop pushed ambient none
  have sourceWord : pushed source = List.replicate n true := by
    simpa [pushed, distinct] using counter
  simp only [sourceWord, List.length_replicate, List.reverse_replicate,
    List.map_id_fun, id_eq] at rest
  have full := iterate_trans first rest
  simpa [pushed, tapesAt, Function.update_comm distinct, encodeWord,
    List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using full

/-- The actual four-phase routine, with exact unary header and preserved body. -/
theorem headerTrace (variableTape clauses destination : K)
    (vc : variableTape ≠ clauses) (vd : variableTape ≠ destination) (cd : clauses ≠ destination)
    (clauseStart clauseLoop variableStart variableLoop : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atClauseStart : program clauseStart = delimiter destination clauseLoop)
    (atClauseLoop : program clauseLoop =
      loopAt clauses destination id false clauseLoop (some variableStart))
    (atVariableStart : program variableStart = delimiter destination variableLoop)
    (atVariableLoop : program variableLoop =
      loopAt variableTape destination id false variableLoop exit)
    (base : K → List Bool) (ambient : A)
    (n m : Nat) (body : List Bool) (register : Option Bool) :
    (advance (TM2.step program))^[n + m + 4]
      (some ⟨some clauseStart, (ambient, register),
        tapes variableTape clauses destination base
          (List.replicate n true) (List.replicate m true) body⟩) =
      some ⟨exit, (ambient, none),
        tapes variableTape clauses destination base [] [] (encodeWord n ++ encodeWord m ++ body)⟩ := by
  have first := prependTrace clauses destination cd clauseStart clauseLoop (some variableStart)
    program atClauseStart atClauseLoop
    (tapes variableTape clauses destination base
      (List.replicate n true) (List.replicate m true) body)
    ambient m (by simp [tapes, cd]) register
  have second := prependTrace variableTape destination vd variableStart variableLoop exit
    program atVariableStart atVariableLoop
    (tapes variableTape clauses destination base (List.replicate n true) []
      (encodeWord m ++ body))
    ambient n (by simp [tapes, vc, vd]) none
  simp only [tapes, tapesAt] at first second ⊢
  simp only [Function.update_self, Function.update_comm cd.symm,
    Function.update_idem] at first
  have full := iterate_trans first second
  simpa only [Function.update_self, Function.update_comm vd.symm,
    Function.update_comm vc.symm, Function.update_idem, List.append_assoc,
    show m + 2 + (n + 2) = n + m + 4 by omega] using full


end Placement


end UniqueGamesTheorem.BinaryHeaderMachine

end OAI
