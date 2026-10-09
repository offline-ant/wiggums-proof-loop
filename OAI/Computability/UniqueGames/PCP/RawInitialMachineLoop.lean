/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.PCP.RawInitialMachineBody
import OAI.Computability.UniqueGames.PCP.RawInitialMachineFinish

namespace OAI

section

/-! Exact execution of the clause loop, in the original occurrence order. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoop

open Turing Target Complexity RawInitialMachineModel RawInitialMachineLoopData
open RawInitialMachineBudget RawInitialMachineBody RawInitialMachineFinish

def finalSigns {n : Nat} (incoming : RawInitialMachineModel.Signs) :
    List (Clause n) → RawInitialMachineModel.Signs
  | [] => incoming
  | c :: cs => finalSigns (RawInitialRows.clauseSigns c) cs

theorem empty_loopTapes (n i : Nat) (rev : List Bool) :
    loopTapes n i 0 [] rev = finishTapes n i rev := by
  funext tape
  cases tape <;> rfl

/-- The complete actual loop: every clause is read once, emits six rows, and
leaves clean field tapes before the next guard. The final zero guard is included. -/
theorem loopTrace {n : Nat} (i : Nat) (cs : List (Clause n))
    (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[loopTime i cs]
      (some ⟨some .guard, state, loopTapes n i cs.length (clauseInput cs) rev⟩) =
      some ⟨some (.scan .dummyVariables), (finalSigns state.1 cs, none),
        finishTapes n (i + cs.length) ((encodeWords (clauseOutput n i cs)).reverse ++ rev)⟩ := by
  induction cs generalizing i rev state with
  | nil =>
      have h := RawInitialMachineBody.guardTrace_zero n i [] rev state
      rw [empty_loopTapes] at h
      simpa only [loopTime, List.length_nil, clauseInput_nil, clauseOutput_nil,
        finalSigns, encodeWords, List.reverse_nil, List.nil_append, Nat.add_zero,
        empty_loopTapes] using h
  | cons c cs ih =>
      have first := bodyTrace i cs.length c (clauseInput cs) rev state
      have rest := ih (i + 1)
        ((encodeWords (RawInitialRows.clauseWords n i
          (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c))).reverse ++ rev)
        (RawInitialRows.clauseSigns c, none)
      have total := UniqueGamesTheorem.Foundations.Complexity.MachineComposition.iterate_trans first rest
      have hi : i + 1 + cs.length = i + (cs.length + 1) := by omega
      simpa only [loopTime, List.length_cons, clauseInput_cons, clauseOutput_cons,
        encodeWords_append, List.reverse_append, List.append_assoc, finalSigns, hi] using total


end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoop

end

end OAI
