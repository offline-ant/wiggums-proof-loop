/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Research.R22MachinesRegular
import OAI.Computability.UniqueGames.Machines.MachineRegularOriginalRow

namespace OAI

/-!
# Reusable inherited-row execution with actual cleanup

Five concrete drain loops remove the query delimiter, unread scan suffix,
raw reverse field, computed reverse field, and copied relation. With initially
empty work tapes, the only final tape change is the appended output row. The
index on tape zero and input table on tape one are both preserved.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalClean

open Turing MachineComposition PCP PCP.GraphTables PCP.PreprocessingRegularTables

abbrev Tape := MachineRegularOriginalRow.Tape
abbrev Alphabet := MachineRegularOriginalRow.Alphabet
abbrev State := MachineRegularOriginalRow.State

inductive Label
  | row (label : MachineRegularOriginalRow.Label)
  | query | scan | rawReverse | computedReverse | relation
  deriving DecidableEq, Fintype

def instruction {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt Alphabet Λ (State σ)
  | .row l => MachineRegularOriginalRow.instruction q (fun l => labels (.row l))
      (some (labels .query)) l
  | .query => MachineDrain.drain 2 (labels .query) (some (labels .scan))
  | .scan => MachineDrain.drain 3 (labels .scan) (some (labels .rawReverse))
  | .rawReverse => MachineDrain.drain 4 (labels .rawReverse) (some (labels .computedReverse))
  | .computedReverse => MachineDrain.drain 6 (labels .computedReverse) (some (labels .relation))
  | .relation => MachineDrain.drain 7 (labels .relation) exit

def cleanupTapes (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update base 2 []) 3 []) 4 []) 6 []) 7 []

def cleanupSteps (base : Tape → List Bool) : Nat :=
  ((base 2).length + 1) + ((base 3).length + 1) + ((base 4).length + 1) +
    ((base 6).length + 1) + ((base 7).length + 1)

theorem cleanupTraceAt {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (base : Tape → List Bool) (state : State σ) :
    (advance (TM2.step program))^[cleanupSteps base]
      (some ⟨some (labels .query), state, base⟩) =
      some ⟨exit, (state.1, none), cleanupTapes base⟩ := by
  let chosen : List Tape := [2, 3, 4, 6, 7]
  let drainLabels := fun l : MachineDrainMany.Label chosen =>
    labels (![Label.query, .scan, .rawReverse, .computedReverse, .relation]
      (MachineDrainMany.labelIndex chosen l))
  have run := MachineDrainMany.trace chosen drainLabels exit program
    (by
      intro l
      rcases l with (_ | _ | _ | _ | _ | l)
      all_goals first | exact nomatch l | exact code _)
    base state.1 state.2
  simpa [MachineDrainMany.steps, MachineDrainMany.finalTapes, MachineDrainMany.entry,
    MachineFiniteSequence.entry, MachineDrainMany.labelIndex, chosen, drainLabels,
    MachineDrainMany.finalRegister, cleanupSteps, cleanupTapes, Nat.add_assoc] using run

structure Input (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Prop
    extends MachineRegularOriginalRow.Input t e base where
  queryEmpty : base 2 = []
  scanEmpty : base 3 = []

/-- One complete stack invariant serves both cleanup correctness and its cost. -/
theorem rowFinalTapes (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    MachineRegularOriginalRow.finalTapes q t e base =
      ![base 0, base 1, encodeWord 0,
        encodeWords (MachineRegularOriginalRow.suffixWords t e),
        encodeWord t.rows[e].reverseIndex.val, base 5,
        encodeWord ((q + 1) * t.rows[e].reverseIndex.val + q),
        encodeWords (relationWords t.rows[e].relation), base 8,
        base 9 ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e)] := by
  funext k
  fin_cases k <;>
    simp [MachineRegularOriginalRow.finalTapes, MachineRegularOriginalRow.affined,
      MachineRegularOriginalRow.copied, MachineRegularOriginalRow.looked,
      MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes, MachineLookup.tapes,
      MachineRegularOriginalRow.lookupTape, input.queryEmpty, input.scanEmpty,
      input.reverseEmpty, input.computedEmpty, input.relationEmpty]

theorem cleanup_frame (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    cleanupTapes (MachineRegularOriginalRow.finalTapes q t e base) =
      Function.update base 9
        (base 9 ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e)) := by
  rw [rowFinalTapes q t e base input]
  funext k
  fin_cases k <;> simp [cleanupTapes, input.queryEmpty, input.scanEmpty,
    input.reverseEmpty, input.computedEmpty, input.relationEmpty]

theorem suffix_length_le (t : Table) (e : Fin t.darts) :
    (encodeWords (MachineRegularOriginalRow.suffixWords t e)).length ≤ (tableBits t).length := by
  have hlength : (tableBits t).length =
      (encodeWords (MachineRegularOriginalRow.prefixWords t e)).length +
        ((encodeWords (rowWords t.rows[e])).length +
          (encodeWords (MachineRegularOriginalRow.suffixWords t e)).length) := by
    rw [tableBits, MachineRegularOriginalRow.tableWords_at_row,
      encodeWords_append, encodeWords_append, List.length_append, List.length_append]
  omega

theorem cleanupSteps_eq (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    cleanupSteps (MachineRegularOriginalRow.finalTapes q t e base) =
      (encodeWords (MachineRegularOriginalRow.suffixWords t e)).length +
        (q + 2) * t.rows[e].reverseIndex.val + q +
          (encodeWords (relationWords t.rows[e].relation)).length + 8 := by
  rw [rowFinalTapes q t e base input]
  simp [cleanupSteps, encodeWord_length]
  ring

theorem cleanupSteps_le (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    cleanupSteps (MachineRegularOriginalRow.finalTapes q t e base) ≤
      (q + 3) * (tableBits t).length + q + 8200 := by
  rw [cleanupSteps_eq q t e base input]
  have hsuffix := suffix_length_le t e
  have htable := tableWords_length_le_bits t
  have hr : t.rows[e].reverseIndex.val ≤ (tableBits t).length := by
    have hrlt := t.rows[e].reverseIndex.isLt
    omega
  have hmul := Nat.mul_le_mul_left (q + 2) hr
  have hrel := relationBits_length_le t.rows[e].relation
  nlinarith

def steps (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Nat :=
  MachineRegularOriginalRow.steps q t e base +
    cleanupSteps (MachineRegularOriginalRow.finalTapes q t e base)

def timeBound {R : Type*} [Semiring R] (q inputLength outputLength : R) : R :=
  (5 * q + 20) * inputLength + 2 * outputLength + 5 * q + 40995

theorem steps_le (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    steps q t e base ≤ timeBound q (tableBits t).length (base 9).length := by
  have hrow := MachineRegularOriginalRow.steps_le q t e base
  have hclean := cleanupSteps_le q t e base input
  unfold steps timeBound MachineRegularOriginalRow.timeBound at *
  nlinarith

theorem traceAt {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (input : Input t e base)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps q t e base]
      (some ⟨some (labels (.row (.lookup .seed))),
        ((ambient, MachineRegularOriginalRow.zeroBuffer), register), base⟩) =
      some ⟨exit, ((ambient, MachineRegularOriginalRow.zeroBuffer), none),
        Function.update base 9
          (base 9 ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e))⟩ := by
  have row := MachineRegularOriginalRow.traceAt q (fun l => labels (.row l))
    (some (labels .query)) program (fun l => code (.row l)) t e base input.toInput ambient register
  have clean := cleanupTraceAt q labels exit program code
    (MachineRegularOriginalRow.finalTapes q t e base)
    ((ambient, MachineRegularOriginalRow.zeroBuffer), none)
  rw [cleanup_frame q t e base input] at clean
  exact UniqueGamesTheorem.Foundations.Complexity.MachineComposition.iterate_trans row clean

def machine (q : Nat) : FinTM2 where
  K := Tape
  k₀ := 1
  k₁ := 9
  Γ := Alphabet
  Λ := Label
  main := .row (.lookup .seed)
  σ := State Unit
  initialState := (((), MachineRegularOriginalRow.zeroBuffer), none)
  m := instruction q id none


end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOriginalClean

end OAI
