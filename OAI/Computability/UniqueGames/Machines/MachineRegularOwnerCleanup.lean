/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Machines.MachineDrainManyLemmas
import OAI.Computability.UniqueGames.Machines.MachineRegularOriginalBody
import OAI.Computability.UniqueGames.Machines.MachineUnaryAffineAt

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup

open Turing MachineComposition

abbrev Tape := MachineRegularOriginalBody.Tape ⊕ Fin 2
abbrev State := MachineRegularOriginalBody.State × Option Bool
abbrev Alphabet (_ : Tape) := Bool

instance tapeDecidableEq : DecidableEq Tape :=
  @instDecidableEqSum _ _
    (@instDecidableEqSum _ _ (inferInstanceAs (DecidableEq (Fin 27)))
      (@instDecidableEqSum _ _ (inferInstanceAs (DecidableEq MachineRegularMetadata.Extra))
        (@instDecidableEqSum _ _
          (@instDecidableEqSum _ _
            (@instDecidableEqSum _ _ (inferInstanceAs (DecidableEq MachineExpanderRow.Tape))
              (inferInstanceAs (DecidableEq MachineExpanderTable.ExtraTape)))
            (inferInstanceAs (DecidableEq MachineExpanderFamily.ExtraTape)))
          (inferInstanceAs (DecidableEq MachineCeilingPower.Tape)))))
    (inferInstanceAs (DecidableEq (Fin 2)))

instance tapeBEq : BEq Tape where
  beq a b := decide (a = b)

instance tapeLawfulBEq : LawfulBEq Tape where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

instance tapeFintype : Fintype Tape := inferInstance

def core (k : Fin 27) : Tape := .inl (.inl k)
def localRank : Tape := core 3
def count : Tape := core 4
def prefixTape : Tape := core 5
def rotor : Tape := core 7
def padding : Tape := .inl (.inr (.inl .padding))
def level : Tape := .inl (.inr (.inl .level))
def dummyFuel : Tape := .inr 0
def scratch : Tape := .inr 1

/-- Every name is distinct, so the exact drain cost uses the entry lengths. -/
def cleanupTapes : List Tape := [localRank, count, rotor, padding, level, dummyFuel]

inductive Label
  | scan
  | restore
  | drain (l : MachineDrainMany.Label cleanupTapes)
  deriving DecidableEq, Fintype

def entry : Label := .scan

variable {Λ : Type}

def cleanupEntry (labels : Label → Λ) (exit : Option Λ) : Option Λ :=
  MachineDrainMany.entry cleanupTapes (fun l => labels (.drain l)) exit

/-- Coefficient one, no seed: the destination already contains its offset. -/
def instruction (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt Alphabet Λ State
  | .scan => MachineUnaryAffineAt.scan padding scratch prefixTape 1
      (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt scratch padding id false
      (labels .restore) (cleanupEntry labels exit)
  | .drain l => MachineDrainMany.instruction cleanupTapes
      (fun l => labels (.drain l)) exit l

def afterAddition (base : Tape → List Bool) (d o : Nat) : Tape → List Bool :=
  Function.update base prefixTape (encodeWord (d + o))

def finalTapes (base : Tape → List Bool) (d o : Nat) : Tape → List Bool :=
  MachineDrainMany.finalTapes cleanupTapes (afterAddition base d o)

def steps (base : Tape → List Bool) (d : Nat) : Nat :=
  2 * (d + 1) + (cleanupTapes.map (fun k => (base k).length + 1)).sum

theorem finalTapes_apply (base : Tape → List Bool) (d o : Nat) (k : Tape) :
    finalTapes base d o k =
      if k ∈ cleanupTapes then []
      else if k = prefixTape then encodeWord (d + o) else base k := by
  simp only [finalTapes, MachineDrainMany.finalTapes_apply, afterAddition,
    Function.update_apply]


theorem drainSteps_eq (base : Tape → List Bool) (d o : Nat) :
    MachineDrainMany.steps cleanupTapes (afterAddition base d o) =
      (cleanupTapes.map (fun k => (base k).length + 1)).sum := by
  simp [MachineDrainMany.steps, cleanupTapes, afterAddition, prefixTape,
    localRank, count, rotor, padding, level, dummyFuel, core]

theorem additionTraceAt (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ State)
    (code : ∀ l, program (labels l) = instruction labels exit l)
    (base : Tape → List Bool) (d o : Nat)
    (paddingWord : base padding = encodeWord d)
    (prefixWord : base prefixTape = encodeWord o)
    (scratchEmpty : base scratch = [])
    (ambient : MachineRegularOriginalBody.State) (register : Option Bool) :
    (advance (TM2.step program))^[2 * (d + 1)]
      (some ⟨some (labels entry), (ambient, register), base⟩) =
      some ⟨cleanupEntry labels exit, (ambient, none), afterAddition base d o⟩ := by
  have frame (word : List Bool) :
      MachineUnaryAffineAt.tapes padding scratch prefixTape base (encodeWord d) [] word =
        Function.update base prefixTape word := by
    rw [← paddingWord, ← scratchEmpty]
    simp only [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, Function.update_eq_self]
  have initial : MachineUnaryAffineAt.tapes padding scratch prefixTape base
      (encodeWord d) [] (encodeWord o) = base := by
    rw [frame, ← prefixWord, Function.update_eq_self]
  have run := MachineUnaryAffineAt.affineTrace padding scratch prefixTape
    (by decide) (by decide) (by decide) 1 (labels .scan) (labels .restore)
    (cleanupEntry labels exit) program (code .scan) (code .restore)
    base d o [] [] ambient register
  simpa only [List.append_nil, Nat.one_mul, initial, frame, entry, afterAddition] using run

/-- Complete physical addition followed by the six exact drain loops.
No phase run or precomputed sum word is supplied as a hypothesis. -/
theorem traceAt (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ State)
    (code : ∀ l, program (labels l) = instruction labels exit l)
    (base : Tape → List Bool) (d o : Nat)
    (paddingWord : base padding = encodeWord d)
    (prefixWord : base prefixTape = encodeWord o)
    (scratchEmpty : base scratch = [])
    (ambient : MachineRegularOriginalBody.State) (register : Option Bool) :
    (advance (TM2.step program))^[steps base d]
      (some ⟨some (labels entry), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), finalTapes base d o⟩ := by
  have first := additionTraceAt labels exit program code base d o
    paddingWord prefixWord scratchEmpty ambient register
  have second := MachineDrainMany.trace cleanupTapes (fun l => labels (.drain l)) exit
    program (fun l => code (.drain l)) (afterAddition base d o) ambient none
  simp only [MachineDrainMany.finalRegister_none, drainSteps_eq] at second
  unfold steps
  rw [Nat.add_comm, Function.iterate_add_apply, first]
  exact second


end UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup

end OAI
