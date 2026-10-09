/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Machines.FinalCNFLoopLemmas

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

section

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.AlphabetTable

/-- One scaled scan/restore, one bounded offset, the delimiter, and final jump. -/
def emitSteps (n : Nat) : Nat := 3 * (n + 1) + 6

theorem affinePlan_bits {σ : Type} {bound : Nat} (coefficient : Nat)
    (offset : σ → Fin bound) (n : Nat) (ambient : σ) :
    Emitter.prefixBits (affinePlan coefficient offset) (fun _ : Fin 1 => n) ambient 3 =
      encodeWord (coefficient * n + (offset ambient).val) := by
  change Emitter.prefixBits
    (Emitter.listCommands (Emitter.affineCommands [((0 : Fin 1), coefficient)] offset))
    (fun _ : Fin 1 => n) ambient
    (Emitter.affineCommands [((0 : Fin 1), coefficient)] offset).length = _
  rw [Emitter.bits_listCommands, Emitter.affineCommands_bits]
  simp [Emitter.affineValue]

theorem affinePlan_steps {σ : Type} {bound : Nat} (coefficient : Nat)
    (offset : σ → Fin bound) (n : Nat) :
    Emitter.prefixSteps (affinePlan coefficient offset) (fun _ : Fin 1 => n) 3 + 1 =
      emitSteps n := by
  simp [affinePlan, Emitter.prefixSteps, Emitter.commandAt, Emitter.listCommands,
    Emitter.affineCommands, Emitter.commandSteps, emitSteps]

/-- Every tape except the accumulator is literally retained. -/
def emittedWord {K : Type} [DecidableEq K]
    (target : K) (base : K → List Bool) (value : Nat) : K → List Bool :=
  Function.update base target ((encodeWord value).reverse ++ base target)


variable {ρ : Type} [Fintype ρ] {d : Nat}

@[simp] theorem program_firstEmit (positive : 0 < d) (H : Table (cloudSize d) d)
    (label : Emitter.Label 3 (degree d)) :
    program (ρ := ρ) positive H (.firstEmit label) =
      Emitter.statement (firstPlan ρ d) (fun _ : Fin 1 => Tape.inputVertex)
        .emitScratch .queryReverse Label.firstEmit (some Label.firstReverse) label := rfl

@[simp] theorem program_secondEmit (positive : 0 < d) (H : Table (cloudSize d) d)
    (label : Emitter.Label 3 (degree d)) :
    program (ρ := ρ) positive H (.secondEmit label) =
      Emitter.statement (secondPlan ρ d) (fun _ : Fin 1 => Tape.quotientFirst)
        .emitScratch .queryReverse Label.secondEmit (some Label.secondReverse) label := rfl

@[simp] theorem program_outputEmit (positive : 0 < d) (H : Table (cloudSize d) d)
    (label : Emitter.Label 3 (rowFactor d)) :
    program (ρ := ρ) positive H (.outputEmit label) =
      Emitter.statement (outputPlan ρ d) (fun _ : Fin 1 => Tape.quotientSecond)
        .emitScratch .output Label.outputEmit (some (Label.cleanup 0)) label := rfl

section Embedded

variable {K Λ : Type} [DecidableEq K]

/-- The code premise identifies concrete statements in a caller's program;
it does not assume any phase execution. -/
theorem firstEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .inputVertex) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.firstEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels .firstReverse), ((ambient, ()), none),
        emittedWord (ports .queryReverse) base (firstAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.firstEmit l)) =
      Emitter.statement (firstPlan ρ d) (fun _ : Fin 1 => ports .inputVertex)
        (ports .emitScratch) (ports .queryReverse) (fun k => labels (.firstEmit k))
        (some (labels .firstReverse)) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (firstPlan ρ d) (fun _ : Fin 1 => ports .inputVertex)
    (ports .emitScratch) (ports .queryReverse)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.firstEmit k)) (some (labels .firstReverse)) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [firstPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, firstAddress] using run

theorem secondEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .quotientFirst) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.secondEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels .secondReverse), ((ambient, ()), none),
        emittedWord (ports .queryReverse) base (secondAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.secondEmit l)) =
      Emitter.statement (secondPlan ρ d) (fun _ : Fin 1 => ports .quotientFirst)
        (ports .emitScratch) (ports .queryReverse) (fun k => labels (.secondEmit k))
        (some (labels .secondReverse)) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (secondPlan ρ d) (fun _ : Fin 1 => ports .quotientFirst)
    (ports .emitScratch) (ports .queryReverse)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.secondEmit k)) (some (labels .secondReverse)) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [secondPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, secondAddress] using run

theorem outputEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .quotientSecond) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.outputEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels (.cleanup 0)), ((ambient, ()), none),
        emittedWord (ports .output) base (outputAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.outputEmit l)) =
      Emitter.statement (outputPlan ρ d) (fun _ : Fin 1 => ports .quotientSecond)
        (ports .emitScratch) (ports .output) (fun k => labels (.outputEmit k))
        (some (labels (.cleanup 0))) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (outputPlan ρ d) (fun _ : Fin 1 => ports .quotientSecond)
    (ports .emitScratch) (ports .output)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.outputEmit k)) (some (labels (.cleanup 0))) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [outputPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, outputAddress] using run


end Embedded


end

/-!
# Actual lookup and reversal phases of the expander row program

The Boolean phase selector chooses the first or second occurrence of the same
preserving lookup. The selected word is proved to be the actual stored reverse
index of the supplied graph row. All execution facts follow from the concrete
program statements; no phase execution is assumed.
-/

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineComposition

def lookupPhaseLabel {d : Nat} (second : Bool)
    (l : MachinePreservingLookupClean.Label) : Label d :=
  if second then .secondLookup l else .firstLookup l

def scanPhaseLabel {d : Nat} (second : Bool) : Label d :=
  if second then .secondScan else .firstScan

def reversePhaseLabel {d : Nat} (second : Bool) : Label d :=
  if second then .secondReverse else .firstReverse


theorem lookupTape_injective : Function.Injective lookupTape := by decide

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

/-- The exact cleaned tape state produced by either lookup. -/
def lookupResultTapes (ports : Tape → K) (base : K → List Bool)
    (value : Nat) (indexSuffix : List Bool) : K → List Bool :=
  Function.update
    (Function.update (Function.update base (ports .queryIndex) (encodeWord 0 ++ indexSuffix))
      (ports .lookupWork) [])
    (ports .lookupOutput) (encodeWord value ++ base (ports .lookupOutput))


section Lookup

variable {v d : Nat} (second : Bool) (positive : 0 < d)
    (H : Table (cloudSize d) d) (ports : Tape → K)
    (distinct : Function.Injective ports) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (base : K → List Bool) (G : Table v (degree d))
    (tableWord : base (ports .table) = encodeWords (rotationWords G))
    (scratchEmpty : base (ports .lookupRestore) = [])
    (x : Fin v × Fin (degree d)) (indexSuffix : List Bool)
    (counterWord : base (ports .queryIndex) =
      encodeWord (rowIndex v (degree d) x).val ++ indexSuffix)
    (workEmpty : base (ports .lookupWork) = [])
    (ambient : (Ambient ρ d × Fin (degree d)) × Unit) (register : Option Bool)

include positive H distinct exit code tableWord scratchEmpty counterWord workEmpty

/-- Actual first/second lookup execution on a stored graph row. The selected
reverse index is obtained from `rotationWords_getElem?`, not a caller premise. -/
theorem lookupPhaseTrace :
    (advance (TM2.step target))^[MachinePreservingLookupClean.steps
        (rotationWords G) (rowIndex v (degree d) x).val]
      (some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))),
        (ambient, register), base⟩) =
      some ⟨some (labels (scanPhaseLabel second)), (ambient, none),
        lookupResultTapes ports base (reverseIndex G (rowIndex v (degree d) x)).val
          indexSuffix⟩ := by
  apply MachinePreservingLookupClean.traceAt_fromTapes (ports ∘ lookupTape)
    (distinct.comp lookupTape_injective)
    (fun l => labels (lookupPhaseLabel second l)) (some (labels (scanPhaseLabel second)))
    target
  · intro l
    cases second
    · exact code (.firstLookup l)
    · exact code (.secondLookup l)
  · exact tableWord
  · exact scratchEmpty
  · exact rotationWords_getElem? G (rowIndex v (degree d) x)
  · exact counterWord
  · exact workEmpty


end Lookup

variable {d : Nat} (second : Bool) (positive : 0 < d)
    (H : Table (cloudSize d) d) (ports : Tape → K)
    (distinct : Function.Injective ports) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (base : K → List Bool)
    (ambient : (Ambient ρ d × Fin (degree d)) × Unit) (register : Option Bool)

include positive H distinct exit code

/-- The reversal consumes the reverse query word and prepends its forward
encoding to the index tape, retaining every other tape and finite state. -/
theorem reversePhaseTrace :
    (advance (TM2.step target))^[(base (ports .queryReverse)).length + 1]
      (some ⟨some (labels (reversePhaseLabel second)), (ambient, register), base⟩) =
      some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))), (ambient, none),
        Reduction.MachineTransfer.tapesAt (ports .queryReverse) (ports .queryIndex) base []
          ((base (ports .queryReverse)).reverse ++ base (ports .queryIndex))⟩ := by
  have h := Reduction.MachineTransfer.transferAt_fromTapes
    (ports .queryReverse) (ports .queryIndex)
    (fun h => (by decide : Tape.queryReverse ≠ .queryIndex) (distinct h))
    id false (labels (reversePhaseLabel second))
    (some (labels (lookupPhaseLabel second (.run .copyFirst)))) target
    (by cases second <;> exact code _) base ambient register
  unfold Reduction.MachineTransfer.nextAt at h
  unfold advance
  simpa only [List.map_id] using h


/-- Reversing an actual emitted unary field takes exactly `index + 2` steps.
This includes consuming the field's delimiter and leaving the reversal loop. -/
theorem reversePhaseTrace_unary (index : Nat) (suffix : List Bool)
    (queryWord : base (ports .queryReverse) = (encodeWord index).reverse)
    (indexWord : base (ports .queryIndex) = suffix) :
    (advance (TM2.step target))^[index + 2]
      (some ⟨some (labels (reversePhaseLabel second)), (ambient, register), base⟩) =
      some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))), (ambient, none),
        Reduction.MachineTransfer.tapesAt (ports .queryReverse) (ports .queryIndex) base []
          (encodeWord index ++ suffix)⟩ := by
  have h := reversePhaseTrace second positive H ports distinct labels exit target code
    base ambient register
  simpa only [queryWord, indexWord, List.length_reverse, encodeWord_length,
    List.reverse_reverse, Nat.add_assoc] using h

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderRow

end OAI
