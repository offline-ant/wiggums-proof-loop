/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Tactic.DeriveFintype
import OAI.Computability.UniqueGames.Machines.MachineDrain
import OAI.Computability.UniqueGames.Machines.MachineLemmas
import OAI.Computability.UniqueGames.Machines.MachineTransducerCopy
import OAI.Computability.UniqueGames.PCP.SourceMachine
import OAI.Computability.UniqueGames.Reduction.CanonicalBodyTemplateLemmas
import OAI.Computability.UniqueGames.Reduction.MachineTransducer

namespace OAI

section

/-!
The literal four-word row used by the hundred-clone finite machine. The
natural-number triple is a fixed program parameter; its bounds and distinctness
are needed only when identifying the output with the typed parity instance.
-/

namespace UniqueGamesTheorem.Explicit.MachineClone100Table

open UniqueGamesTheorem.Reduction

def cloneEquationWords {n : Nat} (e : CloneGap.Equation (Fin n))
    (t : Nat × Nat × Nat) : List Nat :=
  [t.1 + 100 * e.first.val, t.2.1 + 100 * e.second.val,
    t.2.2 + 100 * e.third.val, if e.rhs then 1 else 0]

end UniqueGamesTheorem.Explicit.MachineClone100Table

end

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Model

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad

inductive Tape
  | input | header | counter | field (slot : Fin 4) | scratch | reversed | output
  deriving DecidableEq, Fintype

abbrev Context (D : Nat) := Fin 2 ⊕ (Fin D × Fin 4)
abbrev State (D : Nat) := (Unit × Context D) × Option Bool
abbrev Alphabet (_ : Tape) := Bool

inductive Label (D : Nat)
  | headerStart (slot : Fin 2)
  | headerLoop (slot : Fin 2)
  | setup (context : Context D)
  | scan (context : Context D)
  | emit (context control : Context D) (symbol : Bool)
  | restore (context : Context D)
  | clearHeader
  | guard
  | fieldStart (slot : Fin 4)
  | fieldLoop (slot : Fin 4)
  | cleanup (slot : Fin 4)
  | finalCounter
  | finalReverse
  deriving DecidableEq, Fintype

def defaultControl (D : Nat) : Context D := .inl 0
def initialState (D : Nat) : State D := (((), defaultControl D), none)

def headerTape (j : Fin 2) : Tape := if j.val = 0 then .header else .counter

def contextSource {D : Nat} : Context D → Tape
  | .inl j => headerTape j
  | .inr p => .field p.2

def contextScale {D : Nat} : Context D → Nat
  | .inl j => if j.val = 0 then 100 else D
  | .inr p => if p.2.val < 3 then 100 else 1

def tripleField (t : Nat × Nat × Nat) (j : Fin 4) : Nat :=
  match j.val with
  | 0 => t.1
  | 1 => t.2.1
  | 2 => t.2.2
  | _ => 0

def contextOffset (triples : List (Nat × Nat × Nat)) : Context triples.length → Nat
  | .inl _ => 0
  | .inr p => tripleField (triples.get p.1) p.2

def affineEmit (scale offset : Nat) : Bool → List Bool
  | true => List.replicate scale true
  | false => encodeWord offset

def emission (triples : List (Nat × Nat × Nat)) (c : Context triples.length) :
    Bool → List Bool := affineEmit (contextScale c) (contextOffset triples c)

def contextNext {D : Nat} : Context D → Option (Label D)
  | .inl j => if j.val = 0 then some (.setup (.inl 1)) else some .clearHeader
  | .inr (i, j) =>
      if hj : j.val + 1 < 4 then some (.setup (.inr (i, ⟨j.val + 1, hj⟩)))
      else if hi : i.val + 1 < D then some (.setup (.inr (⟨i.val + 1, hi⟩, 0)))
      else some (.cleanup 0)

def cleanupNext {D : Nat} (j : Fin 4) : Label D :=
  if hj : j.val + 1 < 4 then .cleanup ⟨j.val + 1, hj⟩ else .guard

def program (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ []) :
    Label triples.length → TM2.Stmt Alphabet (Label triples.length) (State triples.length)
  | .headerStart j => SourceMachine.fieldStart (headerTape j) (.headerLoop j)
  | .headerLoop j => SourceMachine.fieldLoop .input (headerTape j) (.headerLoop j)
      (if j.val = 0 then some (.headerStart 1) else some (.setup (.inl 0)))
  | .setup c => .load (fun _ => (((), c), none)) (.goto fun _ => .scan c)
  | .scan c => MachineTransducerCopy.scanLoop (contextSource c) .scratch
      (defaultControl _) (fun q b => .emit c q b) (.restore c)
  | .emit c q b => MachineTransducerCopy.emitter .reversed (fun q _ => q)
      (emission triples) (.scan c) q b
  | .restore c => MachineTransfer.loopAt .scratch (contextSource c) id false
      (.restore c) (contextNext c)
  | .clearHeader => MachineDrain.drain .header .clearHeader (some .guard)
  | .guard => MachineUnaryCounter.guard .counter (.fieldStart 0) .finalCounter
  | .fieldStart j => SourceMachine.fieldStart (.field j) (.fieldLoop j)
  | .fieldLoop j => SourceMachine.fieldLoop .input (.field j) (.fieldLoop j)
      (SourceMachine.fieldNext Label.fieldStart
        (some (.setup (.inr (⟨0, List.length_pos_iff.mpr nonempty⟩, 0)))) j)
  | .cleanup j => MachineDrain.drain (.field j) (.cleanup j) (some (cleanupNext j))
  | .finalCounter => .pop .counter (fun state _ => (state.1, none))
      (.goto fun _ => .finalReverse)
  | .finalReverse => MachineTransfer.loopAt .reversed .output id false .finalReverse none

def machine (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ []) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label triples.length
  main := .headerStart 0
  σ := State triples.length
  initialState := initialState _
  m := program triples nonempty

end UniqueGamesTheorem.Explicit.MachineClone100Model

end

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Affine

open UniqueGamesTheorem.Reduction

open UniqueGamesTheorem.Foundations.Complexity
open MachineClone100Model

/-- Identity control transitions reduce exactly to fixed symbol substitution. -/
theorem output_eq_flatMap {Q : Type} [Fintype Q]
    (emit : Q → Bool → List Bool) (q : Q) (input : List Bool) :
    MachineTransducer.output (fun state _ => state) emit q input =
      input.flatMap (emit q) := by
  induction input with
  | nil => rfl
  | cons b input ih =>
    simp only [MachineTransducer.output, List.flatMap_cons, ih]


theorem affineEmit_replicate_true (scale offset v : Nat) :
    (List.replicate v true).flatMap (affineEmit scale offset) =
      List.replicate (scale * v) true := by
  rw [List.flatMap_replicate]
  change (List.replicate v (List.replicate scale true)).flatten = _
  rw [List.flatten_replicate_replicate, Nat.mul_comm v scale]

/-- This includes zero scale and zero offset, with no positivity assumptions. -/
theorem affineEmit_word (scale offset v : Nat) :
    (encodeWord v).flatMap (affineEmit scale offset) =
      encodeWord (offset + scale * v) := by
  simp only [encodeWord, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, affineEmit_replicate_true, affineEmit]
  rw [← List.append_assoc, List.replicate_append_replicate, Nat.add_comm (scale * v) offset]


/-- Exact symbolic context transform used by the shared clone-table machine. -/
theorem output_word (triples : List (Nat × Nat × Nat))
    (c : Context triples.length) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) c (encodeWord v) =
      encodeWord (contextOffset triples c + contextScale c * v) := by
  rw [output_eq_flatMap]
  exact affineEmit_word (contextScale c) (contextOffset triples c) v


end UniqueGamesTheorem.Explicit.MachineClone100Affine

end

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Cleanup

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineClone100Model

theorem clearHeaderTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (control : Unit × Context triples.length)
    (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[(base .header).length + 1]
      (some ⟨some .clearHeader, (control, register), base⟩) =
      some ⟨some .guard, (control, none), Function.update base .header []⟩ :=
  (MachineDrain.drainInTime Tape.header Label.clearHeader (some Label.guard)
    (program triples nonempty) rfl base control register).evals_in_steps


/-- The four explicit updates made by the successive cleanup labels. -/
def clearFields (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (.field 0) []) (.field 1) []) (.field 2) []) (.field 3) []

@[simp] theorem clearFields_field (base : Tape → List Bool) (j : Fin 4) :
    clearFields base (.field j) = [] := by
  fin_cases j <;> simp [clearFields]


@[simp] theorem clearFields_input (base : Tape → List Bool) :
    clearFields base .input = base .input := by simp [clearFields]
@[simp] theorem clearFields_header (base : Tape → List Bool) :
    clearFields base .header = base .header := by simp [clearFields]
@[simp] theorem clearFields_counter (base : Tape → List Bool) :
    clearFields base .counter = base .counter := by simp [clearFields]
@[simp] theorem clearFields_scratch (base : Tape → List Bool) :
    clearFields base .scratch = base .scratch := by simp [clearFields]
@[simp] theorem clearFields_reversed (base : Tape → List Bool) :
    clearFields base .reversed = base .reversed := by simp [clearFields]
@[simp] theorem clearFields_output (base : Tape → List Bool) :
    clearFields base .output = base .output := by simp [clearFields]


def cleanupSteps (base : Tape → List Bool) : Nat :=
  (base (.field 0)).length + (base (.field 1)).length +
    (base (.field 2)).length + (base (.field 3)).length + 4

theorem cleanupTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (slot : Fin 4) (base : Tape → List Bool)
    (control : Unit × Context triples.length) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[
      (base (.field slot)).length + 1]
      (some ⟨some (.cleanup slot), (control, register), base⟩) =
      some ⟨some (cleanupNext slot), (control, none), Function.update base (.field slot) []⟩ :=
  (MachineDrain.drainInTime (Tape.field slot) (Label.cleanup slot) (some (cleanupNext slot))
    (program triples nonempty) rfl base control register).evals_in_steps

/-- All four field stacks are consumed by the actual cleanup program. -/
theorem cleanupFourTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (control : Unit × Context triples.length)
    (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[cleanupSteps base]
      (some ⟨some (.cleanup 0), (control, register), base⟩) =
      some ⟨some .guard, (control, none), clearFields base⟩ := by
  let t₀ := Function.update base (.field 0) []
  let t₁ := Function.update t₀ (.field 1) []
  let t₂ := Function.update t₁ (.field 2) []
  have h₀ := cleanupTrace triples nonempty 0 base control register
  have h₁ := cleanupTrace triples nonempty 1 t₀ control none
  have h₂ := cleanupTrace triples nonempty 2 t₁ control none
  have h₃ := cleanupTrace triples nonempty 3 t₂ control none
  have combined := MachineComposition.iterate_trans
    (MachineComposition.iterate_trans (MachineComposition.iterate_trans h₀ h₁) h₂) h₃
  convert combined using 1
  · congr 1
    simp [cleanupSteps, t₀, t₁, t₂]
    omega
  · rfl

def cleanupFourInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (base : Tape → List Bool) (control : Unit × Context triples.length)
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some (.cleanup 0), (control, register), base⟩
      (some ⟨some .guard, (control, none), clearFields base⟩)
      (cleanupSteps base) where
  steps := cleanupSteps base
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step (program triples nonempty)))^[_] _ = _
    exact cleanupFourTrace triples nonempty base control register
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Explicit.MachineClone100Cleanup

end

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Context

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineClone100Model

theorem contextSource_ne_scratch {D : Nat} (context : Context D) :
    contextSource context ≠ Tape.scratch := by
  cases context with
  | inl slot =>
    simp only [contextSource, headerTape]
    split <;> simp
  | inr pair => simp [contextSource]

theorem contextSource_ne_reversed {D : Nat} (context : Context D) :
    contextSource context ≠ Tape.reversed := by
  cases context with
  | inl slot =>
    simp only [contextSource, headerTape]
    split <;> simp
  | inr pair => simp [contextSource]

def contextTapes (triples : List (Nat × Nat × Nat)) (context : Context triples.length)
    (base : Tape → List Bool) : Tape → List Bool :=
  Function.update base .reversed
    ((MachineTransducer.output (fun control _ => control) (emission triples)
      context (base (contextSource context))).reverse ++ base .reversed)


theorem contextTapes_other (triples : List (Nat × Nat × Nat))
    (context : Context triples.length) (base : Tape → List Bool) (tape : Tape)
    (different : tape ≠ .reversed) :
    contextTapes triples context base tape = base tape := by
  simp [contextTapes, different]


@[simp] theorem contextTapes_scratch (triples : List (Nat × Nat × Nat))
    (context : Context triples.length) (base : Tape → List Bool) :
    contextTapes triples context base .scratch = base .scratch :=
  contextTapes_other triples context base _ (by decide)

/-- Setup discards arbitrary old control and register values before scanning. -/
theorem setupStep (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (context : Context triples.length) (base : Tape → List Bool)
    (state : State triples.length) :
    TM2.step (program triples nonempty) ⟨some (.setup context), state, base⟩ =
      some ⟨some (.scan context), (((), context), none), base⟩ := rfl

theorem contextTrace (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (context : Context triples.length) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State triples.length) :
    (MachineComposition.advance (TM2.step (program triples nonempty)))^[
        3 * (base (contextSource context)).length + 3]
      (some ⟨some (.setup context), state, base⟩) =
      some ⟨contextNext context, initialState _, contextTapes triples context base⟩ := by
  have copied := MachineTransducerCopy.transduceCopyTrace
    (contextSource context) Tape.scratch Tape.reversed
    (contextSource_ne_scratch context) (contextSource_ne_reversed context) (by decide)
    (defaultControl triples.length) (fun control _ => control) (emission triples)
    (.scan context) (.restore context) (fun control symbol => .emit context control symbol)
    (contextNext context) (program triples nonempty)
    rfl (by intros; rfl) rfl base scratchEmpty () context none
  rw [show 3 * (base (contextSource context)).length + 3 =
      (3 * (base (contextSource context)).length + 2) + 1 by omega,
    Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step (program triples nonempty)))^[
    3 * (base (contextSource context)).length + 2]
    (TM2.step (program triples nonempty) ⟨some (.setup context), state, base⟩) = _
  rw [setupStep]
  exact copied

/-- The exact trace packaged for composition with neighboring cloning stages. -/
def contextInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (context : Context triples.length) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State triples.length) :
    StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some (.setup context), state, base⟩
      (some ⟨contextNext context, initialState _, contextTapes triples context base⟩)
      (3 * (base (contextSource context)).length + 3) where
  steps := 3 * (base (contextSource context)).length + 3
  evals_in_steps := contextTrace triples nonempty context base scratchEmpty state
  steps_le_m := Nat.le_refl _

@[simp] theorem contextInTime_steps (triples : List (Nat × Nat × Nat))
    (nonempty : triples ≠ []) (context : Context triples.length) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State triples.length) :
    (contextInTime triples nonempty context base scratchEmpty state).steps =
      3 * (base (contextSource context)).length + 3 := rfl

end UniqueGamesTheorem.Explicit.MachineClone100Context

end

section

namespace UniqueGamesTheorem.Explicit.MachineClone100Finish

open UniqueGamesTheorem.Reduction

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineClone100Model

def finishTapes (base : Tape → List Bool) : Tape → List Bool :=
  MachineTransfer.tapesAt .reversed .output (Function.update base .counter []) []
    ((base .reversed).reverse ++ base .output)


theorem counterStep (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (hcounter : base .counter = [false]) :
    TM2.step (program triples hne)
      ⟨some .finalCounter, initialState _, base⟩ =
        some ⟨some .finalReverse, initialState _, Function.update base .counter []⟩ := by
  simp [TM2.step, TM2.stepAux, program, initialState, hcounter]

theorem finishTrace (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (hcounter : base .counter = [false]) :
    (MachineComposition.advance (TM2.step (program triples hne)))^[(base .reversed).length + 2]
      (some ⟨some .finalCounter, initialState _, base⟩) =
        some ⟨none, initialState _, finishTapes base⟩ := by
  have first := counterStep triples hne base hcounter
  have rest := MachineTransfer.transferAt_fromTapes Tape.reversed Tape.output
    (by decide) id false (Label.finalReverse : Label triples.length) none
    (program triples hne) rfl (Function.update base Tape.counter [])
    ((), defaultControl triples.length) none
  change (MachineComposition.advance (TM2.step (program triples hne)))^[
      ((Function.update base Tape.counter []) Tape.reversed).length + 1]
    (some ⟨some .finalReverse, initialState _, Function.update base .counter []⟩) = _ at rest
  have rest' :
      (MachineComposition.advance (TM2.step (program triples hne)))^[(base .reversed).length + 1]
        (some ⟨some .finalReverse, initialState _, Function.update base .counter []⟩) =
          some ⟨none, initialState _, finishTapes base⟩ := by
    simpa only [finishTapes, initialState,
      Function.update_of_ne (by decide : Tape.reversed ≠ Tape.counter),
      Function.update_of_ne (by decide : Tape.output ≠ Tape.counter), List.map_id] using rest
  rw [show (base .reversed).length + 2 = ((base .reversed).length + 1) + 1 by omega,
    Function.iterate_succ_apply, MachineComposition.advance_some, first]
  exact rest'

def finishInTime (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (hcounter : base .counter = [false]) :
    StateTransition.EvalsToInTime (TM2.step (program triples hne))
      ⟨some .finalCounter, initialState _, base⟩
      (some ⟨none, initialState _, finishTapes base⟩) ((base .reversed).length + 2) where
  steps := (base .reversed).length + 2
  evals_in_steps := finishTrace triples hne base hcounter
  steps_le_m := Nat.le_refl _

theorem finish_eq_haltList (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool)
    (emptyOther : ∀ tape, tape ≠ .counter → tape ≠ .reversed → base tape = []) :
    (⟨none, initialState _, finishTapes base⟩ : (machine triples hne).Cfg) =
      haltList (machine triples hne) ((base .reversed).reverse) := by
  have hout := emptyOther .output (by decide) (by decide)
  have ht : finishTapes base =
      (haltList (machine triples hne) ((base .reversed).reverse)).stk := by
    funext tape
    cases tape <;> simp [finishTapes, MachineTransfer.tapesAt, haltList, machine, hout,
      emptyOther]
    rfl
  exact congrArg
    (fun tapes => (⟨none, initialState triples.length, tapes⟩ : (machine triples hne).Cfg)) ht

end UniqueGamesTheorem.Explicit.MachineClone100Finish

end

end OAI
