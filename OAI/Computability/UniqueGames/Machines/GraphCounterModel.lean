/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Machines.MachineCloudPadding
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.Machines.MachineCopy
import OAI.Computability.UniqueGames.Machines.MachineDrain
import OAI.Computability.UniqueGames.Machines.MachineLogCounter

namespace OAI

/-! A fixed Boolean-stack program prepending the logarithmic round count to
a graph table. It copies the original word, adds its two unary header values,
runs the actual logarithm machine, then emits the counter and original word. -/

namespace UniqueGamesTheorem.Foundations.Complexity.GraphCounterModel

open Turing

inductive ExtraTape where
  | input | archive | scratch | output
  deriving DecidableEq

instance : Fintype ExtraTape where
  elems := {.input, .archive, .scratch, .output}
  complete x := by cases x <;> simp

inductive ExtraLabel where
  | copyFirst | copySecond | seed | headerFirst | headerSecond
  | clearInput | clockCopy | archiveCopy | finalReverse
  deriving DecidableEq

instance : Fintype ExtraLabel where
  elems := {.copyFirst, .copySecond, .seed,
  .headerFirst, .headerSecond, .clearInput, .clockCopy, .archiveCopy, .finalReverse}
  complete x := by cases x <;> simp

abbrev Tape := Fin 3 ⊕ ExtraTape
abbrev Label := Fin 5 ⊕ ExtraLabel
abbrev Alphabet (_ : Tape) := Bool
abbrev State := MachineLogCounter.State × Option Bool

def initialState : State := (MachineLogCounter.initialState, none)

def clockLabel : Option (Fin 5) → Option Label
  | none => some (.inr .clearInput)
  | some l => some (.inl l)

/-- Place the logarithm program on its tapes and preserve the caller register. -/
def clockStatement (q : TM2.Stmt MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State) :
    TM2.Stmt Alphabet Label State :=
  MachineCloudPadding.Placement.statement Sum.inl Sum.inl (some (.inr .clearInput))
    (MachineStateFrame.frameStatement q)

def readHeader (again next : Label) : TM2.Stmt Alphabet Label State :=
  .pop (.inr .input) (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push (.inl 0) (fun _ => true) (.goto fun _ => again))
      (.load (fun state => (state.1, none)) (.goto fun _ => next)))

def program : Label → TM2.Stmt Alphabet Label State
  | .inl l => clockStatement (MachineLogCounter.program l)
  | .inr .copyFirst => Reduction.MachineTransfer.loopAt (.inr .input) (.inr .scratch)
      id false (.inr .copyFirst) (some (.inr .copySecond))
  | .inr .copySecond => MachineCopy.forkLoop (.inr .scratch) (.inr .input) (.inr .archive)
      false (.inr .copySecond) (some (.inr .seed))
  | .inr .seed => .push (.inl 0) (fun _ => false) (.goto fun _ => .inr .headerFirst)
  | .inr .headerFirst => readHeader (.inr .headerFirst) (.inr .headerSecond)
  | .inr .headerSecond => readHeader (.inr .headerSecond) (.inl 0)
  | .inr .clearInput => MachineDrain.drain (.inr .input) (.inr .clearInput)
      (some (.inr .clockCopy))
  | .inr .clockCopy => Reduction.MachineTransfer.loopAt (.inl 2) (.inr .scratch)
      id false (.inr .clockCopy) (some (.inr .archiveCopy))
  | .inr .archiveCopy => Reduction.MachineTransfer.loopAt (.inr .archive) (.inr .scratch)
      id false (.inr .archiveCopy) (some (.inr .finalReverse))
  | .inr .finalReverse => Reduction.MachineTransfer.loopAt (.inr .scratch) (.inr .output)
      id false (.inr .finalReverse) none

def machine : FinTM2 where
  K := Tape
  k₀ := .inr .input
  k₁ := .inr .output
  Γ := Alphabet
  Λ := Label
  main := .inr .copyFirst
  σ := State
  initialState := initialState
  m := program

def clockTapes (tapes : Fin 3 → List Bool) (extra : ExtraTape → List Bool) : Tape → List Bool
  | .inl k => tapes k
  | .inr k => extra k

def clockConfiguration (extra : ExtraTape → List Bool) (register : Option Bool)
    (c : TM2.Cfg MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State) :
    TM2.Cfg Alphabet Label State := ⟨clockLabel c.l, (c.var, register), clockTapes c.stk extra⟩

theorem clockStatement_simulation (extra : ExtraTape → List Bool) (register : Option Bool)
    (statement : TM2.Stmt MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State)
    (state : MachineLogCounter.State) (tapes : Fin 3 → List Bool) :
    TM2.stepAux (clockStatement statement) (state, register) (clockTapes tapes extra) =
      clockConfiguration extra register (TM2.stepAux statement state tapes) := by
  let view : Tape → Option (Fin 3) := Sum.elim some (fun _ => none)
  have tapes_eq (ts : Fin 3 → List Bool) :
      MachineCloudPadding.Placement.tapes view ts (Sum.elim (fun _ => []) extra) =
        clockTapes ts extra := by
    funext k; cases k <;> rfl
  have run := MachineCloudPadding.Placement.stepAux_simulation Sum.inl view
    (fun _ => rfl) (by intro j k h; cases j <;> simp_all [view])
    Sum.inl (some (.inr ExtraLabel.clearInput)) (Sum.elim (fun _ => []) extra)
    (MachineStateFrame.frameStatement statement) (state, register) tapes
  rw [tapes_eq, MachineStateFrame.frame_stepAux] at run
  cases h : (TM2.stepAux statement state tapes).l <;>
    simpa only [clockStatement, MachineCloudPadding.Placement.configuration,
      MachineStateFrame.frameConfiguration, tapes_eq, clockConfiguration,
      MachineCloudPadding.Placement.label, clockLabel, h] using run

theorem clockStep (extra : ExtraTape → List Bool) (register : Option Bool)
    (a b : MachineLogCounter.machine.Cfg)
    (h : MachineLogCounter.machine.step a = some b) :
    TM2.step program (clockConfiguration extra register a) =
      some (clockConfiguration extra register b) := by
  cases a with
  | mk label state tapes =>
      cases label with
      | none => cases h
      | some label =>
          have hb := Option.some.inj h
          subst b
          exact congrArg some (clockStatement_simulation extra register
            (MachineLogCounter.program label) state tapes)

def clockInTime (extra : ExtraTape → List Bool) (register : Option Bool) (n : Nat) :
    StateTransition.EvalsToInTime (TM2.step program)
      (clockConfiguration extra register (initList MachineLogCounter.machine (encodeWord n)))
      (some (clockConfiguration extra register
        (haltList MachineLogCounter.machine (encodeWord (n.log2 + 1))))) (8 * n + 4) :=
  MachineComposition.liftExecutionInTime _ _ (clockConfiguration extra register)
    (clockStep extra register) (MachineLogCounter.outputsInTime n)

end UniqueGamesTheorem.Foundations.Complexity.GraphCounterModel

end OAI
