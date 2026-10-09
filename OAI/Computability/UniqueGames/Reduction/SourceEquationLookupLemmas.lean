/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Machines.MachineDrain
import OAI.Computability.UniqueGames.Machines.MachineCloudPadding
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.PCP.SourceFieldArrayLemmas
import OAI.Computability.UniqueGames.Reduction.CanonicalBodyTemplateLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.SourceEquationLookup

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open MachineComposition SourceMachine SourceEncoding
open SourceClauseLookup (discardFieldsTrace)

inductive Tape
  | source | index | work | scratch | field (slot : Fin 4)
  deriving DecidableEq, Fintype

inductive Label
  | copyOut | copyBack | headerFirst | headerSecond | guard
  | skip (slot : Fin 4)
  | read (slot : Fin 5 × Bool)
  deriving DecidableEq, Fintype

def fieldDestination (r : Nat) : Tape := .field ⟨min r 3, by omega⟩
def readStart (r : Nat) : Label := .read (SourceFieldArray.boundedIndex 4 r, false)
def readLoop (r : Nat) : Label := .read (SourceFieldArray.boundedIndex 4 r, true)
def skipLabel (r : Nat) : Label := if h : r < 4 then .skip ⟨r, h⟩ else .guard
def headerLabel (r : Nat) : Label :=
  if r = 0 then .headerFirst else if r = 1 then .headerSecond else .guard

variable {σ : Type}

/-- Eight binary stacks and fixed finite control. Every loop scans one actual bit
or tests one actual counter bit. The arbitrary ambient state is preserved. -/
def program : Label → TM2.Stmt (fun _ : Tape => Bool) Label (σ × Option Bool)
  | .copyOut => Reduction.MachineTransfer.loopAt .source .scratch id false
      .copyOut (some .copyBack)
  | .copyBack => MachineCopy.forkLoop .scratch .source .work false
      .copyBack (some .headerFirst)
  | .headerFirst => MachineLookup.discard .work .headerFirst .headerSecond
  | .headerSecond => MachineLookup.discard .work .headerSecond .guard
  | .guard => MachineUnaryCounter.guard .index (skipLabel 0) (readStart 0)
  | .skip slot => MachineLookup.discard .work (.skip slot) (skipLabel (slot.val + 1))
  | .read slot =>
      if slot.1.val < 4 then
        if slot.2 then
          fieldLoop .work (fieldDestination slot.1.val) (.read (slot.1, true))
            (some (readStart (slot.1.val + 1)))
        else fieldStart (fieldDestination slot.1.val) (.read (slot.1, true))
      else SourceFieldArray.finish .work none

theorem atSkip (r : Nat) (hr : r < 4) :
    program (σ := σ) (skipLabel r) = MachineLookup.discard .work (skipLabel r) (skipLabel (r + 1)) := by
  simp [skipLabel, hr, program]

theorem atReadStart (r : Nat) (hr : r < 4) :
    program (σ := σ) (readStart r) = fieldStart (fieldDestination r) (readLoop r) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadLoop (r : Nat) (hr : r < 4) :
    program (σ := σ) (readLoop r) = fieldLoop .work (fieldDestination r) (readLoop r)
      (some (readStart (r + 1))) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadDone : program (σ := σ) (readStart 4) = SourceFieldArray.finish .work none := by
  simp [program, readStart, SourceFieldArray.boundedIndex]

/-- The two header fields are physically consumed from the work copy. -/
theorem discardHeadersTrace (base : Tape → List Bool) (variableCount equations : Nat)
    (suffix : List Bool) (hinput : base .work = encodeWords [variableCount, equations] ++ suffix) (ambient : σ) :
    (advance (TM2.step program))^[variableCount + equations + 2]
      (some ⟨some .headerFirst, (ambient, none), base⟩) =
      some ⟨some .guard, (ambient, none), Function.update base .work suffix⟩ := by
  have ht := discardFieldsTrace .work headerLabel program base 0 [variableCount, equations]
    suffix (by
      intro r hr
      have he : r = 0 ∨ r = 1 := by simp at hr; omega
      rcases he with rfl | rfl <;> rfl) hinput ambient
  simpa [encodeWords_length, headerLabel] using ht

/-- The fixed skip body consumes four complete unary fields and returns to the
same counter guard, preserving the counter and every other tape. -/
theorem discardFourTrace (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 4) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) (ambient : σ) :
    (advance (TM2.step program))^[(encodeWords values).length]
      (some ⟨some (skipLabel 0), (ambient, none), base⟩) =
      some ⟨some .guard, (ambient, none), Function.update base .work suffix⟩ := by
  have ht := discardFieldsTrace .work skipLabel program base 0 values suffix
    (by intro r hr; simpa only [Nat.zero_add] using atSkip r (by omega)) hinput ambient
  simpa [hlen, skipLabel] using ht

/-- Read the selected four fields using the already checked scanner. -/
theorem readFourTrace (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 4) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) (ambient : σ) :
    (advance (TM2.step program))^[(encodeWords values).length + 5]
      (some ⟨some (readStart 0), (ambient, none), base⟩) =
      some ⟨none, (ambient, none),
        SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix⟩ := by
  have ht := SourceFieldArray.sequenceTrace .work fieldDestination readStart readLoop none
    program base 0 values suffix (by intro r hr; simp [fieldDestination])
    (by intro r hr; simpa only [Nat.zero_add] using atReadStart r (by omega))
    (by intro r hr; simpa only [Nat.zero_add] using atReadLoop r (by omega))
    (by simpa [hlen] using atReadDone) hinput ambient none
  have htime : values.sum + 2 * values.length + 1 = (encodeWords values).length + 5 := by
    rw [encodeWords_length, hlen]
  simpa only [Nat.zero_add, htime] using ht

/-- Normal form for the changing counter and consumed work-copy prefix. -/
def scanTapes (base : Tape → List Bool) (index : Nat)
    (indexSuffix input : List Bool) : Tape → List Bool :=
  MachineUnaryCounter.counterTapes .index (Function.update base .work input) index indexSuffix

@[simp] theorem scanTapes_work (base : Tape → List Bool) (i : Nat)
    (indexSuffix input : List Bool) : scanTapes base i indexSuffix input .work = input := by
  simp [scanTapes, MachineUnaryCounter.counterTapes]

@[simp] theorem scanTapes_index (base : Tape → List Bool) (i : Nat)
    (indexSuffix input : List Bool) :
    scanTapes base i indexSuffix input .index = encodeWord i ++ indexSuffix := by
  simp [scanTapes, MachineUnaryCounter.counterTapes]

theorem scanTapes_other (base : Tape → List Bool) (i : Nat)
    (indexSuffix input : List Bool) (p : Tape) (hi : p ≠ .index) (hw : p ≠ .work) :
    scanTapes base i indexSuffix input p = base p := by
  simp [scanTapes, MachineUnaryCounter.counterTapes, hi, hw]

theorem update_scanTapes_work (base : Tape → List Bool) (i : Nat)
    (indexSuffix input replacement : List Bool) :
    Function.update (scanTapes base i indexSuffix input) .work replacement =
      scanTapes base i indexSuffix replacement := by
  funext p
  cases p <;> simp [scanTapes, MachineUnaryCounter.counterTapes]

/-- Each equation-index bit causes one genuine guard transition and exactly four
field-discard loops. The final zero guard enters the field reader. -/
theorem skipEquationsTrace {n : Nat} (base : Tape → List Bool)
    (prior : List (CloneGap.Equation (Fin n))) (indexSuffix suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[(encodeWords (prior.flatMap equationWords)).length + prior.length + 1]
      (some ⟨some .guard, (ambient, register), scanTapes base prior.length indexSuffix
        (encodeWords (prior.flatMap equationWords) ++ suffix)⟩) =
      some ⟨some (readStart 0), (ambient, none), scanTapes base 0 indexSuffix suffix⟩ := by
  induction prior generalizing register with
  | nil =>
    simpa only [List.flatMap_nil, List.length_nil, encodeWords, List.nil_append,
      Nat.zero_add, Function.iterate_one, advance_some, scanTapes] using
      MachineUnaryCounter.guardStep_zero .index .guard (skipLabel 0) (readStart 0)
        program rfl (Function.update base .work suffix) indexSuffix ambient register
  | cons equation prior ih =>
    have hencoding : encodeWords ((equation :: prior).flatMap equationWords) ++ suffix =
        encodeWords (equationWords equation) ++ (encodeWords (prior.flatMap equationWords) ++ suffix) := by
      simp only [List.flatMap_cons, encodeWords_append, List.append_assoc]
    have htime : (encodeWords ((equation :: prior).flatMap equationWords)).length +
        (equation :: prior).length + 1 =
        ((encodeWords (prior.flatMap equationWords)).length + prior.length + 1 +
          (encodeWords (equationWords equation)).length) + 1 := by
      simp only [List.flatMap_cons, encodeWords_append, List.length_append, List.length_cons]
      omega
    rw [htime, Function.iterate_succ_apply]
    change (advance (TM2.step program))^[
      (encodeWords (prior.flatMap equationWords)).length + prior.length + 1 +
        (encodeWords (equationWords equation)).length]
      (TM2.step program ⟨some .guard, (ambient, register),
        MachineUnaryCounter.counterTapes .index
          (Function.update base .work (encodeWords ((equation :: prior).flatMap equationWords) ++ suffix))
          (prior.length + 1) indexSuffix⟩) = _
    rw [MachineUnaryCounter.guardStep_succ .index .guard (skipLabel 0) (readStart 0)
      program rfl]
    rw [Function.iterate_add_apply]
    have hd := discardFourTrace
      (scanTapes base prior.length indexSuffix
        (encodeWords ((equation :: prior).flatMap equationWords) ++ suffix))
      (equationWords equation) (equationWords_length equation)
      (encodeWords (prior.flatMap equationWords) ++ suffix) (by
        rw [scanTapes_work, hencoding]) ambient
    change (advance (TM2.step program))^[
      (encodeWords (prior.flatMap equationWords)).length + prior.length + 1]
      ((advance (TM2.step program))^[(encodeWords (equationWords equation)).length]
        (some ⟨some (skipLabel 0), (ambient, none), scanTapes base prior.length indexSuffix
          (encodeWords ((equation :: prior).flatMap equationWords) ++ suffix)⟩)) = _
    rw [hd, update_scanTapes_work]
    exact ih none

theorem fieldDestination_eq (j : Fin 4) : fieldDestination j.val = .field j := by
  unfold fieldDestination
  congr 1
  apply Fin.ext
  exact Nat.min_eq_left (by omega)

theorem fieldDestination_injective_below (r s : Nat) (hr : r < 4) (hs : s < 4)
    (he : fieldDestination r = fieldDestination s) : r = s := by
  have hv := congrArg (fun t : Tape => match t with | .field j => j.val | _ => 4) he
  simpa [fieldDestination, Nat.min_eq_left (show r ≤ 3 by omega),
    Nat.min_eq_left (show s ≤ 3 by omega)] using hv

theorem readFour_output_field (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 4) (suffix : List Bool) (j : Fin 4) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix (.field j) =
      encodeWord (values[j.val]'(by omega)) ++ base (.field j) := by
  have ht := SourceFieldArray.sequenceTapes_selected .work fieldDestination base 0 values
    suffix j.val (by omega) (by intro r hr; simp [fieldDestination])
    (by
      intro r s hr hs he
      apply fieldDestination_injective_below r s (by omega) (by omega)
      simpa only [Nat.zero_add] using he)
  simpa only [Nat.zero_add, fieldDestination_eq] using ht

theorem readFour_output_work (base : Tape → List Bool) (values : List Nat)
    (_hlen : values.length = 4) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix .work = suffix := by
  apply SourceFieldArray.sequenceTapes_source _ _ _ _ _ _ _ hinput
  intro r hr
  simp [fieldDestination]

theorem readFour_output_frame (base : Tape → List Bool) (values : List Nat)
    (suffix : List Bool) (p : Tape) (hwork : p ≠ .work)
    (hfield : ∀ j : Fin 4, p ≠ .field j) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix p = base p := by
  apply SourceFieldArray.sequenceTapes_other _ _ _ hwork
  intro r hr
  exact hfield _

/-- Exact lookup frame, independent of the scanner's recursive tape updates. -/
def outputTapes {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) : Tape → List Bool
  | .index => encodeWord 0 ++ indexSuffix
  | .work => suffix
  | .field j => encodeWord ((equationWords equation)[j.val]'(by simp)) ++ base (.field j)
  | p => base p

private theorem readTapes_eq_output {n : Nat} (base : Tape → List Bool)
    (equation : CloneGap.Equation (Fin n)) (indexSuffix suffix : List Bool) :
    SourceFieldArray.sequenceTapes .work fieldDestination
      (scanTapes base 0 indexSuffix (encodeWords (equationWords equation) ++ suffix))
      0 (equationWords equation) suffix = outputTapes base equation indexSuffix suffix := by
  funext p
  cases p with
  | work => exact readFour_output_work _ _ (equationWords_length equation) _ (by simp)
  | field j => simp [readFour_output_field _ _ (equationWords_length equation), outputTapes,
      scanTapes_other _ _ _ _ (.field j) (by simp) (by simp)]
  | index => rw [readFour_output_frame _ _ _ .index (by decide) (by intro j; simp)]
             exact scanTapes_index _ _ _ _
  | source => rw [readFour_output_frame _ _ _ .source (by decide) (by intro j; simp)]
              exact scanTapes_other _ _ _ _ _ (by decide) (by decide)
  | scratch => rw [readFour_output_frame _ _ _ .scratch (by decide) (by intro j; simp)]
               exact scanTapes_other _ _ _ _ _ (by decide) (by decide)

def scanSteps {n : Nat} (variableCount declaredEquations : Nat)
    (prior : List (CloneGap.Equation (Fin n))) (equation : CloneGap.Equation (Fin n)) : Nat :=
  variableCount + declaredEquations + 2 +
    (encodeWords (prior.flatMap equationWords)).length + prior.length + 1 +
    (encodeWords (equationWords equation)).length + 5

theorem scanReadTrace {n : Nat} (base : Tape → List Bool) (variableCount declaredEquations : Nat)
    (prior : List (CloneGap.Equation (Fin n))) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[scanSteps variableCount declaredEquations prior equation]
      (some ⟨some .headerFirst, (ambient, none), scanTapes base prior.length indexSuffix
        (encodeWords [variableCount, declaredEquations] ++
          (encodeWords (prior.flatMap equationWords) ++
            (encodeWords (equationWords equation) ++ suffix)))⟩) =
      some ⟨none, (ambient, none), outputTapes base equation indexSuffix suffix⟩ := by
  have hh := discardHeadersTrace
    (scanTapes base prior.length indexSuffix
      (encodeWords [variableCount, declaredEquations] ++
        (encodeWords (prior.flatMap equationWords) ++ (encodeWords (equationWords equation) ++ suffix))))
    variableCount declaredEquations
    (encodeWords (prior.flatMap equationWords) ++ (encodeWords (equationWords equation) ++ suffix))
    (by simp) ambient
  have hs := skipEquationsTrace base prior indexSuffix (encodeWords (equationWords equation) ++ suffix) ambient none
  have hr := readFourTrace
    (scanTapes base 0 indexSuffix (encodeWords (equationWords equation) ++ suffix))
    (equationWords equation) (equationWords_length equation) suffix (by simp) ambient
  rw [show scanSteps variableCount declaredEquations prior equation =
      ((encodeWords (equationWords equation)).length + 5 +
        ((encodeWords (prior.flatMap equationWords)).length + prior.length + 1)) +
        (variableCount + declaredEquations + 2) by unfold scanSteps; omega]
  rw [Function.iterate_add_apply, hh, update_scanTapes_work,
    Function.iterate_add_apply, hs]
  simpa only [readTapes_eq_output] using hr

def lookupSteps {n : Nat} (F : SourceEncoding.Input) (prior : List (CloneGap.Equation (Fin n)))
    (equation : CloneGap.Equation (Fin n)) : Nat :=
  2 * ((inputBits F).length + 1) + scanSteps F.variables F.equations.length prior equation

theorem lookupWithSplitTrace (F : SourceEncoding.Input) (prior : List (CloneGap.Equation (Fin F.variables)))
    (equation : CloneGap.Equation (Fin F.variables)) (after : List (CloneGap.Equation (Fin F.variables)))
    (hsplit : F.equations = prior ++ equation :: after)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hsource : base .source = inputBits F)
    (hindex : base .index = encodeWord prior.length ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[lookupSteps F prior equation]
      (some ⟨some .copyOut, (ambient, register), base⟩) =
      some ⟨none, (ambient, none),
        outputTapes base equation indexSuffix (encodeWords (after.flatMap equationWords))⟩ := by
  have hbits : inputBits F = encodeWords [F.variables, F.equations.length] ++
      (encodeWords (prior.flatMap equationWords) ++
        (encodeWords (equationWords equation) ++ encodeWords (after.flatMap equationWords))) := by
    simp only [inputBits, inputWords, encodeWords_append]
    rw [hsplit]
    simp only [List.flatMap_append, List.flatMap_cons, encodeWords_append]
  have hc := MachineCopy.copyTrace .source .work .scratch (by decide) (by decide)
    (by decide) false .copyOut .copyBack (some .headerFirst) program rfl rfl
    base hscratch ambient register
  have htapes : Function.update base .work (base .source ++ base .work) =
      scanTapes base prior.length indexSuffix (inputBits F) := by
    funext p
    cases p <;> simp [scanTapes, MachineUnaryCounter.counterTapes, hsource, hindex, hwork]
  rw [htapes, hsource] at hc
  rw [lookupSteps, Nat.add_comm, Function.iterate_add_apply, hc, hbits]
  exact scanReadTrace base F.variables F.equations.length prior equation indexSuffix
    (encodeWords (after.flatMap equationWords)) ambient

theorem output_source {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) :
    outputTapes base equation indexSuffix suffix .source = base .source := rfl

theorem output_index {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) :
    outputTapes base equation indexSuffix suffix .index = encodeWord 0 ++ indexSuffix := rfl

theorem output_work {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) :
    outputTapes base equation indexSuffix suffix .work = suffix := rfl

theorem output_field {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) (j : Fin 4) :
    outputTapes base equation indexSuffix suffix (.field j) =
      encodeWord ((equationWords equation)[j.val]'(by simp)) ++ base (.field j) := rfl


theorem output_rhs {n : Nat} (base : Tape → List Bool)
    (equation : CloneGap.Equation (Fin n)) (indexSuffix suffix : List Bool) :
    outputTapes base equation indexSuffix suffix (.field 3) =
      encodeWord (if equation.rhs then 1 else 0) ++ base (.field 3) := by
  simpa [equationWords] using output_field base equation indexSuffix suffix (3 : Fin 4)

theorem output_frame {n : Nat} (base : Tape → List Bool) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) (p : Tape) (hindex : p ≠ .index) (hwork : p ≠ .work)
    (hfield : ∀ j : Fin 4, p ≠ .field j) :
    outputTapes base equation indexSuffix suffix p = base p := by
  cases p <;> simp_all [outputTapes]


theorem lookupSteps_le_input (F : SourceEncoding.Input) (prior : List (CloneGap.Equation (Fin F.variables)))
    (equation : CloneGap.Equation (Fin F.variables)) (after : List (CloneGap.Equation (Fin F.variables)))
    (hsplit : F.equations = prior ++ equation :: after) :
    lookupSteps F prior equation ≤ 4 * (inputBits F).length + 8 := by
  have hlength : (inputBits F).length = F.variables + F.equations.length + 2 +
      (encodeWords (prior.flatMap equationWords)).length +
      (encodeWords (equationWords equation)).length +
      (encodeWords (after.flatMap equationWords)).length := by
    simp only [inputBits, inputWords, encodeWords_append, List.length_append,
      encodeWords, encodeWord_length, List.length_nil]
    rw [hsplit]
    simp only [List.flatMap_append, List.flatMap_cons, encodeWords_append, List.length_append]
    omega
  have hp : prior.length ≤ F.equations.length := by
    rw [hsplit, List.length_append, List.length_cons]
    omega
  unfold lookupSteps scanSteps
  omega

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 4 * Polynomial.X + Polynomial.C 8

theorem timePolynomial_eval (L : Nat) : timePolynomial.eval L = 4 * L + 8 := by
  simp [timePolynomial]

/-- A polynomial bound on the actual complete copy/skip/read execution. -/
def lookupWithSplitInTime (F : SourceEncoding.Input) (prior : List (CloneGap.Equation (Fin F.variables)))
    (equation : CloneGap.Equation (Fin F.variables)) (after : List (CloneGap.Equation (Fin F.variables)))
    (hsplit : F.equations = prior ++ equation :: after)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hsource : base .source = inputBits F)
    (hindex : base .index = encodeWord prior.length ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .copyOut, (ambient, register), base⟩
      (some ⟨none, (ambient, none),
        outputTapes base equation indexSuffix (encodeWords (after.flatMap equationWords))⟩)
      (timePolynomial.eval (inputBits F).length) where
  steps := lookupSteps F prior equation
  evals_in_steps := lookupWithSplitTrace F prior equation after hsplit base indexSuffix
    hsource hindex hwork hscratch ambient register
  steps_le_m := by
    rw [timePolynomial_eval]
    exact lookupSteps_le_input F prior equation after hsplit

def lookupInTime (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hsource : base .source = inputBits F)
    (hindex : base .index = encodeWord i.val ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .copyOut, (ambient, register), base⟩
      (some ⟨none, (ambient, none), outputTapes base F.equations[i.val] indexSuffix
        (encodeWords ((F.equations.drop (i.val + 1)).flatMap equationWords))⟩)
      (timePolynomial.eval (inputBits F).length) := by
  have hp : (F.equations.take i.val).length = i.val := by
    rw [List.length_take, Nat.min_eq_left i.isLt.le]
  have hs : F.equations = F.equations.take i.val ++ F.equations[i.val] :: F.equations.drop (i.val + 1) := by
    rw [List.getElem_cons_drop i.isLt, List.take_append_drop]
  apply lookupWithSplitInTime F (F.equations.take i.val) F.equations[i.val]
    (F.equations.drop (i.val + 1)) hs base indexSuffix hsource
    (by simpa only [hp] using hindex) hwork hscratch ambient register


end UniqueGamesTheorem.Reduction.SourceEquationLookup

end

section

namespace UniqueGamesTheorem.Reduction.MachineSourceTuple

open Turing UniqueGamesTheorem.Foundations.Complexity
open SourceEncoding
open MachineComposition

inductive Tape (width : Nat) (Extra : Type)
  | source | index | work | scratch | copyScratch
  | savedIndex (coordinate : Fin width)
  | field (coordinate : Fin width) (slot : Fin 4)
  | extra (value : Extra)
  deriving DecidableEq, Fintype

inductive Label (width : Nat)
  | copyOut (coordinate : Fin width) | copyBack (coordinate : Fin width)
  | lookup (coordinate : Fin width) (localLabel : SourceEquationLookup.Label)
  | clearWork (coordinate : Fin width) | clearIndex (coordinate : Fin width)
  | done
  deriving DecidableEq, Fintype

variable {width : Nat} {Extra σ : Type}

def place (j : Fin width) : SourceEquationLookup.Tape → Tape width Extra
  | .source => .source | .index => .index | .work => .work | .scratch => .scratch
  | .field s => .field j s


/-- Explicit inverse for the shared lookup block; other coordinate fields
and caller tapes lie outside this placement. -/
def view (j : Fin width) : Tape width Extra → Option SourceEquationLookup.Tape
  | .source => some .source | .index => some .index
  | .work => some .work | .scratch => some .scratch
  | .field i s => if i = j then some (.field s) else none
  | _ => none

def fill (j : Fin width) (base : Tape width Extra → List Bool)
    (localTapes : SourceEquationLookup.Tape → List Bool) : Tape width Extra → List Bool :=
  MachineCloudPadding.Placement.tapes (view j) localTapes base

@[simp] theorem fill_self (j : Fin width) (base : Tape width Extra → List Bool) :
    fill j base (base ∘ place j) = base := by
  funext p
  cases p <;> simp [fill, view, place, MachineCloudPadding.Placement.tapes]
  rename_i i s
  by_cases h : i = j <;> simp [h]

variable [DecidableEq Extra]

omit [DecidableEq Extra] in
@[simp] theorem view_place (j : Fin width) (p : SourceEquationLookup.Tape) :
    view j (place j p : Tape width Extra) = some p := by
  cases p <;> simp [view, place]

omit [DecidableEq Extra] in
theorem place_view (j : Fin width) (p : Tape width Extra) (localTape : SourceEquationLookup.Tape)
    (h : view j p = some localTape) : place j localTape = p := by
  cases p <;> cases localTape <;> simp_all [view, place]

def placedStatement (j : Fin width)
    (q : TM2.Stmt (fun _ : SourceEquationLookup.Tape => Bool)
      SourceEquationLookup.Label ((σ × Unit) × Option Bool)) :
    TM2.Stmt (fun _ : Tape width Extra => Bool) (Label width) ((σ × Unit) × Option Bool) :=
  MachineCloudPadding.Placement.statement (place j) (.lookup j) (some (.clearWork j)) q

def nextLabel (j : Fin width) : Label width :=
  if h : j.val + 1 < width then .copyOut ⟨j.val + 1, h⟩ else .done

def program : Label width → TM2.Stmt (fun _ : Tape width Extra => Bool)
    (Label width) ((σ × Unit) × Option Bool)
  | .copyOut j => Reduction.MachineTransfer.loopAt (.savedIndex j) .copyScratch id false
      (.copyOut j) (some (.copyBack j))
  | .copyBack j => MachineCopy.forkLoop .copyScratch (.savedIndex j) .index false
      (.copyBack j) (some (.lookup j .copyOut))
  | .lookup j l => placedStatement j (SourceEquationLookup.program l)
  | .clearWork j => MachineDrain.drain .work (.clearWork j) (some (.clearIndex j))
  | .clearIndex j => MachineDrain.drain .index (.clearIndex j) (some (nextLabel j))
  | .done => .halt

def lookupOutput (j : Fin width) (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : List Bool) : Tape width Extra → List Bool :=
  fill j base (SourceEquationLookup.outputTapes (base ∘ place j) F.equations[i.val] suffix
    (encodeWords ((F.equations.drop (i.val + 1)).flatMap equationWords)))

noncomputable def placedLookupInTime (j : Fin width) (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : List Bool)
    (hsource : base .source = inputBits F)
    (hindex : base .index = encodeWord i.val ++ suffix)
    (hwork : base .work = []) (hscratch : base .scratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.lookup j .copyOut), ((ambient, ()), register), base⟩
      (some ⟨some (.clearWork j), ((ambient, ()), none), lookupOutput j F i base suffix⟩)
      (4 * (inputBits F).length + 8) := by
  have h := SourceEquationLookup.lookupInTime F i (base ∘ place j) suffix
    hsource hindex hwork hscratch (ambient, ()) register
  have lifted := liftExecutionInTime (TM2.step SourceEquationLookup.program) (TM2.step program)
    (MachineCloudPadding.Placement.configuration (view j) (.lookup j) (some (.clearWork j)) base)
    (MachineCloudPadding.Placement.step_simulation (place j) (view j) (view_place j)
      (place_view j) (.lookup j) (some (.clearWork j)) base SourceEquationLookup.program
      program (fun _ => rfl)) h
  simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    lookupOutput, fill, SourceEquationLookup.timePolynomial_eval,
    show MachineCloudPadding.Placement.tapes (view j) (base ∘ place j) base = base
      from fill_self j base] using lifted

def copiedTapes (j : Fin width) (base : Tape width Extra → List Bool) : Tape width Extra → List Bool :=
  Function.update base .index (base (.savedIndex j))

def coordinateOutput {n : Nat} (j : Fin width) (equation : CloneGap.Equation (Fin n))
    (base : Tape width Extra → List Bool) : Tape width Extra → List Bool
  | .index | .work => []
  | .field k s => if k = j then
      encodeWord ((equationWords equation)[s.val]'(by simp)) ++ base (.field k s)
    else base (.field k s)
  | p => base p

theorem cleanup_lookupOutput (j : Fin width) (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : List Bool) :
    Function.update (Function.update
      (lookupOutput j F i (copiedTapes j base) suffix) .work []) .index [] =
      coordinateOutput j F.equations[i.val] base := by
  funext p
  cases p <;> try simp [lookupOutput, fill, view, MachineCloudPadding.Placement.tapes,
    coordinateOutput, copiedTapes, place, SourceEquationLookup.outputTapes]
  rename_i coordinate slot
  by_cases h : coordinate = j <;> simp [h]

omit [DecidableEq Extra] in
@[simp] theorem coordinateOutput_savedIndex {n : Nat} (j k : Fin width) (equation : CloneGap.Equation (Fin n))
    (base : Tape width Extra → List Bool) :
    coordinateOutput j equation base (.savedIndex k) = base (.savedIndex k) := rfl

omit [DecidableEq Extra] in
@[simp] theorem coordinateOutput_field {n : Nat} (j : Fin width) (s : Fin 4)
    (equation : CloneGap.Equation (Fin n)) (base : Tape width Extra → List Bool) :
    coordinateOutput j equation base (.field j s) =
      encodeWord ((equationWords equation)[s.val]'(by simp)) ++ base (.field j s) := by
  simp [coordinateOutput]

omit [DecidableEq Extra] in
theorem coordinateOutput_other_field {n : Nat} (j k : Fin width) (s : Fin 4)
    (equation : CloneGap.Equation (Fin n)) (base : Tape width Extra → List Bool) (h : k ≠ j) :
    coordinateOutput j equation base (.field k s) = base (.field k s) := by
  simp [coordinateOutput, h]

theorem suffix_length_le_input (F : SourceEncoding.Input) (i : Nat) :
    (encodeWords ((F.equations.drop i).flatMap equationWords)).length ≤ (inputBits F).length := by
  have hs := List.take_append_drop i F.equations
  have he : inputBits F = encodeWords [F.variables, F.equations.length] ++
      encodeWords ((F.equations.take i).flatMap equationWords) ++
      encodeWords ((F.equations.drop i).flatMap equationWords) := by
    conv_lhs => rw [inputBits, inputWords, ← hs]
    simp only [List.flatMap_append, encodeWords_append, List.append_assoc]
    rw [hs]
  rw [he, List.length_append, List.length_append]
  omega

noncomputable def coordinateInTime (j : Fin width) (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : List Bool)
    (hsource : base .source = inputBits F)
    (hsavedIndex : base (.savedIndex j) = encodeWord i.val ++ suffix)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.copyOut j), ((ambient, ()), register), base⟩
      (some ⟨some (nextLabel j), ((ambient, ()), none), coordinateOutput j F.equations[i.val] base⟩)
      (6 * (inputBits F).length + 4 * (base (.savedIndex j)).length + 20) := by
  let copied := copiedTapes j base
  let loaded := lookupOutput j F i copied suffix
  have copyRun := MachineCopy.copyInTime (.savedIndex j) .index .copyScratch
    (by simp) (by simp) (by simp) false (.copyOut j) (.copyBack j)
    (some (.lookup j .copyOut)) program rfl rfl base hcopy (ambient, ()) register
  have copied_eq : Function.update base .index (base (.savedIndex j) ++ base .index) = copied := by
    simp [copied, copiedTapes, hindex]
  rw [copied_eq] at copyRun
  have lookupRun := placedLookupInTime j F i copied suffix
    (by simpa [copied, copiedTapes] using hsource)
    (by simpa [copied, copiedTapes] using hsavedIndex)
    (by simpa [copied, copiedTapes] using hwork)
    (by simpa [copied, copiedTapes] using hscratch) ambient none
  have workRun := MachineDrain.drainInTime .work (.clearWork j) (some (.clearIndex j))
    program rfl loaded (ambient, ()) none
  have indexRun := MachineDrain.drainInTime .index (.clearIndex j) (some (nextLabel j))
    program rfl (Function.update loaded .work []) (ambient, ()) none
  have hrun := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ copyRun lookupRun)
      workRun) indexRun
  have hw : loaded .work = encodeWords ((F.equations.drop (i.val + 1)).flatMap equationWords) := by
    simp [loaded, lookupOutput, fill, view, MachineCloudPadding.Placement.tapes,
      SourceEquationLookup.output_work]
  have hi : (Function.update loaded .work []) .index = encodeWord 0 ++ suffix := by
    simp [loaded, lookupOutput, fill, view, MachineCloudPadding.Placement.tapes,
      SourceEquationLookup.output_index]
  have hc : suffix.length ≤ (base (.savedIndex j)).length := by
    rw [hsavedIndex, List.length_append]
    omega
  refine { steps := hrun.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · simpa only [loaded, copied, cleanup_lookupOutput] using hrun.evals_in_steps
  · apply Nat.le_trans hrun.steps_le_m
    rw [hw, hi, List.length_append, encodeWord_length]
    have hs := suffix_length_le_input F (i.val + 1)
    omega

def labelAt (r : Nat) : Label width :=
  if h : r < width then .copyOut ⟨r, h⟩ else .done

theorem nextLabel_eq (j : Fin width) : nextLabel j = labelAt (j.val + 1) := rfl

/-- Exact prefix frame: each visited coordinate is assigned once, and only
index/work are cleared. This proof-side endpoint does not replay the loader. -/
def stageTapes (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (r : Nat) : Tape width Extra → List Bool
  | .index => if 0 < r ∧ 0 < width then [] else base .index
  | .work => if 0 < r ∧ 0 < width then [] else base .work
  | .field j s => if j.val < r then
      encodeWord ((equationWords F.equations[(tuple j).val])[s.val]'(by simp)) ++ base (.field j s)
    else base (.field j s)
  | p => base p

omit [DecidableEq Extra] in
@[simp] theorem stageTapes_zero (F : SourceEncoding.Input)
    (tuple : Fin width → Fin F.equations.length) (base : Tape width Extra → List Bool) :
    stageTapes F tuple base 0 = base := by
  funext p
  cases p <;> simp [stageTapes]

omit [DecidableEq Extra] in
theorem stageTapes_succ (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (r : Nat) (hr : r < width) :
    stageTapes F tuple base (r + 1) =
      coordinateOutput ⟨r, hr⟩ F.equations[(tuple ⟨r, hr⟩).val] (stageTapes F tuple base r) := by
  funext p
  cases p <;> simp [stageTapes, coordinateOutput, show 0 < width by omega]
  rename_i j s
  by_cases hj : j = (⟨r, hr⟩ : Fin width)
  · subst j; simp
  · have hv : j.val ≠ r := fun h => hj (Fin.ext h)
    have he : j.val ≤ r ↔ j.val < r := by omega
    simp [hj, he]

omit [DecidableEq Extra] in
theorem stageTapes_frame (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (r : Nat) (p : Tape width Extra)
    (hi : p ≠ .index) (hw : p ≠ .work) (hf : ∀ j s, p ≠ .field j s) :
    stageTapes F tuple base r p = base p := by
  cases p <;> simp_all [stageTapes]

omit [DecidableEq Extra] in
theorem stageTapes_clean (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (r : Nat) (hi : base .index = []) (hw : base .work = []) :
    stageTapes F tuple base r .index = [] ∧ stageTapes F tuple base r .work = [] := by
  simp [stageTapes, hi, hw]

omit [DecidableEq Extra] in
theorem stageTapes_field (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (r : Nat) (j : Fin width) (s : Fin 4) :
    stageTapes F tuple base r (.field j s) = if j.val < r then
      encodeWord ((equationWords F.equations[(tuple j).val])[s.val]'(by simp)) ++ base (.field j s)
      else base (.field j s) := by
  rfl

noncomputable def prefixInTime (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : Fin width → List Bool) (C : Nat)
    (hsource : base .source = inputBits F)
    (hsavedIndex : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val ++ suffix j)
    (hsize : ∀ j, (base (.savedIndex j)).length ≤ C)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (r : Nat) (hr : r ≤ width) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((ambient, ()), none), base⟩
      (some ⟨some (labelAt r), ((ambient, ()), none), stageTapes F tuple base r⟩)
      (r * (6 * (inputBits F).length + 4 * C + 20)) := by
  induction r with
  | zero => exact { steps := 0, evals_in_steps := by simp, steps_le_m := by omega }
  | succ r ih =>
    have hru : r < width := by omega
    let j : Fin width := ⟨r, hru⟩
    let before := stageTapes F tuple base r
    have hf (p : Tape width Extra) (hi : p ≠ .index) (hw : p ≠ .work)
        (hh : ∀ j s, p ≠ .field j s) : before p = base p :=
      stageTapes_frame F tuple base r p hi hw hh
    have hd := stageTapes_clean F tuple base r hindex hwork
    have hc : before (.savedIndex j) = base (.savedIndex j) := hf _ (by simp) (by simp) (by simp)
    have one := coordinateInTime j F (tuple j) before (suffix j)
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hsource)
      (by rw [hc]; exact hsavedIndex j) hd.1 hd.2
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hscratch)
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hcopy) ambient none
    have one' : StateTransition.EvalsToInTime (TM2.step program)
        ⟨some (labelAt r), ((ambient, ()), none), before⟩
        (some ⟨some (labelAt (r + 1)), ((ambient, ()), none), stageTapes F tuple base (r + 1)⟩)
        (6 * (inputBits F).length + 4 * C + 20) := by
      refine { steps := one.steps, evals_in_steps := ?_, steps_le_m := ?_ }
      · simpa only [labelAt, dite_eq_left hru, nextLabel_eq, j,
          stageTapes_succ F tuple base r hru, before] using one.evals_in_steps
      · apply Nat.le_trans one.steps_le_m
        rw [hc]
        have hs := hsize j
        omega
    have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (ih (by omega)) one'
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using joined

noncomputable def loadInTime (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : Fin width → List Bool) (C : Nat)
    (hsource : base .source = inputBits F)
    (hsavedIndex : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val ++ suffix j)
    (hsize : ∀ j, (base (.savedIndex j)).length ≤ C)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((ambient, ()), none), base⟩
      (some ⟨none, ((ambient, ()), none), stageTapes F tuple base width⟩)
      (width * (6 * (inputBits F).length + 4 * C + 20) + 1) := by
  have prefixRun := prefixInTime F tuple base suffix C hsource hsavedIndex hsize
    hindex hwork hscratch hcopy width (Nat.le_refl _) ambient
  have doneRun : StateTransition.EvalsToInTime (TM2.step (program (Extra := Extra)))
      ⟨some (labelAt width), ((ambient, ()), none), stageTapes F tuple base width⟩
      (some ⟨none, ((ambient, ()), none), stageTapes F tuple base width⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step program ⟨some (labelAt width), ((ambient, ()), none), stageTapes F tuple base width⟩ = _
    simp only [labelAt, Nat.lt_irrefl, ↓reduceDIte]
    rfl
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ prefixRun doneRun

theorem equations_length_le_input (F : SourceEncoding.Input) :
    F.equations.length ≤ (inputBits F).length := by
  simp only [inputBits, encodeWords_length, inputWords_length]
  omega

/-- Actual odometer digits have empty suffixes. The resulting complete loader
runs in a polynomial whose coefficients depend only on the fixed repetition k. -/
noncomputable def loadUnaryInTime (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool)
    (hsource : base .source = inputBits F)
    (hsavedIndex : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((ambient, ()), none), base⟩
      (some ⟨none, ((ambient, ()), none), stageTapes F tuple base width⟩)
      (width * (10 * (inputBits F).length + 20) + 1) := by
  have run := loadInTime F tuple base (fun _ => []) (inputBits F).length hsource
    (by simpa only [List.append_nil] using hsavedIndex)
    (by
      intro j
      rw [hsavedIndex j, encodeWord_length]
      have h := (tuple j).isLt
      have hm := equations_length_le_input F
      omega)
    hindex hwork hscratch hcopy ambient
  have he : 6 * (inputBits F).length + 4 * (inputBits F).length + 20 =
      10 * (inputBits F).length + 20 := by omega
  simpa only [he] using run

noncomputable def timePolynomial (width : Nat) : Polynomial Nat :=
  Polynomial.C (10 * width) * Polynomial.X + Polynomial.C (20 * width + 1)

theorem timePolynomial_eval (width L : Nat) :
    (timePolynomial width).eval L = width * (10 * L + 20) + 1 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]


def rhsField (j : Fin width) : Tape width Extra := .field j 3


def equationName {n : Nat} (e : CloneGap.Equation (Fin n)) (s : Fin 3) : Nat :=
  match s.val with
  | 0 => e.first.val
  | 1 => e.second.val
  | _ => e.third.val

omit [DecidableEq Extra] in
theorem output_rhs (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (j : Fin width) :
    stageTapes F tuple base width (rhsField j) =
      encodeWord (if F.equations[(tuple j).val].rhs then 1 else 0) ++ base (rhsField j) := by
  rw [rhsField, stageTapes_field, ite_eq_left j.isLt]
  rfl

omit [DecidableEq Extra] in
theorem output_savedIndex (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (j : Fin width) :
    stageTapes F tuple base width (.savedIndex j) = base (.savedIndex j) :=
  stageTapes_frame F tuple base width (.savedIndex j) (by simp) (by simp) (by simp)

omit [DecidableEq Extra] in
theorem output_source (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) :
    stageTapes F tuple base width .source = base .source :=
  stageTapes_frame F tuple base width .source (by simp) (by simp) (by simp)


/-- A caller shares this complete tape arena and state, mapping only labels and
the final continuation. All saved occurrence IDs remain available to its body. -/
noncomputable def placedLoadUnaryInTime {Λ : Type}
    (labels : Label width → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : Tape width Extra => Bool) Λ ((σ × Unit) × Option Bool))
    (atLabels : ∀ l, target (labels l) = MachineSubroutine.statement labels exit (program l))
    (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool)
    (hsource : base .source = inputBits F)
    (hsaved : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (labelAt 0)), ((ambient, ()), none), base⟩
      (some ⟨exit, ((ambient, ()), none), stageTapes F tuple base width⟩)
      (width * (10 * (inputBits F).length + 20) + 1) :=
  MachineSubroutine.execution labels exit program target atLabels
    (loadUnaryInTime F tuple base hsource hsaved hindex hwork hscratch hcopy ambient)


end UniqueGamesTheorem.Reduction.MachineSourceTuple

end

end OAI
