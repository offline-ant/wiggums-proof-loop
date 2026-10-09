/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Data.Fin.Rev
import Mathlib.Data.List.FinRange
import OAI.Computability.UniqueGames.Machines.GraphCounterStartLemmas
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineDrainManyLemmas
import OAI.Computability.UniqueGames.Machines.MachineFiniteTable
import OAI.Computability.UniqueGames.Machines.MachineRadixStepLemmas
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.PCP.ClauseVerifierLemmas
import OAI.Computability.UniqueGames.PCP.SourceAddressArithmeticLemmas
import OAI.Computability.UniqueGames.PCP.SourceContextLoad
import OAI.Computability.UniqueGames.PCP.SourceHonestLemmas
import OAI.Computability.UniqueGames.PCP.SourceOccurrences

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission

open Turing
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open UniqueGamesTheorem.Reduction.CloneGap
open UniqueGamesTheorem.Foundations.Complexity


variable {K Λ : Type} [DecidableEq K]

/-- Executable state equality is obtained from the explicit radix code. -/
instance localInputDecidableEq (u D : ℕ) : DecidableEq (LocalInput u D) :=
  fun x y =>
    if h : (localInputEncoding u D).code x = (localInputEncoding u D).code y then
      isTrue ((localInputEncoding u D).code.injective h)
    else isFalse (fun hxy => h (congrArg (localInputEncoding u D).code hxy))


end UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission

/-! Emit one fixed descriptor equation from three preserved unary base registers.
The output order is first address, second address, third address, RHS. The actual
stack program emits those fields in reverse order. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceEquationEmit

open Turing Complexity
open SourceAddressDescriptors
open UniqueGamesTheorem.Reduction.CloneGap
open UniqueGamesTheorem.Reduction.MachineSubstitution

inductive Label
  | seed | thirdDrain | thirdFork | thirdEmit
  | secondDrain | secondFork | secondEmit | firstDrain | firstFork | firstEmit
  deriving DecidableEq

instance : Fintype Label where
  elems := {.seed, .thirdDrain, .thirdFork, .thirdEmit,
  .secondDrain, .secondFork, .secondEmit, .firstDrain, .firstFork, .firstEmit}
  complete x := by cases x <;> simp

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (σ : Type) := σ × Option Bool

def rhsBit (e : Equation Descriptor) : Nat := if e.rhs then 1 else 0

def steps (values : Fin 3 → Nat) (e : Equation Descriptor) : Nat :=
  2 * (values e.first.1 + values e.second.1 + values e.third.1) + 16

variable {K Λ σ : Type} [DecidableEq K]

def statement (sources : Fin 3 → K) (destination scratch : K)
    (e : Equation Descriptor) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .seed => pushWord destination (encodeWord (rhsBit e)).reverse
      (.goto fun _ => labels .thirdDrain)
  | .thirdDrain => Reduction.MachineTransfer.loopAt (sources e.third.1) scratch id false
      (labels .thirdDrain) (some (labels .thirdFork))
  | .thirdFork => MachineCopy.forkLoop scratch (sources e.third.1) destination false
      (labels .thirdFork) (some (labels .thirdEmit))
  | .thirdEmit => MachineRegisterEmit.emitStatement destination e.third.2
      (some (labels .secondDrain))
  | .secondDrain => Reduction.MachineTransfer.loopAt (sources e.second.1) scratch id false
      (labels .secondDrain) (some (labels .secondFork))
  | .secondFork => MachineCopy.forkLoop scratch (sources e.second.1) destination false
      (labels .secondFork) (some (labels .secondEmit))
  | .secondEmit => MachineRegisterEmit.emitStatement destination e.second.2
      (some (labels .firstDrain))
  | .firstDrain => Reduction.MachineTransfer.loopAt (sources e.first.1) scratch id false
      (labels .firstDrain) (some (labels .firstFork))
  | .firstFork => MachineCopy.forkLoop scratch (sources e.first.1) destination false
      (labels .firstFork) (some (labels .firstEmit))
  | .firstEmit => MachineRegisterEmit.emitStatement destination e.first.2 exit

def program (sources : Fin 3 → K) (destination scratch : K) (e : Equation Descriptor) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (State σ) :=
  statement sources destination scratch e id none

def prefixTapes (destination : K) (base : K → List Bool) (written : List Nat) :
    K → List Bool := Function.update base destination (encodeWords written ++ base destination)

theorem prefixTapes_other (destination : K) (base : K → List Bool) (written : List Nat)
    (k : K) (hk : k ≠ destination) : prefixTapes destination base written k = base k := by
  simp [prefixTapes, hk]

theorem equationTrace (sources : Fin 3 → K) (destination scratch : K)
    (sourceDestination : ∀ side, sources side ≠ destination)
    (sourceScratch : ∀ side, sources side ≠ scratch)
    (destinationScratch : destination ≠ scratch) (e : Equation Descriptor)
    (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement sources destination scratch e labels exit label)
    (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (sources side) = encodeWord (values side))
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps values e]
      (some ⟨some (labels .seed), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), prefixTapes destination base (words values e)⟩ := by
  have hw (written : List Nat) (side : Fin 3) :
      prefixTapes destination base written (sources side) = encodeWord (values side) := by
    rw [prefixTapes_other _ _ _ _ (sourceDestination side), sourceWords side]
  have hs (written : List Nat) : prefixTapes destination base written scratch = [] := by
    rw [prefixTapes_other _ _ _ _ (Ne.symm destinationScratch), scratchEmpty]
  have hseed : (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .seed), (ambient, register), base⟩) =
      some ⟨some (labels .thirdDrain), (ambient, register),
        prefixTapes destination base [rhsBit e]⟩ := by
    change some (TM2.stepAux (p (labels .seed)) (ambient, register) base) = _
    rw [atLabels .seed]
    simp only [statement, stepAux_pushWord, List.reverse_reverse, TM2.stepAux,
      prefixTapes, encodeWords, List.append_nil]
  have hthird : (MachineComposition.advance (TM2.step p))^[2 * values e.third.1 + 5]
      (some ⟨some (labels .thirdDrain), (ambient, register),
        prefixTapes destination base [rhsBit e]⟩) =
      some ⟨some (labels .secondDrain), (ambient, none),
        prefixTapes destination base [realize values e.third, rhsBit e]⟩ := by
    have h := MachineRegisterEmit.registerEmitTrace (sources e.third.1) destination scratch
      (sourceDestination _) (sourceScratch _) destinationScratch e.third.2
      (labels .thirdDrain) (labels .thirdFork) (labels .thirdEmit) (some (labels .secondDrain))
      p (atLabels .thirdDrain) (atLabels .thirdFork) (atLabels .thirdEmit)
      (prefixTapes destination base [rhsBit e]) (values e.third.1)
      (hw _ _) (hs _) ambient register
    simpa only [prefixTapes, Function.update_self, Function.update_idem, realize,
      encodeWords, List.append_nil, List.append_assoc] using h
  have hsecond : (MachineComposition.advance (TM2.step p))^[2 * values e.second.1 + 5]
      (some ⟨some (labels .secondDrain), (ambient, none),
        prefixTapes destination base [realize values e.third, rhsBit e]⟩) =
      some ⟨some (labels .firstDrain), (ambient, none),
        prefixTapes destination base [realize values e.second, realize values e.third, rhsBit e]⟩ := by
    have h := MachineRegisterEmit.registerEmitTrace (sources e.second.1) destination scratch
      (sourceDestination _) (sourceScratch _) destinationScratch e.second.2
      (labels .secondDrain) (labels .secondFork) (labels .secondEmit) (some (labels .firstDrain))
      p (atLabels .secondDrain) (atLabels .secondFork) (atLabels .secondEmit)
      (prefixTapes destination base [realize values e.third, rhsBit e]) (values e.second.1)
      (hw _ _) (hs _) ambient none
    simpa only [prefixTapes, Function.update_self, Function.update_idem, realize,
      encodeWords, List.append_nil, List.append_assoc] using h
  have hfirst : (MachineComposition.advance (TM2.step p))^[2 * values e.first.1 + 5]
      (some ⟨some (labels .firstDrain), (ambient, none),
        prefixTapes destination base [realize values e.second, realize values e.third, rhsBit e]⟩) =
      some ⟨exit, (ambient, none), prefixTapes destination base (words values e)⟩ := by
    have h := MachineRegisterEmit.registerEmitTrace (sources e.first.1) destination scratch
      (sourceDestination _) (sourceScratch _) destinationScratch e.first.2
      (labels .firstDrain) (labels .firstFork) (labels .firstEmit) exit
      p (atLabels .firstDrain) (atLabels .firstFork) (atLabels .firstEmit)
      (prefixTapes destination base [realize values e.second, realize values e.third, rhsBit e])
      (values e.first.1) (hw _ _) (hs _) ambient none
    simpa only [prefixTapes, Function.update_self, Function.update_idem, words, rhsBit, realize,
      encodeWords, List.append_nil, List.append_assoc] using h
  rw [show steps values e = (2 * values e.first.1 + 5) +
      ((2 * values e.second.1 + 5) + ((2 * values e.third.1 + 5) + 1)) by
        unfold steps; omega]
  rw [Function.iterate_add_apply _ (2 * values e.first.1 + 5),
    Function.iterate_add_apply _ (2 * values e.second.1 + 5),
    Function.iterate_add_apply _ (2 * values e.third.1 + 5), hseed, hthird, hsecond, hfirst]


abbrev Tape := Fin 3 ⊕ Bool

def machine (e : Equation Descriptor) : FinTM2 where
  K := Tape
  k₀ := .inl 0
  k₁ := .inr false
  Γ _ := Bool
  Λ := Label
  main := .seed
  σ := State Unit
  initialState := ((), none)
  m := program Sum.inl (.inr false) (.inr true) e


end UniqueGamesTheorem.Foundations.Hastad.SourceEquationEmit

namespace UniqueGamesTheorem.Foundations.Hastad.SourceProfileBridge

open Target SourceContexts SourceOccurrences SourceLocalSignature
open Complexity

def positionEncoding (u : ℕ) : Encoding (Position u) :=
  (Encoding.fin u).prod slotEncoding

def names (F : Formula) {u : ℕ} (c : ClauseContext F u) :
    Fin (positionEncoding u).size → ℕ :=
  fun i => (occurrenceName F c ((positionEncoding u).code.symm i)).val

def nameWords (F : Formula) {u : ℕ} (c : ClauseContext F u) :
    Fin (positionEncoding u).size → List Bool :=
  fun i => encodeWord (names F c i)

def reindexProfile (u : ℕ) (profile : MachineFieldProfile.Profile (positionEncoding u).size) :
    NameProfile u :=
  fun p q => profile ((positionEncoding u).code p) ((positionEncoding u).code q)

theorem computed_profile_eq (F : Formula) {u : ℕ} (c : ClauseContext F u) :
    reindexProfile u (MachineFieldProfile.equalityProfile (nameWords F c)) =
      contextNameProfile F c := by
  funext p q
  unfold reindexProfile nameWords
  rw [MachineFieldProfile.equalityProfile_encodeWord]
  simp only [names, Equiv.symm_apply_apply, contextNameProfile, Fin.ext_iff]

theorem prepared_signature_eq (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) :
    (⟨fun p => positiveAt (PCP.clauseAt F (c p.1)) p.2,
      reindexProfile u (MachineFieldProfile.equalityProfile (nameWords F c)), s⟩ :
        Signature u) = ofContext F c s := by
  rw [computed_profile_eq]
  rfl

/-- Every isolated unary variable-name field is bounded by the true CNF
input encoding, including formulas with unused declared variable names. -/
theorem nameWords_length_le_input (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (i : Fin (positionEncoding u).size) :
    (nameWords F c i).length ≤ (formulaBits F).length := by
  rw [nameWords, encodeWord_length]
  exact (Nat.succ_le_of_lt
    (occurrenceName F c ((positionEncoding u).code.symm i)).isLt).trans
      (SourceBounds.formulaBits_length_ge_variables F)

end UniqueGamesTheorem.Foundations.Hastad.SourceProfileBridge

namespace UniqueGamesTheorem.Foundations.Hastad.SourceRankPhase

open Turing Complexity
open scoped BigOperators
open Target SourceContexts SourceOccurrences SourceAddressArithmetic

def rank {width : Nat} (radix : Nat) (digits : Fin width → Nat) : Nat :=
  ∑ i : Fin width, digits i * radix ^ i.val

def reverseDigits {width : Nat} (digits : Fin width → Nat) (i : Nat) : Nat :=
  if h : i < width then digits (Fin.rev ⟨i, h⟩) else 0

@[simp] theorem reverseDigits_apply {width : Nat} (digits : Fin width → Nat) (i : Fin width) :
    reverseDigits digits i.val = digits i.rev := by
  simp [reverseDigits, i.isLt]

theorem horner_value_sum (radix : Nat) (digits : Nat → Nat) (n : Nat) :
    MachineHorner.value radix digits n =
      ∑ i ∈ Finset.range n, digits i * radix ^ (n - 1 - i) := by
  induction n with
  | zero => simp [MachineHorner.value]
  | succ n ih =>
    rw [MachineHorner.value, ih, Finset.sum_range_succ, Finset.mul_sum]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, Nat.mul_one]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [show n - i = (n - 1 - i) + 1 by omega, pow_succ]
    ac_rfl

theorem horner_reverse_eq_rank {width : Nat} (radix : Nat) (digits : Fin width → Nat) :
    MachineHorner.value radix (reverseDigits digits) width = rank radix digits := by
  rw [horner_value_sum, Finset.sum_range]
  calc
    (∑ i : Fin width, reverseDigits digits i.val * radix ^ (width - 1 - i.val)) =
        ∑ i : Fin width, digits i.rev * radix ^ i.rev.val := by
      apply Finset.sum_congr rfl
      intro i _
      rw [reverseDigits_apply]
      have he : width - 1 - i.val = i.rev.val := by
        simp only [Fin.rev]
        omega
      rw [he]
    _ = rank radix digits := by
      simpa only [rank, Fin.revPerm_apply] using
        Equiv.sum_comp (Fin.revPerm (n := width)) (fun i => digits i * radix ^ i.val)

variable {K Λ σ : Type} {width : Nat}

/-- Reverse only digit positions. All six fixed work/control roles stay put. -/
def reverseSlots (slots : MachineHorner.Layout width ↪ K) : MachineHorner.Layout width ↪ K :=
  (Equiv.sumCongr (Equiv.refl (Fin 6)) (Fin.revPerm (n := width))).toEmbedding.trans slots

@[simp] theorem reverseSlots_control (slots : MachineHorner.Layout width ↪ K) (i : Fin 6) :
    reverseSlots slots (.inl i) = slots (.inl i) := rfl

@[simp] theorem reverseSlots_digit (slots : MachineHorner.Layout width ↪ K) (i : Fin width) :
    reverseSlots slots (.inr i) = slots (.inr i.rev) := rfl

variable [DecidableEq K]

omit [DecidableEq K] in
theorem clean_reverseSlots (slots : MachineHorner.Layout width ↪ K) (base : K → List Bool)
    (clean : MachineHorner.Clean slots base) : MachineHorner.Clean (reverseSlots slots) base where
  accA := by simpa only [reverseSlots_control] using clean.accA
  accB := by simpa only [reverseSlots_control] using clean.accB
  counter := by simpa only [reverseSlots_control] using clean.counter
  scratch := by simpa only [reverseSlots_control] using clean.scratch

def statement (slots : MachineHorner.Layout width ↪ K)
    (labels : MachineHorner.Label width → Λ) (exit : Option Λ) :
    MachineHorner.Label width → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ) :=
  MachineHorner.statement (reverseSlots slots) labels exit

def program (slots : MachineHorner.Layout width ↪ K) :
    MachineHorner.Label width → TM2.Stmt (fun _ : K => Bool)
      (MachineHorner.Label width) (MachineHorner.State σ) :=
  statement slots id none

/-- Exact execution using existing digit fields; only the destination changes. -/
theorem rankTrace (slots : MachineHorner.Layout width ↪ K)
    (labels : MachineHorner.Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Fin width → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i, base (slots (.inr i)) = encodeWord (digits i))
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[
      MachineHorner.steps radix (reverseDigits digits) width]
      (some ⟨some (labels .start), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (rank radix digits)⟩ := by
  have h := MachineHorner.hornerTrace (reverseSlots slots) labels exit p atLabels base radix
    (reverseDigits digits) operandRadix
    (fun i => by simpa only [reverseSlots_digit, reverseDigits_apply] using operandDigits i.rev)
    (clean_reverseSlots slots base clean) ambient register
  rw [horner_reverse_eq_rank] at h
  simpa only [MachineHorner.resultTapes, reverseSlots_control] using h


def rankInPolynomialTime (slots : MachineHorner.Layout width ↪ K)
    (labels : MachineHorner.Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Fin width → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i, base (slots (.inr i)) = encodeWord (digits i))
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool)
    (magnitude : Nat) (radixBound : radix ≤ magnitude) (digitBound : ∀ i, digits i ≤ magnitude) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .start), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (rank radix digits)⟩)
      ((MachineHorner.timePolynomial width).eval magnitude) where
  steps := MachineHorner.steps radix (reverseDigits digits) width
  evals_in_steps := rankTrace slots labels exit p atLabels base radix digits operandRadix
    operandDigits clean ambient register
  steps_le_m := MachineHorner.steps_le_timePolynomial radix (reverseDigits digits) width magnitude
    radixBound (fun i hi => by simpa only [reverseDigits, dite_eq_left hi] using digitBound (Fin.rev ⟨i, hi⟩))

def variableRankInTime (F : Formula) (u : Nat) (v : VariableContext F u)
    (slots : MachineHorner.Layout u ↪ K) (labels : MachineHorner.Label u → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (operandRadix : base (slots (.inl 0)) = encodeWord F.variables)
    (operandDigits : ∀ i, base (slots (.inr i)) = encodeWord (v i).val)
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .start), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none),
        MachineHorner.resultTapes slots base (((variableEncoding F u).code v).val)⟩)
      ((MachineHorner.timePolynomial u).eval F.variables) := by
  have h := rankInPolynomialTime slots labels exit p atLabels base F.variables (fun i => (v i).val)
    operandRadix operandDigits clean ambient register F.variables (Nat.le_refl _) (fun i => (v i).isLt.le)
  simpa only [rank, ← variable_rank F u v] using h

def clauseRankInTime (F : Formula) (u : Nat) (c : ClauseContext F u)
    (slots : MachineHorner.Layout u ↪ K) (labels : MachineHorner.Label u → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (operandRadix : base (slots (.inl 0)) = encodeWord F.clauses.length)
    (operandDigits : ∀ i, base (slots (.inr i)) = encodeWord (c i).val)
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .start), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none),
        MachineHorner.resultTapes slots base (((clauseEncoding F u).code c).val)⟩)
      ((MachineHorner.timePolynomial u).eval F.clauses.length) := by
  have h := rankInPolynomialTime slots labels exit p atLabels base F.clauses.length (fun i => (c i).val)
    operandRadix operandDigits clean ambient register F.clauses.length (Nat.le_refl _) (fun i => (c i).isLt.le)
  simpa only [rank, ← clause_rank F u c] using h


def machine (width : Nat) : FinTM2 where
  K := MachineHorner.Layout width
  k₀ := .inl 0
  k₁ := .inl 3
  Γ _ := Bool
  Λ := MachineHorner.Label width
  main := .start
  σ := MachineHorner.State Unit
  initialState := (((), ()), none)
  m := program (Function.Embedding.refl (MachineHorner.Layout width))


variable {u : Nat} {Extra : Type}

/-- Control roles may include preserved headers and dedicated protected extras. -/
def clauseSlots (controls : Fin 6 ↪ Extra) :
    MachineHorner.Layout u ↪ SourceContextLoad.Tape u Extra where
  toFun
    | .inl i => .extra (controls i)
    | .inr i => .current i
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (controls.injective (SourceContextLoad.Tape.extra.inj h))
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr (SourceContextLoad.Tape.current.inj h)

/-- Each coordinate selects its own loaded variable field, even if names repeat. -/
def variableSlots (controls : Fin 6 ↪ Extra) (selected : SlotContext u) :
    MachineHorner.Layout u ↪ SourceContextLoad.Tape u Extra where
  toFun
    | .inl i => .extra (controls i)
    | .inr i => SourceContextLoad.variableField i (slotEncoding.code (selected i))
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (controls.injective (SourceContextLoad.Tape.extra.inj h))
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr (SourceContextLoad.Tape.field.inj h).1

@[simp] theorem clauseSlots_control (controls : Fin 6 ↪ Extra) (i : Fin 6) :
    clauseSlots (u := u) controls (.inl i) = .extra (controls i) := rfl

@[simp] theorem clauseSlots_digit (controls : Fin 6 ↪ Extra) (i : Fin u) :
    clauseSlots controls (.inr i) = .current i := rfl

@[simp] theorem variableSlots_control (controls : Fin 6 ↪ Extra) (selected : SlotContext u) (i : Fin 6) :
    variableSlots controls selected (.inl i) = .extra (controls i) := rfl

@[simp] theorem variableSlots_digit (controls : Fin 6 ↪ Extra) (selected : SlotContext u) (i : Fin u) :
    variableSlots controls selected (.inr i) =
      SourceContextLoad.variableField i (slotEncoding.code (selected i)) := rfl

theorem selectedDigits_loaded (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (controls : Fin 6 ↪ Extra) (base : SourceContextLoad.Tape u Extra → List Bool)
    (empty : ∀ i, base (SourceContextLoad.variableField i (slotEncoding.code (selected i))) = [])
    (i : Fin u) :
    SourceContextLoad.stageTapes F c base u (variableSlots controls selected (.inr i)) =
      encodeWord (sampledVariables F c selected i).val := by
  rw [variableSlots_digit]
  erw [SourceContextLoad.output_variable, empty i, List.append_nil]
  congr 1
  cases hs : selected i <;> simp [sampledVariables, PCP.nameAt, PCP.clauseAt, slotEncoding, hs] <;> rfl

end UniqueGamesTheorem.Foundations.Hastad.SourceRankPhase

namespace UniqueGamesTheorem.Foundations.Hastad.SourceSignLoad

open Turing
open SourceLocalSignature
open UniqueGamesTheorem.Foundations.Complexity

/-- An explicit computable enumeration, without an arbitrary finite-type
equivalence. Slots occur first, second, third within each clause coordinate. -/
def positions (u : ℕ) : List (Position u) :=
  ((SourceOccurrences.Encoding.fin u).prod SourceOccurrences.slotEncoding).enumerate

theorem mem_positions {u : ℕ} (p : Position u) : p ∈ positions u :=
  SourceOccurrences.Encoding.mem_enumerate _ p

/-- The mathematical result of the individual finite sign-register writes. -/
def fillSigns {u : ℕ} (values initial : Position u → Bool)
    (cells : List (Position u)) : Position u → Bool :=
  cells.foldl (fun signs p => Function.update signs p (values p)) initial

theorem fillSigns_apply {u : ℕ} (values initial : Position u → Bool)
    (cells : List (Position u)) (p : Position u) :
    fillSigns values initial cells p = if p ∈ cells then values p else initial p := by
  induction cells generalizing initial with
  | nil => simp [fillSigns]
  | cons q cells ih =>
    change fillSigns values (Function.update initial q (values q)) cells p = _
    rw [ih]
    by_cases hp : p ∈ cells
    · simp [hp]
    · by_cases hpq : p = q
      · subst q; simp [hp]
      · simp [hp, hpq]

theorem fillSigns_positions {u : ℕ} (values initial : Position u → Bool) :
    fillSigns values initial (positions u) = values := by
  funext p
  rw [fillSigns_apply]
  simp only [mem_positions, ↓reduceIte]

variable {u : ℕ} {K Λ τ : Type} [DecidableEq K]

abbrev State (u : ℕ) (τ : Type) := Signature u × τ
abbrev Alphabet (_ : K) := Bool

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State u τ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

/-- Each statement reads only the head of one supplied polarity field. The
other signature fields and the entire ambient-register component are copied. -/
def peekChain (field : Position u → K) (exit : Option Λ) :
    List (Position u) → TM2.Stmt (Alphabet (K := K)) Λ (State u τ)
  | [] => finish exit
  | p :: rest =>
    .peek (field p) (fun state head =>
      ({state.1 with signs := Function.update state.1.signs p (head.getD false)}, state.2))
      (peekChain field exit rest)

def statement (field : Position u → K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State u τ) :=
  peekChain field exit (positions u)

/-- The head defaults make the finite program total on malformed tapes too;
the correctness theorem below supplies the actual unary-field representation. -/
def readSigns (field : Position u → K) (tapes : K → List Bool) : Position u → Bool :=
  fun p => (tapes (field p)).head?.getD false

theorem stepAux_peekChain (field : Position u → K) (exit : Option Λ)
    (cells : List (Position u)) (initial : Signature u) (ambient : τ)
    (tapes : K → List Bool) :
    TM2.stepAux (peekChain field exit cells) (initial, ambient) tapes =
      ⟨exit, ({initial with signs := fillSigns (readSigns field tapes) initial.signs cells},
        ambient), tapes⟩ := by
  induction cells generalizing initial with
  | nil => cases exit <;> rfl
  | cons p rest ih =>
    simp only [peekChain, TM2.stepAux]
    rw [ih]
    rfl

theorem stepAux_statement (field : Position u → K) (exit : Option Λ)
    (initial : Signature u) (ambient : τ) (tapes : K → List Bool) :
    TM2.stepAux (statement field exit) (initial, ambient) tapes =
      ⟨exit, ({initial with signs := readSigns field tapes}, ambient), tapes⟩ := by
  rw [statement, stepAux_peekChain, fillSigns_positions]


omit [DecidableEq K] in
theorem readSigns_of_unary (field : Position u → K) (tapes : K → List Bool)
    (values : Position u → Bool) (suffix : Position u → List Bool)
    (hfields : ∀ p, tapes (field p) = encodeWord (if values p then 1 else 0) ++ suffix p) :
    readSigns field tapes = values := by
  funext p
  rw [readSigns, hfields]
  cases values p <;> rfl


end UniqueGamesTheorem.Foundations.Hastad.SourceSignLoad

end OAI
