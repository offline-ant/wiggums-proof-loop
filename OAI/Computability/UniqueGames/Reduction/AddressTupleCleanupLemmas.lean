/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Machines.MachineDrainManyLemmas
import OAI.Computability.UniqueGames.Reduction.AddressMachineSpace

namespace OAI

section

namespace UniqueGamesTheorem.Integration.AddressTupleCleanup

open Turing UniqueGamesTheorem.Reduction UniqueGamesTheorem.Foundations.Complexity

variable (k s d noiseCount : Nat)

/-- The executable field order is slot-major within each tuple position. -/
def loadedFields : List (AddressMachineSpace.Tape k s d noiseCount) :=
  List.ofFn (fun i : Fin (4 * k) =>
    MachineSourceTuple.Tape.field ((CanonicalBodyMachine.fieldEquiv k).symm i).1
      ((CanonicalBodyMachine.fieldEquiv k).symm i).2)

@[simp] theorem loadedFields_length : (loadedFields k s d noiseCount).length = 4 * k := by
  simp only [loadedFields, List.length_ofFn]

theorem mem_loadedFields (tape : AddressMachineSpace.Tape k s d noiseCount) :
    tape ∈ loadedFields k s d noiseCount ↔
      ∃ position : Fin k, ∃ slot : Fin 4, tape = .field position slot := by
  unfold loadedFields
  constructor
  · intro h
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
    exact ⟨((CanonicalBodyMachine.fieldEquiv k).symm i).1,
      ((CanonicalBodyMachine.fieldEquiv k).symm i).2, hi.symm⟩
  · rintro ⟨position, slot, rfl⟩
    apply List.mem_ofFn.mpr
    refine ⟨CanonicalBodyMachine.fieldEquiv k (position, slot), ?_⟩
    simp only [Equiv.symm_apply_apply]

abbrev Label := MachineDrainMany.Label (loadedFields k s d noiseCount)

noncomputable abbrev cleared (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :=
  MachineDrainMany.finalTapes (loadedFields k s d noiseCount) base

noncomputable abbrev budget (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :=
  MachineDrainMany.lengthSum (loadedFields k s d noiseCount) base + 4 * k

/-- Cleanup has one pointwise normal form: erase fields and preserve every other tape. -/
@[simp] theorem cleared_apply (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (tape : AddressMachineSpace.Tape k s d noiseCount) :
    cleared k s d noiseCount base tape =
      match tape with
      | .field _ _ => []
      | _ => base tape := by
  rw [cleared, MachineDrainMany.finalTapes_apply]
  cases tape <;> simp [mem_loadedFields]

/-- Every tape outside the physical loaded fields is preserved verbatim. -/
theorem cleared_outside (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (tape : AddressMachineSpace.Tape k s d noiseCount)
    (outside : ∀ position : Fin k, ∀ slot : Fin 4, tape ≠ .field position slot) :
    cleared k s d noiseCount base tape = base tape := by
  apply MachineDrainMany.finalTapes_not_mem
  intro h
  obtain ⟨position, slot, same⟩ := (mem_loadedFields k s d noiseCount tape).1 h
  exact outside position slot same

variable {Λ : Type}

abbrev entry (labels : Label k s d noiseCount → Λ) (exit : Option Λ) :=
  MachineDrainMany.entry (loadedFields k s d noiseCount) labels exit

/-- Fixed concrete drain instructions on the actual shared address state. -/
def instruction (labels : Label k s d noiseCount → Λ) (exit : Option Λ) :
    Label k s d noiseCount → TM2.Stmt
      (fun _ : AddressMachineSpace.Tape k s d noiseCount => Bool) Λ (AddressMachineSpace.State k) :=
  MachineDrainMany.instruction (loadedFields k s d noiseCount) labels exit

noncomputable def execution (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : AddressMachineSpace.Tape k s d noiseCount => Bool)
      Λ (AddressMachineSpace.State k))
    (atLabels : ∀ l, program (labels l) = instruction k s d noiseCount labels exit l)
    (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (control : AddressMachineSpace.Control k) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry k s d noiseCount labels exit, (control, register), base⟩
      (some ⟨exit,
        (control, MachineDrainMany.finalRegister (loadedFields k s d noiseCount) register),
        cleared k s d noiseCount base⟩) (budget k s d noiseCount base) := by
  simpa only [loadedFields_length] using
    MachineDrainMany.execution (loadedFields k s d noiseCount) labels exit program atLabels
      base control register

end UniqueGamesTheorem.Integration.AddressTupleCleanup

end

section

namespace UniqueGamesTheorem.Integration.AddressTupleLoaded

open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Foundations.Complexity

abbrev Arena (k s d noiseCount : Nat) := AddressMachineSpace.Tape k s d noiseCount

variable {k s d noiseCount : Nat}

theorem loaded_field (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hempty : ∀ j slot, baseArena (.field j slot) = []) (j : Fin k) (slot : Fin 4) :
    MachineSourceTuple.stageTapes F tuple baseArena k (.field j slot) =
      encodeWord ((SourceEncoding.equationWords F.equations[(tuple j).val])[slot.val]'(by simp)) := by
  rw [MachineSourceTuple.stageTapes_field, ite_eq_left j.isLt, hempty, List.append_nil]


theorem loaded_extra (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (extra : AddressMachineSpace.Extra k s d noiseCount) :
    MachineSourceTuple.stageTapes F tuple baseArena k (.extra extra) = baseArena (.extra extra) :=
  MachineSourceTuple.stageTapes_frame F tuple baseArena k _
    (by simp) (by simp) (by intros; simp)

theorem loaded_header (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (header : MachineAddressHeaders.Arithmetic.Control) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (AddressMachineSpace.headerTape k s d noiseCount header) =
        baseArena (AddressMachineSpace.headerTape k s d noiseCount header) :=
  AddressMachineSpace.tupleOutput_headerTape k s d noiseCount F tuple baseArena header

theorem loaded_radix (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool) (B : Nat)
    (hB : baseArena (AddressMachineSpace.headerTape k s d noiseCount .baseValue) = encodeWord B) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (MachineAddressEdge.addressSlots (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
        .radix) = encodeWord B := by
  rw [AddressMachineSpace.addressSlots_radix, loaded_header, hB]


theorem loaded_privateAddress (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (tape : MachineTemplateAddress.Tape (4 * k) (1 + 9 * k)) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (AddressMachineSpace.privateAddress k s d noiseCount tape) =
        baseArena (AddressMachineSpace.privateAddress k s d noiseCount tape) :=
  loaded_extra F tuple baseArena _

/-- Cleanliness of the actual edge machine is preserved by the actual loader.
All of these local work tapes occupy the private disjoint arena block. -/
theorem loaded_clean (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (clean : MachineAddressEdge.Clean (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
      baseArena) :
    MachineAddressEdge.Clean (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
      (MachineSourceTuple.stageTapes F tuple baseArena k) := by
  constructor
  · constructor
    · exact (loaded_privateAddress F tuple baseArena .reversed).trans clean.address.reversed
    · exact (loaded_privateAddress F tuple baseArena .forward).trans clean.address.forward
    · exact (loaded_privateAddress F tuple baseArena .copyScratch).trans clean.address.copyScratch
    · exact (loaded_privateAddress F tuple baseArena .accA).trans clean.address.accA
    · exact (loaded_privateAddress F tuple baseArena .accB).trans clean.address.accB
    · exact (loaded_privateAddress F tuple baseArena .counter).trans clean.address.counter
    · exact (loaded_privateAddress F tuple baseArena .hornerScratch).trans clean.address.hornerScratch
    · intro j
      exact (loaded_privateAddress F tuple baseArena (.digit j)).trans (clean.address.digit j)
  · exact (loaded_privateAddress F tuple baseArena .output).trans clean.work


def canonicalValues (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (j : Fin k) : Fin 4 → Nat :=
  CanonicalBodyTemplate.recordFields
    (MachineSourceTuple.equationName F.equations[(tuple j).val]) (tuple j).val

/-- The three names and the distinct saved occurrence field are exact unary
values; the RHS remains on its separate field tape. -/
theorem loaded_canonicalField (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hsaved : ∀ j, baseArena (.savedIndex j) = encodeWord (tuple j).val)
    (hempty : ∀ j slot, baseArena (.field j slot) = []) (j : Fin k) (slot : Fin 4) :
    MachineSourceTuple.stageTapes F tuple baseArena k
      (AddressMachineSpace.canonicalField k s d noiseCount j slot) =
        encodeWord (canonicalValues F tuple j slot) := by
  fin_cases slot <;>
    simp [AddressMachineSpace.canonicalField, canonicalValues, CanonicalBodyTemplate.recordFields,
      loaded_field F tuple baseArena hempty, MachineSourceTuple.output_savedIndex, hsaved,
      MachineSourceTuple.equationName, SourceEncoding.equationWords]

/-- Literal input function used by the generic field-template machine. -/
theorem loaded_savedFields (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (baseArena : Arena k s d noiseCount → List Bool)
    (hsaved : ∀ j, baseArena (.savedIndex j) = encodeWord (tuple j).val)
    (hempty : ∀ j slot, baseArena (.field j slot) = []) :
    (fun i => MachineSourceTuple.stageTapes F tuple baseArena k
      (MachineAddressEdge.addressSlots (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
        (.field i))) = CanonicalBodyMachine.savedFields (canonicalValues F tuple) := by
  funext i
  change MachineSourceTuple.stageTapes F tuple baseArena k
    (AddressMachineSpace.canonicalField k s d noiseCount
      ((CanonicalBodyMachine.fieldEquiv k).symm i).1
      ((CanonicalBodyMachine.fieldEquiv k).symm i).2) = _
  exact loaded_canonicalField F tuple baseArena hsaved hempty _ _

end UniqueGamesTheorem.Integration.AddressTupleLoaded

end

section

/-!
# The exact frame after a tuple body and its field cleanup

Loading replaces the initially empty equation-field tapes. Appending writes
only the shared reversed-output header, which is outside those fields. The
actual field drains therefore restore the original arena with precisely the
same appended bytes. Saved occurrence indices and the odometer survive.
-/

namespace UniqueGamesTheorem.Integration.AddressTupleFrame

open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Foundations.Complexity

variable {k s d noiseCount : Nat}

abbrev Arena (k s d noiseCount : Nat) := AddressMachineSpace.Tape k s d noiseCount

/-- Clearing the physical fields commutes with an append to any other tape. -/
theorem cleared_outputTapes (base : Arena k s d noiseCount → List Bool)
    (output : Arena k s d noiseCount) (bits : List Bool)
    (outside : ∀ j : Fin k, ∀ slot : Fin 4, output ≠ .field j slot) :
    AddressTupleCleanup.cleared k s d noiseCount
        (MachineFieldTemplate.outputTapes base output bits) =
      MachineFieldTemplate.outputTapes
        (AddressTupleCleanup.cleared k s d noiseCount base) output bits := by
  funext tape
  by_cases h : tape = output
  · subst tape
    rw [AddressTupleCleanup.cleared_outside k s d noiseCount _ output outside,
      MachineFieldTemplate.outputTapes_output, MachineFieldTemplate.outputTapes_output,
      AddressTupleCleanup.cleared_outside k s d noiseCount base output outside]
  · rw [MachineFieldTemplate.outputTapes_other _ output bits tape h]
    change MachineDrainMany.finalTapes (AddressTupleCleanup.loadedFields k s d noiseCount)
        (MachineFieldTemplate.outputTapes base output bits) tape =
      MachineDrainMany.finalTapes (AddressTupleCleanup.loadedFields k s d noiseCount) base tape
    rw [MachineDrainMany.finalTapes_apply, MachineDrainMany.finalTapes_apply,
      MachineFieldTemplate.outputTapes_other base output bits tape h]

/-- The actual edge-output slot is a header tape, not a loaded equation field. -/
theorem cleared_appended (base : Arena k s d noiseCount → List Bool) (bits : List Bool) :
    AddressTupleCleanup.cleared k s d noiseCount
        (MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
          base bits) =
      MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
        (AddressTupleCleanup.cleared k s d noiseCount base) bits := by
  apply cleared_outputTapes
  intro j slot
  simp [AddressMachineSpace.addressSlots_output, AddressMachineSpace.headerTape]

/-- Cleanup erases exactly the fields assigned by the tuple loader. -/
theorem cleared_loaded (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Arena k s d noiseCount → List Bool)
    (hindex : base .index = []) (hwork : base .work = [])
    (hfields : ∀ j slot, base (.field j slot) = []) :
    AddressTupleCleanup.cleared k s d noiseCount
      (MachineSourceTuple.stageTapes F tuple base k) = base := by
  funext tape
  cases tape <;> simp [MachineSourceTuple.stageTapes, hindex, hwork, hfields]

/-- Exact endpoint of load, edge-byte append, and actual loaded-field cleanup. -/
theorem cleared_appended_loaded (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (base : Arena k s d noiseCount → List Bool)
    (hindex : base .index = []) (hwork : base .work = [])
    (hfields : ∀ j slot, base (.field j slot) = []) (bits : List Bool) :
    AddressTupleCleanup.cleared k s d noiseCount
        (MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
          (MachineSourceTuple.stageTapes F tuple base k) bits) =
      MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d noiseCount)
        base bits := by
  rw [cleared_appended, cleared_loaded F tuple base hindex hwork hfields]

end UniqueGamesTheorem.Integration.AddressTupleFrame

end

end OAI
