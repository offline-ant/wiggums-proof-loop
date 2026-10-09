/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Machines.MachineInitialHeaders

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAffineAt

open Turing
open MachineComposition
open Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

/-- The affine scan is the same non-destructive scaled-prefix emitter used
for headers; only its seeded output word differs. -/
def scan (source scratch destination : K) (coefficient : Nat) (scanLabel restoreLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineInitialHeaders.prefixScan source scratch destination coefficient scanLabel restoreLabel

def seed (destination : K) (offset : Nat) (scanLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  pushWord destination (encodeWord offset).reverse (.goto (fun _ => scanLabel))

def tapes (source scratch destination : K) (base : K → List Bool)
    (input saved output : List Bool) : K → List Bool :=
  MachineCopy.forkTapes source scratch destination base input saved output

@[simp] theorem tapes_source (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination)
    (base : K → List Bool) (input saved output : List Bool) :
    tapes source scratch destination base input saved output source = input :=
  MachineCopy.forkTapes_source source scratch destination hs hd base input saved output

@[simp] theorem tapes_scratch (source scratch destination : K) (hsd : scratch ≠ destination)
    (base : K → List Bool) (input saved output : List Bool) :
    tapes source scratch destination base input saved output scratch = saved :=
  MachineCopy.forkTapes_left source scratch destination hsd base input saved output

@[simp] theorem tapes_destination (source scratch destination : K)
    (base : K → List Bool) (input saved output : List Bool) :
    tapes source scratch destination base input saved output destination = output :=
  MachineCopy.forkTapes_right source scratch destination base input saved output

theorem prepend_replicate_word (c b : Nat) (suffix : List Bool) :
    List.replicate c true ++ (encodeWord b ++ suffix) =
      encodeWord (c + b) ++ suffix := by
  simp only [encodeWord, List.replicate_add, List.append_assoc]

theorem affineTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (atRestore : program restoreLabel = Reduction.MachineTransfer.loopAt
      scratch source id false restoreLabel exit)
    (base : K → List Bool) (a b : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * (a + 1)]
      (some ⟨some scanLabel, (ambient,register), tapes source scratch destination base
        (encodeWord a ++ suffix) [] (encodeWord b ++ output)⟩) =
      some ⟨exit, (ambient,none), tapes source scratch destination base
        (encodeWord a ++ suffix) [] (encodeWord (coefficient * a + b) ++ output)⟩ := by
  have run := MachineInitialHeaders.prefixTrace source scratch destination hs hd hsd
    coefficient scanLabel restoreLabel exit program atScan atRestore
    (tapes source scratch destination base (encodeWord a ++ suffix) [] (encodeWord b ++ output))
    a suffix (tapes_source _ _ _ hs hd _ _ _ _) (tapes_scratch _ _ _ hsd _ _ _ _)
    ambient register
  simpa only [tapes_destination, prepend_replicate_word, tapes, MachineCopy.forkTapes,
    Function.update_self, Function.update_idem, Nat.mul_add, Nat.mul_one] using run


/-- Include the literal offset prefix. The caller supplies an arbitrary output
suffix, not a precomputed address; all runtime arithmetic occurs on the tapes. -/
theorem seededAffineTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient offset : Nat) (seedLabel scanLabel restoreLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atSeed : program seedLabel = seed destination offset scanLabel)
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (atRestore : program restoreLabel = Reduction.MachineTransfer.loopAt
      scratch source id false restoreLabel exit)
    (base : K → List Bool) (a : Nat) (suffix : List Bool)
    (sourceWord : base source = encodeWord a ++ suffix) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * (a + 1) + 1]
      (some ⟨some seedLabel, (ambient,register), base⟩) =
      some ⟨exit, (ambient,none),
        Function.update base destination (encodeWord (coefficient * a + offset) ++ base destination)⟩ := by
  have hseed : TM2.step program ⟨some seedLabel,(ambient,register),base⟩ =
      some ⟨some scanLabel,(ambient,register),
        Function.update base destination (encodeWord offset ++ base destination)⟩ := by
    change some (TM2.stepAux (program seedLabel) _ _) = _
    rw [atSeed, seed, stepAux_pushWord]
    simp only [List.reverse_reverse, TM2.stepAux]
  have hrun := affineTrace source scratch destination hs hd hsd coefficient scanLabel restoreLabel
    exit program atScan atRestore base a offset suffix (base destination) ambient register
  have hframe (word : List Bool) :
      tapes source scratch destination base (encodeWord a ++ suffix) [] word =
        Function.update base destination word := by
    rw [← sourceWord, ← scratchEmpty]
    simp only [tapes, MachineCopy.forkTapes, Function.update_eq_self]
  rw [hframe, hframe] at hrun
  rw [Function.iterate_succ_apply]
  simp only [advance_some]
  rw [hseed]
  exact hrun

inductive Label
  | seed | scan | restore
  deriving DecidableEq

instance : Fintype Label where
  elems := {.seed, .scan, .restore}
  complete x := by cases x <;> simp

def program (source scratch destination : K) (coefficient offset : Nat) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool)
  | .seed => seed destination offset .scan
  | .scan => scan source scratch destination coefficient .scan .restore
  | .restore => Reduction.MachineTransfer.loopAt scratch source id false .restore none

def machine (coefficient offset : Nat) : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := Label
  main := .seed
  σ := Unit × Option Bool
  initialState := ((),none)
  m := program 0 1 2 coefficient offset

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryAffineAt

end OAI
