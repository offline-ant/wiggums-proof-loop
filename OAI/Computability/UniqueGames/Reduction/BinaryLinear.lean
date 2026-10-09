/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import OAI.Computability.UniqueGames.Model
import OAI.Computability.UniqueGames.Reduction.BinaryCoordinates

namespace OAI

section

/-! Exact transport from XOR bit vectors to vector spaces over `ZMod 2`. -/
namespace UniqueGamesTheorem.Integration.BinaryLinear

open BinaryCoordinates

def ofBit (b : Bool) : F2 := if b then 1 else 0
def toBit (a : F2) : Bool := decide (a = 1)

theorem scalar_cases : ∀ a : F2, a = 0 ∨ a = 1 := by decide
theorem ofBit_toBit : ∀ a : F2, ofBit (toBit a) = a := by decide
theorem toBit_ofBit : ∀ b : Bool, toBit (ofBit b) = b := by decide
theorem ofBit_xor : ∀ a b : Bool, ofBit (a ^^ b) = ofBit a + ofBit b := by decide
theorem toBit_add : ∀ a b : F2, toBit (a + b) = (toBit a ^^ toBit b) := by decide

def toVector {n : Nat} (v : BitVec n) : Vector n := fun i => ofBit (unpack v i)
def fromVector {n : Nat} (v : Vector n) : BitVec n := pack (fun i => toBit (v i))

theorem toVector_fromVector {n : Nat} (v : Vector n) : toVector (fromVector v) = v := by
  funext i
  simp only [toVector, fromVector, unpack_pack, ofBit_toBit]

theorem fromVector_toVector {n : Nat} (v : BitVec n) : fromVector (toVector v) = v := by
  simp only [fromVector, toVector, toBit_ofBit]
  exact pack_unpack v

def coordinatesEquiv (n : Nat) : BitVec n ≃ Vector n where
  toFun := toVector
  invFun := fromVector
  left_inv := fromVector_toVector
  right_inv := toVector_fromVector


theorem finrank_vector (n : Nat) : Module.finrank F2 (Vector n) = n := by
  simp [Vector]

end UniqueGamesTheorem.Integration.BinaryLinear

end

end OAI
