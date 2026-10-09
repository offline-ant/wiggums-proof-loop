/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import OAI.Computability.UniqueGames.Machines.MachineDrain
import OAI.Computability.UniqueGames.Machines.MachineFiniteAlphabet
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.Reduction.MachineFieldTemplate

namespace OAI

/-!
A fixed number of copies of an arbitrary bit stream, by a real finite-alphabet
machine. This is the uniform-rounding stream primitive: copying a header-free
occurrence stream `C` times gives multiplicity `C` to every listed occurrence.
The input is preserved during the copy phase, physically drained, and replaced
by the forward-order result. No unbounded word is stored in finite control.
-/

namespace UniqueGamesTheorem.Explicit.MachineFixedCopies

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction


def tokens (C : Nat) : List (MachineFieldTemplate.Token 1) :=
  List.replicate C (.copy 0)

@[simp] theorem tokens_length (C : Nat) : (tokens C).length = C := by simp [tokens]


abbrev Tape := Fin 3


end UniqueGamesTheorem.Explicit.MachineFixedCopies

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionRows

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction

def identityTable (q : Nat) : PermutationTable q where
  images := Vector.ofFn id
  inverseImages := Vector.ofFn id
  leftInverse _ := by simp
  rightInverse _ := by simp

def inverseTable {q : Nat} (p : PermutationTable q) : PermutationTable q where
  images := p.inverseImages
  inverseImages := p.images
  leftInverse := p.rightInverse
  rightInverse := p.leftInverse

/-- The saved fields are ordered `u,p,q,r,v`. All four edges are oriented
left-to-right; hence the last permutation is inverted. -/
def rows {n q : Nat} (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    List (Constraint n q) :=
  [⟨vertices 0, vertices 1, identityTable q⟩,
   ⟨vertices 2, vertices 1, identityTable q⟩,
   ⟨vertices 2, vertices 3, identityTable q⟩,
   ⟨vertices 4, vertices 3, inverseTable p⟩]

@[simp] theorem rows_length {n q : Nat}
    (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    (rows vertices p).length = 4 := rfl

/-- The program copies saved endpoint words and emits complete forward tables. -/
def tokens (identity inverse : List Bool) : List (MachineFieldTemplate.Token 5) :=
  [.copy 0, .copy 1, .literal identity,
   .copy 2, .copy 1, .literal identity,
   .copy 2, .copy 3, .literal identity,
   .copy 4, .copy 3, .literal inverse]

@[simp] theorem tokens_length (identity inverse : List Bool) :
    (tokens identity inverse).length = 12 := rfl


def rowBits {n q : Nat} (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    List Bool := encodeWords ((rows vertices p).flatMap constraintWords)


def scratch : Fin 7 := 5
def output : Fin 7 := 6


/-- The semantic subdivision numbering: originals and middle vertices on the
left, then two private right vertices for each occurrence. -/
def subdivisionVertexWords (n Q u v e : Nat) : Fin 5 → Nat
  | 0 => u
  | 1 => n + Q + 2 * e
  | 2 => n + e
  | 3 => n + Q + 2 * e + 1
  | 4 => v


end UniqueGamesTheorem.Explicit.MachineSubdivisionRows

end OAI
