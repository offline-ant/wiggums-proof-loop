/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.PCP.AlphabetGraphLemmas
import OAI.Computability.UniqueGames.PCP.AlphabetReductionLemmas
import OAI.Computability.UniqueGames.PCP.FinalBooleanVerifier
import OAI.Computability.UniqueGames.PCP.GraphTables

namespace OAI

section

/-!
# Concrete relation addresses for the final Boolean verifier

Six-bit labels use the already checked executable little-endian enumeration.
A twelve-bit CNF pattern is split into its two endpoint labels, then addressed
in the graph table's row-major order. This fixed address map uses the actual
`VerifierToCNF.patternAt` enumeration, so no assumed correspondence between
two enumeration orders is needed. The graph interpretation is an explicit
relabeling of the validated table semantics.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern

open PCP
open scoped BigOperators

abbrev Label := FinalBooleanVerifier.Label

/-- Coordinate zero is the least significant bit. -/
abbrev labelEquiv : Label ≃ Fin 64 := AlphabetTable.Enumeration.labelEquiv


def labelIndex (label : Label) : Fin 64 := labelEquiv label


def leftHalf (bits : VerifierToCNF.Pattern 12) : Label :=
  fun j => bits (Fin.castAdd 6 j)

def rightHalf (bits : VerifierToCNF.Pattern 12) : Label :=
  fun j => bits (Fin.natAdd 6 j)

/-- Graph rows store the right endpoint index fastest. -/
def relationAddress (bits : VerifierToCNF.Pattern 12) : Fin 4096 :=
  GraphTables.relationIndex (labelIndex (leftHalf bits), labelIndex (rightHalf bits))


/-- The address is computed from the converter's actual enumerated pattern. -/
def patternRelationIndex (p : VerifierToCNF.PatternIndex 12) : Fin 4096 :=
  relationAddress (VerifierToCNF.patternAt 12 p)

@[simp] theorem patternRelationIndex_eq (p : VerifierToCNF.PatternIndex 12) :
    patternRelationIndex p = relationAddress (VerifierToCNF.patternAt 12 p) := rfl

/-- Interpret the numeric table over its explicitly decoded Boolean labels. -/
def tableGraph (table : GraphTables.Table) :
    ConstraintGraph (Fin table.vertices) (Fin table.darts) Label :=
  (GraphTables.semantics table).reindex (Equiv.refl _) (Equiv.refl _) labelEquiv.symm

@[simp] theorem tableGraph_tail (table : GraphTables.Table) (e : Fin table.darts) :
    (tableGraph table).tail e = table.rows[e].tail := rfl

@[simp] theorem tableGraph_reverse (table : GraphTables.Table) (e : Fin table.darts) :
    (tableGraph table).reverse e = table.rows[e].reverseIndex := rfl

@[simp] theorem tableGraph_accepts (table : GraphTables.Table) (e : Fin table.darts)
    (a b : Label) :
    (tableGraph table).accepts e a b =
      GraphTables.relationAt table.rows[e].relation (labelIndex a) (labelIndex b) := rfl

/-- The concrete Boolean verifier associated with an already indexed table. -/
abbrev tableVerifier (table : GraphTables.Table) : VerifierToCNF.FiniteVerifier 12 :=
  FinalBooleanVerifier.verifier (tableGraph table) (Equiv.refl _) (Equiv.refl _)


theorem pattern_lookup_eq_verifier_accepts (table : GraphTables.Table)
    (e : Fin table.darts) (p : VerifierToCNF.PatternIndex 12) :
    table.rows[e].relation[patternRelationIndex p] =
      (tableVerifier table).accepts e (VerifierToCNF.patternAt 12 p) := rfl


end UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern

end

end OAI
