/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Machines.MachineBinaryFormulaLemmas
import OAI.Computability.UniqueGames.Machines.MachineBinaryNameMachine
import OAI.Computability.UniqueGames.Model

namespace OAI

section

/-!
Soundness of the ordinary-binary parser and its concrete name-scanning machine.
Every successful parse consumes exactly a canonical encoding and leaves its
stated suffix. Thus malformed or noncanonical bitstrings cannot name an extra
formula. The finite scanner's final-digit test is proved equivalent to the
codec's arithmetic canonicality test.
-/

namespace UniqueGamesTheorem.BinaryParsing

open BinaryEncoding BinaryFormula

theorem frame_eq (bits : List Bool) : BinaryNameMachine.frame bits = frame bits := rfl

theorem canonical_cons_cons (a b : Bool) (bits : List Bool) :
    BinaryNameMachine.canonical (a :: b :: bits) = BinaryNameMachine.canonical (b :: bits) := rfl

/-- A payload has no redundant high zero precisely when its last digit is one,
with the empty payload representing zero. -/
theorem canonical_iff (bits : List Bool) :
    BinaryNameMachine.canonical bits = true ↔ (bitsValue bits).bits = bits := by
  induction bits with
  | nil => simp [BinaryNameMachine.canonical, BinaryNameMachine.finalDigit, bitsValue]
  | cons bit bits ih =>
      cases bits with
      | nil => cases bit <;> decide
      | cons next bits =>
          rw [canonical_cons_cons, ih]
          constructor
          · intro htail
            have hn : bitsValue (next :: bits) ≠ 0 := by
              intro hz
              rw [hz, Nat.zero_bits] at htail
              contradiction
            rw [bitsValue, Nat.bits_append_bit _ bit (fun h => False.elim (hn h)), htail]
          · intro hfull
            calc
              (bitsValue (next :: bits)).bits =
                  (Nat.bit bit (bitsValue (next :: bits))).div2.bits := by rw [Nat.div2_bit]
              _ = (Nat.bit bit (bitsValue (next :: bits))).bits.tail :=
                Nat.div2_bits_eq_tail _
              _ = (bit :: next :: bits).tail := congrArg List.tail hfull
              _ = next :: bits := rfl

@[simp] theorem canonical_nat_bits (name : Nat) :
    BinaryNameMachine.canonical name.bits = true := by
  apply (canonical_iff _).mpr
  rw [bitsValue_bits]

theorem parseFrame_sound (input digits rest : List Bool)
    (parsed : parseFrame input = some (digits, rest)) : input = frame digits ++ rest := by
  induction input using List.twoStepInduction generalizing digits rest with
  | nil => simp [parseFrame] at parsed
  | singleton flag =>
      cases flag
      · simp only [parseFrame, Option.some.injEq, Prod.mk.injEq] at parsed
        rcases parsed with ⟨rfl, rfl⟩
        rfl
      · simp [parseFrame] at parsed
  | cons_cons flag bit input ih _ =>
      cases flag
      · simp only [parseFrame, Option.some.injEq, Prod.mk.injEq] at parsed
        rcases parsed with ⟨rfl, rfl⟩
        rfl
      · simp only [parseFrame, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Prod.exists, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at parsed
        obtain ⟨ds, tail, h, rfl, rfl⟩ := parsed
        simp [frame, ih ds tail h]

theorem parseName_sound (input : List Bool) (name : Nat) (rest : List Bool)
    (parsed : parseName input = some (name, rest)) : input = nameBits name ++ rest := by
  simp only [parseName, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Prod.exists, Option.ite_some_none_eq_some, Prod.mk.injEq] at parsed
  obtain ⟨digits, tail, framed, canonical, rfl, rfl⟩ := parsed
  simpa only [nameBits, ← canonical] using parseFrame_sound input digits tail framed

theorem parseLiteral_sound (input : List Bool) (literal : Literal) (rest : List Bool)
    (parsed : parseLiteral input = some (literal, rest)) :
    input = literalBits literal ++ rest := by
  cases input with
  | nil => simp [parseLiteral] at parsed
  | cons sign input =>
      simp only [parseLiteral, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Prod.exists, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at parsed
      obtain ⟨name, tail, named, rfl, rfl⟩ := parsed
      simp [literalBits, parseName_sound input name tail named]

theorem parseClause_sound (input : List Bool) (clause : Clause) (rest : List Bool)
    (parsed : parseClause input = some (clause, rest)) : input = clauseBits clause ++ rest := by
  simp only [parseClause, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Prod.exists, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at parsed
  obtain ⟨a, afterA, ha, b, afterB, hb, c, afterC, hc, rfl, rfl⟩ := parsed
  simp [clauseBits, parseLiteral_sound input a afterA ha,
    parseLiteral_sound afterA b afterB hb, parseLiteral_sound afterB c afterC hc,
    List.append_assoc]

theorem parseClauses_sound (fuel : Nat) (input : List Bool)
    (clauses : List Clause) (rest : List Bool)
    (parsed : parseClauses fuel input = some (clauses, rest)) :
    input = clausesBits clauses ++ rest := by
  induction fuel generalizing input clauses rest with
  | zero => simp [parseClauses] at parsed
  | succ fuel ih =>
      cases input with
      | nil => simp [parseClauses] at parsed
      | cons flag input =>
          cases flag
          · simp only [parseClauses, Option.some.injEq, Prod.mk.injEq] at parsed
            rcases parsed with ⟨rfl, rfl⟩
            rfl
          · simp only [parseClauses, Option.bind_eq_bind, Option.bind_eq_some_iff,
              Prod.exists, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at parsed
            obtain ⟨clause, afterClause, hc, cs, tail, hs, rfl, rfl⟩ := parsed
            simp [clausesBits, parseClause_sound input clause afterClause hc,
              ih afterClause cs tail hs, List.append_assoc]

theorem decodeFormula_sound (input : List Bool) (formula : Formula)
    (parsed : decodeFormula input = some formula) : input = formulaBits formula := by
  simp only [decodeFormula, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Prod.exists, Option.ite_some_none_eq_some] at parsed
  obtain ⟨clauses, rest, h, rfl, rfl⟩ := parsed
  simpa only [formulaBits, List.append_nil] using
    parseClauses_sound (input.length + 1) input clauses [] h


end UniqueGamesTheorem.BinaryParsing

end

section

/-!
The ordinary binary 3SAT language includes exactly the successfully decoded
satisfiable formulas. A total semantic extension of occurrence-index renaming
maps malformed bitstrings to a fixed contradictory formula. Its runtime is a
separate machine-composition obligation; the size theorem below is only size.
-/

namespace UniqueGamesTheorem.BinaryLanguage

open UniqueGamesTheorem.Foundations

def rejectBinary : BinaryFormula.Formula where
  clauses := [#v[⟨0, true⟩, ⟨0, true⟩, ⟨0, true⟩],
    #v[⟨0, false⟩, ⟨0, false⟩, ⟨0, false⟩]]

theorem rejectBinary_unsatisfiable : ¬rejectBinary.Satisfiable := by
  rintro ⟨assignment, satisfied⟩
  have positive := satisfied #v[⟨0, true⟩, ⟨0, true⟩, ⟨0, true⟩]
    (by simp [rejectBinary])
  have negative := satisfied #v[⟨0, false⟩, ⟨0, false⟩, ⟨0, false⟩]
    (by simp [rejectBinary])
  cases h : assignment 0 <;>
    simp [BinaryFormula.Clause.eval, BinaryFormula.Literal.eval, h] at positive negative


def totalParsed (input : List Bool) : BinaryFormula.Formula :=
  (BinaryEncoding.decodeFormula input).getD rejectBinary

def totalRename (input : List Bool) : Target.Formula :=
  BinaryOccurrenceRename.renamed (totalParsed input)

theorem totalParsed_satisfiable_iff (input : List Bool) :
    (totalParsed input).Satisfiable ↔ language input := by
  cases parsed : BinaryEncoding.decodeFormula input with
  | none => simp [totalParsed, parsed, rejectBinary_unsatisfiable, language]
  | some formula => simp [totalParsed, parsed, language]

theorem totalRename_satisfiable_iff (input : List Bool) :
    (totalRename input).Satisfiable ↔ language input := by
  exact (BinaryOccurrenceRename.renamed_satisfiable_iff (totalParsed input)).trans
    (totalParsed_satisfiable_iff input)


end UniqueGamesTheorem.BinaryLanguage

end

end OAI
