/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.PCP.ClauseVerifierLemmas

namespace OAI

section

/-!
An explicit name compaction for finite three-literal CNF formulas. Only the
occurring names are scanned: the declared variable count is never enumerated.
Both assignment transports preserve every clause evaluation and therefore
every finite clause-score gap. The encoding bound is a size theorem; a machine
running-time bound and the constant-gap PCP construction remain separate.
-/

namespace UniqueGamesTheorem.Foundations.PCP.NameCompaction

open UniqueGamesTheorem.Foundations.Target

def clauseNames {n : Nat} (clause : Clause n) : List (Fin n) :=
  [clause[0].variableIndex, clause[1].variableIndex, clause[2].variableIndex]

def sourceNames (F : Formula) : List (Fin F.variables) :=
  F.clauses.flatMap clauseNames

def activeNames (F : Formula) : List (Fin F.variables) :=
  (sourceNames F).eraseDups

theorem literal_mem_active (F : Formula) (clause : Clause F.variables)
    (hc : clause ∈ F.clauses) (i : Fin 3) :
    clause[i].variableIndex ∈ activeNames F := by
  simp only [activeNames, List.mem_eraseDups]
  apply List.mem_flatMap.mpr
  refine ⟨clause, hc, ?_⟩
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> simp [clauseNames]

def compactIndex (F : Formula) (v : Fin F.variables)
    (hv : v ∈ activeNames F) : Fin (activeNames F).length :=
  ⟨(activeNames F).idxOf v, List.idxOf_lt_length_iff.mpr hv⟩

def decodeName (F : Formula) (v : Fin (activeNames F).length) : Fin F.variables :=
  (activeNames F)[v.val]

def compactLiteral (F : Formula) (l : Literal F.variables)
    (hl : l.variableIndex ∈ activeNames F) : Literal (activeNames F).length :=
  ⟨compactIndex F l.variableIndex hl, l.positive⟩

def compactClause (F : Formula) (clause : Clause F.variables)
    (hc : clause ∈ F.clauses) : Clause (activeNames F).length :=
  #v[compactLiteral F clause[0] (literal_mem_active F clause hc 0),
    compactLiteral F clause[1] (literal_mem_active F clause hc 1),
    compactLiteral F clause[2] (literal_mem_active F clause hc 2)]

def compactClauses (F : Formula) : List (Clause (activeNames F).length) :=
  F.clauses.attach.map (fun c => compactClause F c.val c.property)

def compact (F : Formula) : Formula where
  «variables» := (activeNames F).length
  clauses := compactClauses F

def restrictAssignment (F : Formula) (A : Fin F.variables → Bool) :
    Fin (activeNames F).length → Bool := fun v => A (decodeName F v)

def extendAssignment (F : Formula) (B : Fin (activeNames F).length → Bool)
    (v : Fin F.variables) : Bool :=
  if hv : v ∈ activeNames F then B (compactIndex F v hv) else false

@[simp] theorem decode_compactIndex (F : Formula) (v : Fin F.variables)
    (hv : v ∈ activeNames F) : decodeName F (compactIndex F v hv) = v := by
  exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hv)

@[simp] theorem eval_compact_restrict (F : Formula) (c : Clause F.variables)
    (hc : c ∈ F.clauses) (A : Fin F.variables → Bool) :
    (compactClause F c hc).eval (restrictAssignment F A) = c.eval A := by
  simp [compactClause, compactLiteral, Clause.eval, Literal.eval,
    restrictAssignment, decode_compactIndex]

@[simp] theorem eval_compact_extend (F : Formula) (clause : Clause F.variables)
    (hc : clause ∈ F.clauses) (B : Fin (activeNames F).length → Bool) :
    (compactClause F clause hc).eval B = clause.eval (extendAssignment F B) := by
  have h₀ : clause[0].variableIndex ∈ activeNames F := literal_mem_active F clause hc 0
  have h₁ : clause[1].variableIndex ∈ activeNames F := literal_mem_active F clause hc 1
  have h₂ : clause[2].variableIndex ∈ activeNames F := literal_mem_active F clause hc 2
  simp [compactClause, compactLiteral, Clause.eval, Literal.eval, extendAssignment,
    h₀, h₁, h₂]
  rfl

theorem map_attach_val {α β : Type} (xs : List α) (f : α → β) :
    xs.attach.map (fun x => f x.val) = xs.map f := by
  exact List.attach_map_val

def evaluationList (F : Formula) (A : Fin F.variables → Bool) : List Bool :=
  F.clauses.map (fun c => c.eval A)


def failedCount (F : Formula) (A : Fin F.variables → Bool) : Nat :=
  (evaluationList F A).count false

theorem evaluationList_restrict (F : Formula) (A : Fin F.variables → Bool) :
    evaluationList (compact F) (restrictAssignment F A) = evaluationList F A := by
  simp only [evaluationList, compact, compactClauses, List.map_map]
  simpa only [Function.comp_def, eval_compact_restrict] using
    map_attach_val F.clauses (fun c => c.eval A)

theorem evaluationList_extend (F : Formula) (B : Fin (compact F).variables → Bool) :
    evaluationList (compact F) B = evaluationList F (extendAssignment F B) := by
  simp only [evaluationList, compact, compactClauses, List.map_map]
  change F.clauses.attach.map (fun c => (compactClause F c.val c.property).eval B) = _
  calc
    _ = F.clauses.attach.map (fun c => c.val.eval (extendAssignment F B)) := by
      apply List.map_congr_left
      intro c _
      exact eval_compact_extend F c.val c.property B
    _ = _ := map_attach_val F.clauses (fun c => c.eval (extendAssignment F B))


theorem failedCount_restrict (F : Formula) (A : Fin F.variables → Bool) :
    failedCount (compact F) (restrictAssignment F A) = failedCount F A := by
  simp only [failedCount, evaluationList_restrict]


theorem failedCount_extend (F : Formula) (B : Fin (compact F).variables → Bool) :
    failedCount (compact F) B = failedCount F (extendAssignment F B) := by
  simp only [failedCount, evaluationList_extend]

theorem clauseNames_flat_length {n : Nat} (cs : List (Clause n)) :
    (cs.flatMap clauseNames).length = 3 * cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, clauseNames,
      List.length_cons, List.length_nil, ih]
    omega


theorem length_eraseDups_le {α : Type} [BEq α] (xs : List α) :
    xs.eraseDups.length ≤ xs.length := by
  match xs with
  | [] => simp
  | a :: rest =>
    rw [List.eraseDups_cons]
    have filtered := List.length_filter_le (fun b => !(b == a)) rest
    have ih := length_eraseDups_le (rest.filter (fun b => !(b == a)))
    simp only [List.length_cons]
    omega
termination_by xs.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)


theorem failureCount_evaluations (F : Formula) (A : Fin F.variables → Bool)
    (indices : List (Fin F.clauses.length)) :
    failureCount F A indices =
      (indices.map (fun i => (clauseAt F i).eval A)).count false := by
  induction indices with
  | nil => simp [failureCount]
  | cons i rest ih =>
    cases h : (clauseAt F i).eval A <;>
      simp [failureCount, clauseFailure, h, ih, Nat.add_comm]

theorem evaluations_allIndices (F : Formula) (A : Fin F.variables → Bool) :
    ((allIndices F).map (fun i => (clauseAt F i).eval A)) = evaluationList F A := by
  calc
    _ = (List.ofFn (fun i : Fin F.clauses.length => F.clauses[i.val])).map
        (fun c => c.eval A) := by
      simp only [allIndices, List.finRange, clauseAt, List.map_ofFn, Function.comp_def]
    _ = _ := by rw [List.ofFn_getElem]; rfl

/-- The semantic score is the checked verifier's actual failed-clause count. -/
theorem verifier_failureCount (F : Formula) (A : Fin F.variables → Bool) :
    failureCount F A (allIndices F) = failedCount F A := by
  rw [failureCount_evaluations, evaluations_allIndices]
  rfl


end UniqueGamesTheorem.Foundations.PCP.NameCompaction

end

end OAI
