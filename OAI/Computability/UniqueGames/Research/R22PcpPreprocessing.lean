import OAI.Computability.UniqueGames.PCP.CloudRoundingLemmas

namespace OAI.UniqueGamesTheorem.Foundations.PCP

/-- Complete relation tables are determined by their label-pair lookups. -/
theorem GraphTables.relation_ext {r s : GraphTables.RelationTable}
    (h : ∀ a b, GraphTables.relationAt r a b = GraphTables.relationAt s a b) : r = s := by
  apply Vector.ext
  intro i hi
  simpa only [GraphTables.relationAt, Prod.eta, Equiv.apply_symm_apply,
    Fin.getElem_fin] using
    h (GraphTables.relationIndex.symm ⟨i, hi⟩).1
      (GraphTables.relationIndex.symm ⟨i, hi⟩).2

/-- A stored row is determined by its tail, decoded reverse dart and predicate. -/
theorem PortTables.row_eq {n d : Nat} (table : PortTables.Table n d)
    (v : Fin n) (p : Fin d) (target : Fin n × Fin d) (relation : GraphTables.RelationTable)
    (hr : PortTables.rotation table (v, p) = target)
    (hp : ∀ a b, PortTables.accepts table (v, p) a b = GraphTables.relationAt relation a b) :
    (⟨v, table.reverseIndex[PortTables.rowIndex n d (v, p)],
      table.relations[PortTables.rowIndex n d (v, p)]⟩ : GraphTables.DartRow n (n * d)) =
      ⟨v, PortTables.rowIndex n d target, relation⟩ := by
  apply congrArg₂ (GraphTables.DartRow.mk v)
  · rw [← PortTables.rowIndex_rotation, hr]
  · exact GraphTables.relation_ext hp

/-- Proof fields of a constraint graph need no separate comparison. -/
theorem constraintGraph_ext {V E A : Type*} {G H : ConstraintGraph V E A}
    (hr : ∀ e, G.reverse e = H.reverse e) (ht : G.tail = H.tail)
    (hp : G.accepts = H.accepts) : G = H := by
  cases G
  cases H
  cases Equiv.ext hr
  cases ht
  cases hp
  rfl

end OAI.UniqueGamesTheorem.Foundations.PCP
