/- Modified 2026-10-09: AI-assisted proof simplification; see MODIFICATIONS.md. -/
import OAI.Computability.UniqueGames.Decoding.TableKeysGame
import OAI.Computability.UniqueGames.Reduction.EncodingLemmas
import OAI.Computability.UniqueGames.Reduction.RealTargetLemmas
import OAI.Computability.UniqueGames.Reduction.TableReduction

namespace OAI

section

/-!
Direct addresses for the v2 single-orbit matrix game. There is one canonical
body address space, with no side bit and no extra right-endpoint offset.
Unused addresses are isolated. Runtime construction uses canonical words and
radix arithmetic, not deduplication or inverse vertex enumeration.
-/

namespace UniqueGamesTheorem.Decoder.TableKeysAddressGame

open UniqueGamesTheorem.Reduction
open ActualSource Foundations.Target
open Integration.VertexEmbedding

abbrev vertexCount (S : Source) (k s d : Nat) : Nat :=
  CanonicalAddress.capacity S.variables S.occurrences k s d

def vertexAddress (S : Source) (k s d : Nat) (v : TableKeysGame.Vertex S k s d) :
    Fin (vertexCount S k s d) := CanonicalAddress.bodyAddress v.val

theorem vertexAddress_injective (S : Source) (k s d : Nat) :
    Function.Injective (vertexAddress S k s d) := by
  intro v w h
  apply Subtype.ext
  exact CanonicalAddress.bodyAddress_injective h

/-- Both endpoints use this same routine and this same address block. -/
def queryAddress (S : Source) (k s d : Nat) (q : TableKeysGame.Query S k s d) :
    Fin (vertexCount S k s d) :=
  CanonicalAddress.bodyAddress (ActualOrbit.body (TableKeysGame.canonical S k s d) q)

@[simp] theorem vertexAddress_query (S : Source) (k s d : Nat)
    (q : TableKeysGame.Query S k s d) :
    vertexAddress S k s d (TableKeysGame.vertex S k s d q) =
      queryAddress S k s d q := rfl

/-- This inverse is a proof adapter only; the output constructor never calls it. -/
def explicitToAddress (S : Source) (k s d : Nat) :
    Fin (TableKeysGame.explicitVertexCount S k s d) → Fin (vertexCount S k s d) :=
  fun i => vertexAddress S k s d ((TableKeysGame.explicitVertexEncoding S k s d).symm i)

theorem explicitToAddress_injective (S : Source) (k s d : Nat) :
    Function.Injective (explicitToAddress S k s d) :=
  (vertexAddress_injective S k s d).comp
    (TableKeysGame.explicitVertexEncoding S k s d).symm.injective

@[simp] theorem explicitToAddress_apply (S : Source) (k s d : Nat)
    (v : TableKeysGame.Vertex S k s d) :
    explicitToAddress S k s d (TableKeysGame.explicitVertexEncoding S k s d v) =
      vertexAddress S k s d v := by
  simp only [explicitToAddress, Equiv.symm_apply_apply]


def addressEdge (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : TableKeysGame.Outcome S k g) : Constraint (vertexCount S k s d) (2^s) where
  source := queryAddress S k s d (TableKeysGame.leftQuery S k g ω)
  target := queryAddress S k s d (TableKeysGame.rightQuery S k g ω)
  permutation := Encoding.translationTable
    (TableKeysGame.offset S k s d (TableKeysGame.leftQuery S k g ω))
    (TableKeysGame.offset S k s d (TableKeysGame.rightQuery S k g ω))

theorem addressEdge_eq_embed (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : TableKeysGame.Outcome S k g) :
    addressEdge S k g ω = embedConstraint (explicitToAddress S k s d)
      (TableKeysGame.explicitEdge S k g ω) := by
  simp only [addressEdge, embedConstraint, TableKeysGame.explicitEdge,
    explicitToAddress_apply, vertexAddress_query]


/-- The correcting function is not evaluated when producing an edge list. -/
def outputInstance (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (en : NoiseEnumeration g) : Instance (2^s) where
  vertices := vertexCount S k s d
  constraints := (ActualGame.explicitOutcomes S k g en).map (addressEdge S k g)
  nonempty h := by
    have hempty := List.map_eq_nil_iff.mp h
    apply (TableKeysGame.outputInstanceWithEnumeration S k g en).nonempty
    change (ActualGame.explicitOutcomes S k g en).map (TableKeysGame.explicitEdge S k g) = []
    rw [hempty]
    rfl


@[simp] theorem outputInstance_length (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (outputInstance S k g en).constraints.length =
      Explicit.edgeCount S.occurrences k (s+d) en.indices.length := by
  simp only [outputInstance, List.length_map, ActualGame.explicitOutcomes,
    ActualEnumeration.length_indexedOutcomes]

theorem outputInstance_count (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    countSatisfied labeling (outputInstance S k g en).constraints =
      countSatisfied (labeling ∘ explicitToAddress S k s d)
        (TableKeysGame.outputInstanceWithEnumeration S k g en).constraints := by
  simpa only [outputInstance, TableKeysGame.outputInstanceWithEnumeration, List.map_map,
    Function.comp_def, ← addressEdge_eq_embed] using
    count_map (explicitToAddress S k s d)
      ((ActualGame.explicitOutcomes S k g en).map (TableKeysGame.explicitEdge S k g)) labeling


theorem outputInstance_translations (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    Integration.TranslationTarget.IsTranslationInstance (Encoding.alphabetEquiv s).symm
      (outputInstance S k g en) := by
  intro constraint hconstraint
  obtain ⟨ω, _, rfl⟩ := List.mem_map.mp hconstraint
  refine ⟨TableKeysGame.offset S k s d (TableKeysGame.leftQuery S k g ω) +
    TableKeysGame.offset S k s d (TableKeysGame.rightQuery S k g ω), ?_⟩
  intro label
  have h := Encoding.translationTable_images
    (TableKeysGame.offset S k s d (TableKeysGame.leftQuery S k g ω))
    (TableKeysGame.offset S k s d (TableKeysGame.rightQuery S k g ω))
    ((Encoding.alphabetEquiv s).symm label)
  simpa only [addressEdge, Encoding.alphabetEquiv_apply_symm_apply,
    Encoding.alphabetEquiv_symm_apply_apply, add_assoc] using
    congrArg (Encoding.alphabetEquiv s).symm h

/-- Fixed finite noise data suffice for executable output. -/
def tableOutput (S : Source) (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d) :
    Instance (2^s) :=
  outputInstance S k (Integration.TableReduction.tableSkeleton T)
    (Integration.TableReduction.tableEnumeration T Prod.fst (fun _ _ => rfl))

/-- The nonlinear correctness witness is erased from the output program. -/
theorem tableOutput_eq_with_witness (S : Source) (k : Nat) {s d : Nat}
    (T : Integration.NoiseTables.Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c) :
    tableOutput S k T = outputInstance S k (T.gadget f hf)
      (Integration.TableReduction.tableEnumeration T f hf) := by
  rfl


theorem tableOutput_translations (S : Source) (k : Nat) {s d : Nat}
    (T : Integration.NoiseTables.Table s d) :
    Integration.TranslationTarget.IsTranslationInstance (Encoding.alphabetEquiv s).symm
      (tableOutput S k T) := outputInstance_translations S k _ _


end UniqueGamesTheorem.Decoder.TableKeysAddressGame

end

section

/-! Transport the matrix-test bound to the actual direct-address edge list.
Every address labeling restricts to a semantic orbit labeling, with exactly
the same satisfied fraction and the same occurrence multiplicities. -/

namespace UniqueGamesTheorem.Decoder.MatrixGap

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Integration
open ActualSource

noncomputable section

theorem address_rate_eq_semantic_acceptance (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g)
    (labeling : Fin (TableKeysAddressGame.vertexCount S k s d) → Fin (2 ^ s)) :
    GapSemantics.satisfactionRate (TableKeysAddressGame.outputInstance S k g en) labeling =
      TableKeysGame.acceptanceProbability S k g
        ((labeling ∘ TableKeysAddressGame.explicitToAddress S k s d) ∘
          TableKeysGame.semanticToExplicitVertices S k s d) := by
  calc
    _ = GapSemantics.satisfactionRate
        (TableKeysGame.outputInstanceWithEnumeration S k g en)
        (labeling ∘ TableKeysAddressGame.explicitToAddress S k s d) := by
      unfold GapSemantics.satisfactionRate
      exact congrArg₂ (fun a b : Nat => (a : ℚ) / b)
        (TableKeysAddressGame.outputInstance_count S k g en labeling)
        (by simp only [TableKeysAddressGame.outputInstance,
          TableKeysGame.outputInstanceWithEnumeration, List.length_map])
    _ = GapSemantics.satisfactionRate (TableKeysGame.outputInstance S k g)
        ((labeling ∘ TableKeysAddressGame.explicitToAddress S k s d) ∘
          TableKeysGame.semanticToExplicitVertices S k s d) :=
      InstanceEquivalences.satisfactionRate_eq_of_rename_perm
        (TableKeysGame.outputInstance S k g)
        (TableKeysGame.outputInstanceWithEnumeration S k g en)
        (TableKeysGame.semanticToExplicitVertices S k s d)
        (TableKeysGame.explicitConstraints_perm_renamed S k g en) _
    _ = _ := (TableKeysGame.acceptanceProbability_eq_count S k g _).symm

/-- Soundness is measured on the generated direct-address instance. Unused
addresses and reindexing introduce no additional labeling advantage. -/
theorem address_value_le_of_semantic_acceptance (S : Source) (k : Nat) {s d : Nat}
    (T : NoiseTables.Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c)
    (h : ∀ labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s),
      TableKeysGame.acceptanceProbability S k (T.gadget f hf) labeling ≤ (99 : ℚ) / 100) :
    InstanceValue.value (TableKeysAddressGame.tableOutput S k T) ≤ (99 : ℝ) / 100 := by
  rw [TableKeysAddressGame.tableOutput_eq_with_witness S k T f hf]
  apply (InstanceValue.forall_rate_le_iff _ (by positivity) _).mp
  intro labeling
  change (Fin (TableKeysAddressGame.vertexCount S k s d) → Fin (2 ^ s)) at labeling
  have hrate : GapSemantics.satisfactionRate
      (TableKeysAddressGame.outputInstance S k (T.gadget f hf)
        (TableReduction.tableEnumeration T f hf)) labeling ≤ (99 : ℚ) / 100 := by
    rw [address_rate_eq_semantic_acceptance S k (T.gadget f hf)
      (TableReduction.tableEnumeration T f hf) labeling]
    exact h _
  have hreal := (Rat.cast_le (K := ℝ)
    (p := GapSemantics.satisfactionRate
      (TableKeysAddressGame.outputInstance S k (T.gadget f hf)
        (TableReduction.tableEnumeration T f hf)) labeling)
    (q := (99 : ℚ) / 100)).2 hrate
  simpa [GapSemantics.satisfactionRate] using hreal

end

end UniqueGamesTheorem.Decoder.MatrixGap

end

end OAI
