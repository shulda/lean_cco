import CCO.RawExact.CanonicalQuotientExpansion
import CCO.RawExact.QuotientExpansionCycleWitnesses
import CCO.RawExact.DiagramReindex

/-!
# Source CCO for the actual canonical finite quotient family

The actual source supplies its full-exact menus, their positivity, and
its surjective real projections. Every raw expansion cycle is realised
by the proved two-mark/multi-mark bridge. Applying the original CCO and
projecting the completed expansion discharges C27 without a quotient
cycle, menu, positivity, or representation provider.
-/

universe v w t z

namespace CCO.RawExact.CanonicalQuotients

variable {A : Type v}
variable (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable {family : Finset (Setoid A)} (E : ExactData S family)

include cco

/-- Every actual finite ordinal quotient diagram satisfying the genuine
specified simple-cycle premise has a homomorphic completion. -/
theorem semanticCCO_fin (n : Nat)
    (D : PartialDiagram (source S H E) (Fin n))
    (hCycles : ∀ C : SimpleCycle D, CycleHom C) :
    Nonempty (DiagramHom D) := by
  classical
  let P := CanonicalQuotientExpansion.menus S H cco E D
  have hNonempty := CanonicalQuotientExpansion.menus_nonempty S H cco E D
  have hRaw := QuotientExpansion.all_raw_cycles_of_typed_cycles
    S (source S H E) D P hNonempty projection projection_surjective
    (CanonicalQuotientExpansion.occurrence_specified S H cco E D)
    (CanonicalQuotientExpansion.menus_represents S H cco E D)
    (CanonicalQuotientExpansion.menus_positive S H cco E D) hCycles
  obtain ⟨f⟩ := (semanticCCO_change_universe S cco) _
    (QuotientExpansion.diagram S (fun _ => ()) P hNonempty) hRaw
  exact ⟨CanonicalQuotientExpansion.project_completed S H cco E D f⟩

/-- Genuine semantic CCO inherited by the finite named family of actual
full-exact quotients of one original source sort. Vertex types are
arbitrary finite types in any universe; no stronger source premise or
countability assumption is used. -/
theorem semanticCCO : SemanticCCO.{_,_,z,_} (source S H E) :=
  semanticCCO_of_fin (source S H E) (semanticCCO_fin S H cco E)

end CCO.RawExact.CanonicalQuotients
