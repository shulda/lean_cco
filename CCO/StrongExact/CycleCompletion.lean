import CCO.Injectivization

/-!
# STRONG C06: specified-cycle criterion for injective completions

The source `SemanticCCO` interface promises only a (possibly colliding)
homomorphism. The accepted B001 SAP injectivization makes *all* formal
vertices distinct, retaining every specified diversity edge. In particular
this theorem is about genuine three-distinct-real-vertex STRONG edges, not
the equality-inclusive RAW represented multiplication.

No new gluing, completion, or automorphism provider is postulated here.
-/

universe u v w z

namespace CCO

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u, v, w} ι X} {V : Type z}

/-- An actual injective realization of the whole finite specified diversity
diagram, giving an induced complete old source diagram on its distinct image
vertices. No artificial equality atom is introduced. -/
def PartialDiagram.HasStrongCompletion (D : PartialDiagram S V) : Prop :=
  ∃ f : DiagramHom D, f.IsInjective

/-- Restrict an actual diagram homomorphism to any specified simple cycle.
Injectivity is not needed for this direction. -/
theorem DiagramHom.cycleHom (D : PartialDiagram S V)
    (f : DiagramHom D) (C : SimpleCycle D) : CycleHom C := by
  refine ⟨(fun p => f.point (C.vertices p)), ?_⟩
  intro p a ha
  exact f.preserves_edge
    (C.vertices p) (C.vertices (cyclicNext C.length_pos p))
    (C.next_ne p) a ha

/-- STRONG C06, cycle criterion: homomorphic semantic CCO plus real-source
homogeneity and SAP imply injective completion. Conversely any such
completion provides a homomorphism of every specified simple cycle.
The finite diagram may repeat named sorts arbitrarily. -/
theorem PartialDiagram.strongCompletion_iff_cycles_of_SAP_CCO
    {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u, v, w, z} S) (D : PartialDiagram S V) :
    D.HasStrongCompletion ↔ ∀ C : SimpleCycle D, CycleHom C := by
  constructor
  · rintro ⟨f, _⟩ C
    exact DiagramHom.cycleHom D f C
  · intro hCycles
    obtain ⟨f⟩ := cco V D hCycles
    obtain ⟨f', hf', _, _⟩ :=
      DiagramHom.injectivize_of_SAP H sap f
        (∅ : Set V) (by simp)
        (∅ : Set (Sigma X)) Set.finite_empty
    exact ⟨f', hf'⟩

/-- The injectivization refinement can pin a pre-aligned complete old base.
This is deliberately stronger than merely retaining the colours of the base:
every displayed pinned vertex stays at its **literal** prescribed real point.
Alignment of a different prescribed copy uses `HomogeneousSource` separately. -/
theorem PartialDiagram.strongCompletion_fixed_base_of_SAP
    {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (D : PartialDiagram S V) (f : DiagramHom D)
    (base : Set V)
    (hbase : ∀ u ∈ base, ∀ v ∈ base, f.image u = f.image v → u = v) :
    ∃ f' : DiagramHom D, f'.IsInjective ∧
      ∀ x ∈ base, f'.image x = f.image x := by
  obtain ⟨f', hf', hfixed, _⟩ :=
    DiagramHom.injectivize_of_SAP H sap f
      base hbase (∅ : Set (Sigma X)) Set.finite_empty
  exact ⟨f', hf', hfixed⟩

end CCO
