import CCO.RawExact.WordOccurrences
import CCO.RawExact.LabelledRealTrace

/-!
# B002 C12: genuine private-path reference witnesses at every real centre

A full-exact relation is an intersection of actual represented RAW
words. Original-sort transitivity makes its ball nonempty at EVERY
actual centre. Each word occurrence therefore has a real WordPath
whose right endpoint is that literal centre. The chosen witness
is only used to instantiate the graph's original atomic labels:
it is not assumed to be injective, to have a common root for
different occurrences, or to be a quotient section.

Pairwise-compatible witnesses with one common root for cycles are
already provided separately by WordOccurrences.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Every actual occurrence has a correctly typed real walk to its
literal centre. No CCO, SAP, quotient homogeneity or exact Helly is
needed to choose this one path: only the original homogeneous source. -/
theorem occurrence_realizable_at_centre
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D) :
    Nonempty (Σ x : X root,
      WordPath S (occurrenceWord S D o) x (centres o.1)) := by
  have hInv : TRel.Invariant (G := G)
      (evaluate S (D o.1).words) :=
    presentation_invariant_of_homogeneous S H (D o.1).words
  obtain ⟨x, hx⟩ :=
    S.raw_coserial_of_homogeneous H
      (evaluate S (D o.1).words) (D o.1).nonempty
      hInv (centres o.1)
  have hw : RawWord.relation S (occurrenceWord S D o)
      x (centres o.1) :=
    occurrenceWord_of_ball S D centres o x hx
  obtain ⟨path⟩ :=
    (wordPath_iff_relation S (occurrenceWord S D o)
      x (centres o.1)).mpr hw
  exact ⟨⟨x, path⟩⟩

/-- Fix an independently selected reference walk for each actual
occurrence; it has no globally shared-root property. The latter
would be the desired Helly conclusion and must not be assumed. -/
noncomputable def referenceOccurrenceWalk
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D) :
    Σ x : X root,
      WordPath S (occurrenceWord S D o) x (centres o.1) :=
  Classical.choice (occurrence_realizable_at_centre S H D centres o)

/-- Each selected reference walk is certified using its REAL original
atomic colours. Equality letters introduce no edge, and a positive
walk is still permitted to have an identity OUTPUT pair. -/
theorem referenceOccurrenceWalk_certified
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D) :
    TypedWalkCertificate S
      (realWalkTrace S (referenceOccurrenceWalk S H D centres o).2)
      (rawAtomicSteps S (occurrenceWord S D o)) :=
  realWalkTrace_certified S
    (referenceOccurrenceWalk S H D centres o).2

end CCO.RawExact
