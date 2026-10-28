import CCO.RawExact.OccurrenceRealizations

/-!
# B002 C12: original real reference points at each private path index

Every genuine word occurrence has an actual old WordPath ending at its
prescribed old centre (chosen only as reference data). Its finite
vertex trace can therefore be indexed by exactly the same Fin
positions as the proved formal private path skeleton.

The source sort of the real point at each position is fixed by the
syntax of the typed RAW word. A different real path witness has the
same sort trace, even if its intermediate real points are different.
No ambient common root, Helly, SAP or quotient section is assumed.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- The original tagged point at a position on the independently
selected REAL reference path for one occurrence. -/
noncomputable def referencePointAt
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p : PathPosition S (occurrenceWord S D o)) : Sigma X := by
  let path := (referenceOccurrenceWalk S H D centres o).2
  exact (realWalkTrace S path).get
    ⟨p.val, by
      rw [realWalkTrace_length S path]
      exact p.isLt⟩

/-- The reference point's original named sort is literally the
corresponding position sort in the typed RAW word syntax. -/
theorem referencePointAt_sort
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p : PathPosition S (occurrenceWord S D o)) :
    (referencePointAt S H D centres o p).1 =
      pathSortAt S (occurrenceWord S D o) p := by
  let w := (referenceOccurrenceWalk S H D centres o).2
  have hsort : (realWalkTrace S w).map Sigma.fst =
      wordSortTrace S (occurrenceWord S D o) :=
    realWalkTrace_sorts S w
  have hRealLen : (realWalkTrace S w).length =
      diversityLength S (occurrenceWord S D o) + 1 :=
    realWalkTrace_length S w
  have hReal : p.val < (realWalkTrace S w).length := by
    rw [hRealLen]
    exact p.isLt
  have hSort : p.val <
      (wordSortTrace S (occurrenceWord S D o)).length := by
    rw [wordSortTrace_length S (occurrenceWord S D o)]
    exact p.isLt
  -- Use Nat-indexed optional lookup to rewrite the two lists without
  -- an ill-typed dependent rewrite of the Fin bound proof.
  have hNat :
      ((realWalkTrace S w).map Sigma.fst)[p.val]? =
      (wordSortTrace S (occurrenceWord S D o))[p.val]? :=
    congrArg (fun l : List ι => l[p.val]?) hsort
  have hAt :
      ((realWalkTrace S w)[p.val]'hReal).1 =
      (wordSortTrace S (occurrenceWord S D o))[p.val]'hSort := by
    rw [List.getElem?_eq_getElem (by
      simpa only [List.length_map] using hReal)] at hNat
    rw [List.getElem?_eq_getElem hSort] at hNat
    simpa only [List.getElem_map] using hNat
  simpa only [referencePointAt, pathSortAt, w] using hAt

end CCO.RawExact
