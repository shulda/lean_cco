import CCO.RawExact.ReferencePositions
import CCO.RawExact.RealTrace
import Mathlib.Tactic

/-!
# B002 C12: actual endpoints of independently selected real RAW walks

The first and last entries of a realized RAW word's diversity trace
are its literal source and target old real points. This holds for
identity-bearing words and for positive words whose two actual
endpoints happen to coincide. Consequently, the reference finite
position at each occurrence's finish is precisely its prescribed
original tagged centre, not a separately chosen abstract lift.

These equalities are necessary for identifying old-centre/word-path
edge colours in the eventual single labelled private fan diagram.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- The first real vertex of the RAW diversity trace is exactly
the supplied original starting point, even after identity erasure. -/
theorem realWalkTrace_first_tagged {i j : ι}
    {word : RawWord S i j} {x : X i} {y : X j}
    (path : WordPath S word x y) :
    (realWalkTrace S path)[0]? = some (⟨i, x⟩ : Sigma X) := by
  obtain ⟨tail, hTrace⟩ := realWalkTrace_cons S path
  rw [hTrace]
  rfl

/-- The last real vertex of any represented RAW word is the
LITERAL designated endpoint. In particular a positive loop
may end at its own start; no diversity identity is asserted. -/
theorem realWalkTrace_last_tagged {i j : ι}
    {word : RawWord S i j} {x : X i} {y : X j}
    (path : WordPath S word x y) :
    (realWalkTrace S path)[diversityLength S word]? =
      some (⟨j, y⟩ : Sigma X) := by
  induction path with
  | nil x =>
      rfl
  | identity tail ih =>
      exact ih
  | atom a edge rest ih =>
      change (realWalkTrace S rest)[diversityLength S _]? =
        some (⟨_, _⟩ : Sigma X)
      exact ih

/-- The first finite formal position of the reference walk is
its independently chosen actual old root. -/
theorem referencePointAt_start_value
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D) :
    referencePointAt S H D centres o
      (pathStart S (occurrenceWord S D o)) =
        (⟨root, (referenceOccurrenceWalk S H D centres o).1⟩ : Sigma X) := by
  let path := (referenceOccurrenceWalk S H D centres o).2
  have hFirst := realWalkTrace_first_tagged S path
  have hBound : 0 < (realWalkTrace S path).length := by
    rw [realWalkTrace_length S path]
    omega
  rw [List.getElem?_eq_getElem hBound] at hFirst
  have hAt := Option.some.inj hFirst
  simpa only [referencePointAt, pathStart, List.get_eq_getElem] using hAt

/-- At the final formal position of EVERY private word occurrence,
its selected reference point is literally the given old tagged
centre. This also covers repeated centres and identity-only words. -/
theorem referencePointAt_finish_value
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D) :
    referencePointAt S H D centres o
      (pathFinish S (occurrenceWord S D o)) =
        taggedCentre sort centres o.1 := by
  let path := (referenceOccurrenceWalk S H D centres o).2
  have hLast := realWalkTrace_last_tagged S path
  have hBound : diversityLength S (occurrenceWord S D o) <
      (realWalkTrace S path).length := by
    rw [realWalkTrace_length S path]
    omega
  rw [List.getElem?_eq_getElem hBound] at hLast
  have hAt := Option.some.inj hLast
  simpa only [referencePointAt, pathFinish, List.get_eq_getElem,
    taggedCentre] using hAt

end CCO.RawExact
