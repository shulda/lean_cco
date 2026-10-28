import CCO.RawExact.RealTraceEndpoints
import CCO.RawExact.ReducedDirectWords
import Mathlib.Tactic

/-!
# B002 C12: actual original atomic fingerprints on direct private spokes

A reduced one-step RAW word may have arbitrarily many genuine
identity letters. Its reference walk nevertheless has the same
literal original atomic endpoint colour as the one-atom relation
it represents. The full dependent tagged colour fingerprint
remains identical on duplicate direct edges at the same ACTUAL
old centre, even when the reference roots were chosen separately.

This is the precise transport required to label a merged edge
independently of which occurrence supplies its reference walk.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

def forwardRequestFingerprint {root : ι}
    (r : AtomicBallRequest S root) :
    Σ i : ι, Σ j : ι, Option (S.Atom i j) :=
  ⟨root, r.1.1, some r.2⟩

def reverseRequestFingerprint {root : ι}
    (r : AtomicBallRequest S root) :
    Σ i : ι, Σ j : ι, Option (S.Atom i j) :=
  ⟨r.1.1, root, some (S.conv r.2)⟩

/-- An occurrence's independently selected reference root is an
ACTUAL realization of its represented RAW word with its literal
old centre as endpoint. In the one-step case that endpoint pair
has precisely the chosen old atom, not an approximate colour. -/
theorem reference_one_step_old_atom
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (a : S.Atom root (sort o.1))
    (ha : RawWord.relation S (occurrenceWord S D o) = S.atomRel a) :
    S.colour (referenceOccurrenceWalk S H D centres o).1
      (centres o.1) = some a := by
  have hw : RawWord.relation S (occurrenceWord S D o)
      (referenceOccurrenceWalk S H D centres o).1 (centres o.1) :=
    (wordPath_iff_relation S (occurrenceWord S D o)
      (referenceOccurrenceWalk S H D centres o).1
      (centres o.1)).mp
        ⟨(referenceOccurrenceWalk S H D centres o).2⟩
  rw [ha] at hw
  exact hw

/-- Full dependent sort-tagged colour of the first to last
reference edge of a one-step private word, forward orientation. -/
theorem reference_one_step_forward_fingerprint
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (a : S.Atom root (sort o.1))
    (ha : RawWord.relation S (occurrenceWord S D o) = S.atomRel a) :
    taggedColour S
      (referencePointAt S H D centres o
        (pathStart S (occurrenceWord S D o)))
      (referencePointAt S H D centres o
        (pathFinish S (occurrenceWord S D o))) =
      forwardRequestFingerprint S
        (⟨taggedCentre sort centres o.1, a⟩ : AtomicBallRequest S root) := by
  have hColour := reference_one_step_old_atom S H D centres o a ha
  rw [referencePointAt_start_value S H D centres o,
    referencePointAt_finish_value S H D centres o]
  change (⟨root, sort o.1,
    S.colour (referenceOccurrenceWalk S H D centres o).1
      (centres o.1)⟩ :
        Σ i : ι, Σ j : ι, Option (S.Atom i j)) =
    ⟨root, sort o.1, some a⟩
  rw [hColour]

/-- The same fingerprint on the reversed formal direct spoke
uses only the TRUE original typed converse atom. -/
theorem reference_one_step_reverse_fingerprint
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (a : S.Atom root (sort o.1))
    (ha : RawWord.relation S (occurrenceWord S D o) = S.atomRel a) :
    taggedColour S
      (referencePointAt S H D centres o
        (pathFinish S (occurrenceWord S D o)))
      (referencePointAt S H D centres o
        (pathStart S (occurrenceWord S D o))) =
      reverseRequestFingerprint S
        (⟨taggedCentre sort centres o.1, a⟩ : AtomicBallRequest S root) := by
  have hColour := reference_one_step_old_atom S H D centres o a ha
  have hReverse : S.colour (centres o.1)
      (referenceOccurrenceWalk S H D centres o).1 =
      some (S.conv a) :=
    (S.colour_swap _ _ a).mp hColour
  rw [referencePointAt_finish_value S H D centres o,
    referencePointAt_start_value S H D centres o]
  change (⟨sort o.1, root,
    S.colour (centres o.1)
      (referenceOccurrenceWalk S H D centres o).1⟩ :
        Σ i : ι, Σ j : ι, Option (S.Atom i j)) =
    ⟨sort o.1, root, some (S.conv a)⟩
  rw [hReverse]

/-- Two direct one-edge word occurrences ending at the same tagged
actual centre have equal FULL original edge-colour fingerprints,
even though their chosen reference roots may be different. -/
theorem reference_direct_forward_fingerprints_agree
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (hPair : ∀ p q : I,
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty)
    (o o' : WordOccurrence S D)
    (hLength : diversityLength S (occurrenceWord S D o) = 1)
    (hLength' : diversityLength S (occurrenceWord S D o') = 1)
    (hCentre : taggedCentre sort centres o.1 =
      taggedCentre sort centres o'.1) :
    taggedColour S
      (referencePointAt S H D centres o
        (pathStart S (occurrenceWord S D o)))
      (referencePointAt S H D centres o
        (pathFinish S (occurrenceWord S D o))) =
    taggedColour S
      (referencePointAt S H D centres o'
        (pathStart S (occurrenceWord S D o')))
      (referencePointAt S H D centres o'
        (pathFinish S (occurrenceWord S D o'))) := by
  obtain ⟨a, b, ha, hb, hReq⟩ :=
    duplicate_reduced_direct_edges_agree S sort D centres
      hPair o o' hLength hLength' hCentre
  rw [reference_one_step_forward_fingerprint S H D centres o a ha,
    reference_one_step_forward_fingerprint S H D centres o' b hb]
  exact congrArg (forwardRequestFingerprint S) hReq

end CCO.RawExact
