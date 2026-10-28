import CCO.RawExact.FanDirectReferenceColour
import CCO.RawExact.FanDirectColourConsistency
import Lean.Elab.Tactic.Omega

/-!
# B002 C12: uniqueness of all typed root-spoke original atom labels

A root-spoke candidate comes from a genuine diversity step 0→1
of one particular RAW word occurrence, with the correct ORIGINAL
sort and genuine old atomic colour of that step. The same formal
spoke may be described by several independent occurrences ONLY
when they are all one-step paths to the same actual old centre.

The prior pairwise-ball atom equality then proves the full
sort-dependent candidate relation is FUNCTIONAL. This is the
key compatibility theorem for adding the formal root to the
already realized punctured private fan. There is no use of SAP,
a global Helly root, or a fabricated atomic palette.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- A genuine old original atomic colour that one private
RAW word occurrence prescribes on an oriented formal root spoke.
Every witness is a real certified source edge and the target
sort is precisely the formal vertex's named original sort. -/
def privateFanRootSpokeCandidate
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v : PrivateFanVertex S D centres)
    (a : S.Atom root (privateFanSort S D centres v)) : Prop :=
  ∃ (o : WordOccurrence S D)
    (q : PathPosition S (occurrenceWord S D o)),
    q.val = 1 ∧
    v = privateFanAtWordPosition S D centres o q ∧
    taggedColour S
      (referencePointAt S H D centres o
        (pathStart S (occurrenceWord S D o)))
      (referencePointAt S H D centres o q) =
      (⟨root, privateFanSort S D centres v, some a⟩ :
        Σ i : ι, Σ j : ι, Option (S.Atom i j))

/-- Even when multiple distinct menu indices or duplicate words
contribute the SAME formal root spoke, they prescribe only ONE
actual original atom. The equality is about the correctly TYPED
atom, not just sort names or an untyped relation fingerprint. -/
theorem privateFanRootSpokeCandidate_functional
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (hPair : ∀ p q : I,
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty)
    (v : PrivateFanVertex S D centres)
    (a b : S.Atom root (privateFanSort S D centres v))
    (ha : privateFanRootSpokeCandidate S H D centres v a)
    (hb : privateFanRootSpokeCandidate S H D centres v b) :
    a = b := by
  obtain ⟨o, q, hq, hv, hColour⟩ := ha
  obtain ⟨o', q', hq', hv', hColour'⟩ := hb
  have hpq : pathAdjacent S (occurrenceWord S D o)
      (pathStart S (occurrenceWord S D o)) q :=
    (pathAdjacent_start_iff S (occurrenceWord S D o) q).mpr hq
  have hpq' : pathAdjacent S (occurrenceWord S D o')
      (pathStart S (occurrenceWord S D o')) q' :=
    (pathAdjacent_start_iff S (occurrenceWord S D o') q').mpr hq'
  have hFirst : privateFanAtWordPosition S D centres o
      (pathStart S (occurrenceWord S D o)) =
      privateFanAtWordPosition S D centres o'
        (pathStart S (occurrenceWord S D o')) := by
    rw [privateFanAt_start S D centres o,
      privateFanAt_start S D centres o']
  have hSecond : privateFanAtWordPosition S D centres o q =
      privateFanAtWordPosition S D centres o' q' :=
    hv.symm.trans hv'
  have hFingerprints :
      taggedColour S
        (referencePointAt S H D centres o
          (pathStart S (occurrenceWord S D o)))
        (referencePointAt S H D centres o q) =
      taggedColour S
        (referencePointAt S H D centres o'
          (pathStart S (occurrenceWord S D o')))
        (referencePointAt S H D centres o' q') := by
    by_cases hSame : o = o'
    · subst o'
      have hPositions : q = q' :=
        privateFanAtWordPosition_injective S D centres o hSecond
      subst q'
      rfl
    · obtain ⟨hl, hl', hc⟩ :=
        privateFan_different_overlapping_edges_same_direct_spoke
          S D centres o o' hSame
          (pathStart S (occurrenceWord S D o)) q
          (pathStart S (occurrenceWord S D o')) q'
          hpq hpq' hFirst hSecond
      have hTagged : taggedCentre sort centres o.1 =
        taggedCentre sort centres o'.1 := by
        simpa only [toDistinctCentre] using congrArg Subtype.val hc
      have hFinish : q = pathFinish S (occurrenceWord S D o) := by
        apply Fin.ext
        change q.val = diversityLength S (occurrenceWord S D o)
        omega
      have hFinish' : q' = pathFinish S (occurrenceWord S D o') := by
        apply Fin.ext
        change q'.val = diversityLength S (occurrenceWord S D o')
        omega
      rw [hFinish, hFinish']
      exact reference_direct_forward_fingerprints_agree
        S H D centres hPair o o' hl hl' hTagged
  have hEncoded :
      (⟨root, privateFanSort S D centres v, some a⟩ :
        Σ i : ι, Σ j : ι, Option (S.Atom i j)) =
      (⟨root, privateFanSort S D centres v, some b⟩ :
        Σ i : ι, Σ j : ι, Option (S.Atom i j)) :=
    hColour.symm.trans (hFingerprints.trans hColour')
  simpa only [Sigma.mk.injEq, heq_eq_eq, true_and,
    Option.some.injEq] using hEncoded

end CCO.RawExact
