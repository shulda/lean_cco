import CCO.RawExact.FanRootSpokeExistence
import Mathlib.Tactic

/-!
# B002 C12: canonical selection of the unique real root-spoke atom

The root-spoke label relation has already been proved functional
under actual pairwise exact-ball intersections; existence on each
root incident edge uses only actual original reference-walk edges.

Therefore each root--vertex edge can be assigned its UNIQUE actual
atomic label, even when that edge is represented by several distinct
identity-bearing RAW word occurrences. The formal root itself has
no candidate: a true diversity edge never becomes a diagonal.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- The formal root cannot carry a root-to-itself diversity
atom under the actual private-path witness relation. -/
theorem privateFan_root_spoke_candidate_not_root
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (a : S.Atom root
      (privateFanSort S D centres (privateFanRoot S D centres))) :
    ¬ privateFanRootSpokeCandidate S H D centres
      (privateFanRoot S D centres) a := by
  rintro ⟨o, q, hq, hv, _⟩
  have hStart : q = pathStart S (occurrenceWord S D o) :=
    (privateFanAt_is_root_iff_start S D centres o q).mp hv.symm
  have hVal := congrArg Fin.val hStart
  change q.val = 0 at hVal
  omega

/-- A root-spoke candidate only comes from a genuine edge of
the finite fan; selecting a label creates no artificial edge. -/
theorem privateFan_root_spoke_candidate_implies_adjacent
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v : PrivateFanVertex S D centres)
    (a : S.Atom root (privateFanSort S D centres v))
    (h : privateFanRootSpokeCandidate S H D centres v a) :
    privateFanAdjacent S D centres
      (privateFanRoot S D centres) v := by
  obtain ⟨o, q, hq, hv, _⟩ := h
  have hStep : pathAdjacent S (occurrenceWord S D o)
      (pathStart S (occurrenceWord S D o)) q :=
    (pathAdjacent_start_iff S (occurrenceWord S D o) q).mpr hq
  have hGraph := privateFan_path_edge S D centres o
    (pathStart S (occurrenceWord S D o)) q hStep
  rw [privateFanAt_start S D centres o] at hGraph
  rw [hv]
  exact hGraph

/-- A unique genuine original atomic label can be selected
locally at any formal neighbour of the root. A missing root
edge has value `none`, not a fake logical identity atom. -/
noncomputable def privateFanRootSelectedAtom
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v : PrivateFanVertex S D centres) :
    Option (S.Atom root (privateFanSort S D centres v)) := by
  classical
  exact if h : ∃ a, privateFanRootSpokeCandidate S H D centres v a then
    some (Classical.choose h)
  else
    none

/-- Selected root atoms are EXACTLY the original real candidates,
with a single value even when direct spokes are duplicated. -/
theorem privateFanRootSelectedAtom_some_iff
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
    (a : S.Atom root (privateFanSort S D centres v)) :
    privateFanRootSelectedAtom S H D centres v = some a ↔
      privateFanRootSpokeCandidate S H D centres v a := by
  classical
  unfold privateFanRootSelectedAtom
  by_cases h : ∃ b, privateFanRootSpokeCandidate S H D centres v b
  · rw [dif_pos h]
    constructor
    · intro heq
      have hab : Classical.choose h = a := Option.some.inj heq
      rw [← hab]
      exact Classical.choose_spec h
    · intro ha
      have hab : Classical.choose h = a :=
        privateFanRootSpokeCandidate_functional S H D centres
          hPair v (Classical.choose h) a
          (Classical.choose_spec h) ha
      rw [hab]
  · rw [dif_neg h]
    constructor
    · intro heq
      cases heq
    · intro ha
      exact False.elim (h ⟨a, ha⟩)

/-- Exactly the actual fan's formal root-neighbours have
a selected true old atomic colour. This combines the proved
root-incidence witness and unique-colour selection, not CCO. -/
theorem privateFanRootSelectedAtom_ne_none_iff
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v : PrivateFanVertex S D centres) :
    privateFanRootSelectedAtom S H D centres v ≠ none ↔
      privateFanAdjacent S D centres
        (privateFanRoot S D centres) v := by
  classical
  constructor
  · intro hSome
    by_cases hExists :
        ∃ a, privateFanRootSpokeCandidate S H D centres v a
    · obtain ⟨a, ha⟩ := hExists
      exact privateFan_root_spoke_candidate_implies_adjacent
        S H D centres v a ha
    · have hNone : privateFanRootSelectedAtom S H D centres v = none := by
        unfold privateFanRootSelectedAtom
        simp [hExists]
      exact False.elim (hSome hNone)
  · intro hGraph
    obtain ⟨a, ha⟩ :=
      privateFan_root_spoke_candidate_exists S H D centres v hGraph
    have hExists :
        ∃ b, privateFanRootSpokeCandidate S H D centres v b :=
      ⟨a, ha⟩
    unfold privateFanRootSelectedAtom
    simp [hExists]

end CCO.RawExact
