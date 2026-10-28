import CCO.RawExact.FanRootSpokeUniqueness
import CCO.RawExact.FanRootIncidence
import CCO.RawExact.FanReferenceEdges
import Lean.Elab.Tactic.Omega

/-!
# B002 C12: every genuine formal root spoke has an old atomic label

The previously constructed root-spoke candidate relation is proved
functional (under the actual pairwise exact-ball intersection input).
Here we independently prove existence of a candidate for EVERY
genuine formal graph edge from the root, by selecting the first
diversity step of an original represented reference RAW walk.

The candidate atom is transported to the exact original sort of
the formal neighbour, not chosen from a hypothetical table.
No SAP, CCO completion or global exact-ball Helly is assumed.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Move a genuine actual atomic source edge across equality
of the original named sort tags. The output retains the whole
dependent tagged pair-colour fingerprint. -/
theorem genuineEdge_tagged_some_at_sorts
    (p q : Sigma X) (i j : ι)
    (hi : p.1 = i) (hj : q.1 = j)
    (h : GenuineEdge S p q) :
    ∃ a : S.Atom i j,
      taggedColour S p q =
        (⟨i, j, some a⟩ :
          Σ r : ι, Σ s : ι, Option (S.Atom r s)) := by
  rcases p with ⟨pi, x⟩
  rcases q with ⟨qj, y⟩
  change pi = i at hi
  change qj = j at hj
  subst pi
  subst qj
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  change (⟨i, j, S.colour x y⟩ :
    Σ r : ι, Σ s : ι, Option (S.Atom r s)) =
      ⟨i, j, some a⟩
  rw [ha]

/-- Every formal nonloop root edge of the actual private fan
has at least one genuinely old coloured source witness. Unlike
uniqueness, this needs no pairwise ball hypothesis at all. -/
theorem privateFan_root_spoke_candidate_exists
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v : PrivateFanVertex S D centres)
    (hAdj : privateFanAdjacent S D centres
      (privateFanRoot S D centres) v) :
    ∃ a : S.Atom root (privateFanSort S D centres v),
      privateFanRootSpokeCandidate S H D centres v a := by
  obtain ⟨o, q, hq, hv⟩ :=
    privateFan_root_edges_are_first_steps S D centres v hAdj
  let word := occurrenceWord S D o
  let first := pathStart S word
  have hStep : first.val + 1 = q.val := by
    change 0 + 1 = q.val
    omega
  have hGenuine : GenuineEdge S
      (referencePointAt S H D centres o first)
      (referencePointAt S H D centres o q) :=
    referencePointAt_genuine_forward S H D centres
      o first q hStep
  have hRootSort :
      (referencePointAt S H D centres o first).1 = root := by
    calc
      (referencePointAt S H D centres o first).1 =
          pathSortAt S word first :=
        referencePointAt_sort S H D centres o first
      _ = root := pathSortAt_start S word
  have hNeighbourSort :
      (referencePointAt S H D centres o q).1 =
        privateFanSort S D centres v := by
    calc
      (referencePointAt S H D centres o q).1 =
          pathSortAt S word q :=
        referencePointAt_sort S H D centres o q
      _ = privateFanSort S D centres
            (privateFanAtWordPosition S D centres o q) :=
        (privateFanAtWordPosition_sort S D centres o q).symm
      _ = privateFanSort S D centres v := by rw [hv]
  obtain ⟨a, ha⟩ :=
    genuineEdge_tagged_some_at_sorts S
      (referencePointAt S H D centres o first)
      (referencePointAt S H D centres o q)
      root (privateFanSort S D centres v)
      hRootSort hNeighbourSort hGenuine
  refine ⟨a, o, q, hq, hv, ?_⟩
  simpa only [first, word] using ha

end CCO.RawExact
