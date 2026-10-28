import CCO.RawExact.FanReferenceEdges
import CCO.RawExact.RealTraceEndpoints
import CCO.RawExact.FanTerminalIncidence
import Mathlib.Tactic

/-!
# B002 C12: genuine old realization of the private fan *minus its root*

Each private RAW word occurrence has a chosen independent actual
reference walk ending at its literal old marked centre. Its inner
vertices can therefore be realized by the corresponding old points.
All old marked centres retain their literal original points.

An arbitrary placeholder is assigned at the ONE formal root only to
obtain a total dependent function. The theorem does NOT claim this
placeholder satisfies ANY root-incident path edge; constructing a
common satisfying root is precisely the unproved C13 conclusion.

Every edge not incident to the formal root already has a genuine
old-real atomic realization. This observation substantially reduces
the required global edge-colouring/gluing step to the root spokes.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- The actual ORIGINAL old reference point at each private fan
vertex. Only the formal root receives an arbitrary placeholder;
other points are the literal old centre or private walk witness. -/
noncomputable def privateFanNonrootReference
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t)) :
    PrivateFanVertex S D centres → Sigma X
  | .inl none => ⟨root, Classical.choice (S.nonemptySort root)⟩
  | .inl (some c) => c.val
  | .inr ⟨o, p⟩ => referencePointAt S H D centres o p.1

/-- All choices land in the exact named ORIGINAL sort of the
formal vertex. No quotient sort or arbitrary sort cast is used. -/
theorem privateFanNonrootReference_sort
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v : PrivateFanVertex S D centres) :
    (privateFanNonrootReference S H D centres v).1 =
      privateFanSort S D centres v := by
  rcases v with (.inl oc | .inr op)
  · cases oc with
    | none => rfl
    | some c => rfl
  · rcases op with ⟨o, p⟩
    exact referencePointAt_sort S H D centres o p.1

/-- The value of every marked centre is its literal actual
tagged original real point, including repeated occurrences. -/
theorem privateFanNonrootReference_centre
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (c : DistinctCentres sort centres) :
    privateFanNonrootReference S H D centres
      (privateFanCentre S D centres c) = c.val := rfl

/-- At every positive private word position OTHER than the one
global root, the fan reference point is exactly the actual
position of that occurrence's own reference walk. For the last
position this relies on the proved equality with its literal
old marked centre. -/
theorem privateFanNonrootReference_at_nonroot
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p : PathPosition S (occurrenceWord S D o))
    (hp : p.val ≠ 0) :
    privateFanNonrootReference S H D centres
      (privateFanAtWordPosition S D centres o p) =
      referencePointAt S H D centres o p := by
  by_cases hEnd : p.val = diversityLength S (occurrenceWord S D o)
  · have hpFin : p = pathFinish S (occurrenceWord S D o) :=
      Fin.ext hEnd
    have hPos : 0 < diversityLength S (occurrenceWord S D o) := by
      omega
    rw [hpFin, privateFanAt_finish S D centres o hPos]
    change taggedCentre sort centres o.1 =
      referencePointAt S H D centres o
        (pathFinish S (occurrenceWord S D o))
    exact (referencePointAt_finish_value S H D centres o).symm
  · rw [privateFanAt_interior S D centres o p hp hEnd]
    rfl

/-- Every genuine private-path edge with neither endpoint at
the formal root already has a REAL old diversity atom under
the chosen per-occurrence reference map. No common-root Helly
witness is assumed or manufactured. -/
theorem privateFan_nonroot_path_edge_is_genuine
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p q : PathPosition S (occurrenceWord S D o))
    (hp : p.val ≠ 0) (hq : q.val ≠ 0)
    (hpq : pathAdjacent S (occurrenceWord S D o) p q) :
    GenuineEdge S
      (privateFanNonrootReference S H D centres
        (privateFanAtWordPosition S D centres o p))
      (privateFanNonrootReference S H D centres
        (privateFanAtWordPosition S D centres o q)) := by
  rw [privateFanNonrootReference_at_nonroot S H D centres o p hp,
    privateFanNonrootReference_at_nonroot S H D centres o q hq]
  exact referencePointAt_genuine_adjacent S H D centres o p q hpq

/-- The complete marked-centre graph also preserves EVERY
literal old atom with the same actual point assignment. -/
theorem privateFan_nonroot_centres_actual_colour
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (c d : DistinctCentres sort centres) :
    taggedColour S
      (privateFanNonrootReference S H D centres
        (privateFanCentre S D centres c))
      (privateFanNonrootReference S H D centres
        (privateFanCentre S D centres d)) =
      taggedColour S c.val d.val := rfl

end CCO.RawExact
