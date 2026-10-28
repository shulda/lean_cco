import CCO.RawExact.FanPuncturedDiagram
import CCO.RawExact.FanNonrootRealization
import Mathlib.Tactic

/-!
# B002 C12: exact support of the actual private-fan punctured diagram

A non-root old-centre edge has the LITERAL source colour of two
distinct actual marked old points. Every non-root private-word
edge likewise has the real source colour of its one occurrence's
independently selected RAW walk.

Thus the punctured diagram records exactly the formal fan graph
edges away from the root; it cannot accidentally lose a genuine
diversity edge by assigning the logical diagonal to it, nor can
it invent a new edge between different private interiors.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- Distinct actual old centres really carry a diversity colour
under the single punctured-fan reference realization. -/
theorem privateFan_punctured_old_centre_edge_has_atom
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (c d : DistinctCentres sort centres)
    (hcd : c ≠ d) :
    ∃ a : S.Atom
        (privateFanSort S D centres (privateFanCentre S D centres c))
        (privateFanSort S D centres (privateFanCentre S D centres d)),
      S.colour
        (privateFanNonrootTypedPoint S H D centres
          (privateFanCentre S D centres c))
        (privateFanNonrootTypedPoint S H D centres
          (privateFanCentre S D centres d)) = some a := by
  let v := privateFanCentre S D centres c
  let w := privateFanCentre S D centres d
  have hDifferent :
      S.colour (privateFanNonrootTypedPoint S H D centres v)
        (privateFanNonrootTypedPoint S H D centres w) ≠ none := by
    intro hNone
    have hTag := (S.colour_none_iff
      (privateFanNonrootTypedPoint S H D centres v)
      (privateFanNonrootTypedPoint S H D centres w)).mp hNone
    have hv := privateFanNonrootTypedPoint_tag S H D centres v
    have hw := privateFanNonrootTypedPoint_tag S H D centres w
    rw [hv, hw] at hTag
    exact hcd (Subtype.ext hTag)
  cases hColour : S.colour
    (privateFanNonrootTypedPoint S H D centres v)
    (privateFanNonrootTypedPoint S H D centres w) with
  | none =>
      exact False.elim (hDifferent hColour)
  | some a =>
      exact ⟨a, rfl⟩

/-- Every private-word edge not incident with the formal root
has a literal diversity colour under the same one point map. -/
theorem privateFan_punctured_word_edge_has_atom
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    (p q : PathPosition S (occurrenceWord S D o))
    (hp : p.val ≠ 0) (hq : q.val ≠ 0)
    (hpq : pathAdjacent S (occurrenceWord S D o) p q) :
    ∃ a : S.Atom
        (privateFanSort S D centres
          (privateFanAtWordPosition S D centres o p))
        (privateFanSort S D centres
          (privateFanAtWordPosition S D centres o q)),
      S.colour
        (privateFanNonrootTypedPoint S H D centres
          (privateFanAtWordPosition S D centres o p))
        (privateFanNonrootTypedPoint S H D centres
          (privateFanAtWordPosition S D centres o q)) = some a := by
  have h := privateFan_nonroot_path_edge_is_genuine
    S H D centres o p q hp hq hpq
  have hTagP := privateFanNonrootTypedPoint_tag S H D centres
    (privateFanAtWordPosition S D centres o p)
  have hTagQ := privateFanNonrootTypedPoint_tag S H D centres
    (privateFanAtWordPosition S D centres o q)
  rw [← hTagP, ← hTagQ] at h
  exact h

/-- Full support equivalence: the punctured diagram contains
precisely all formal fan edges between two non-root vertices.
Its actual edge labels are original diversity atoms, not
unproved or artificial binary relations. -/
theorem privateFanPuncturedDiagram_support_iff
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v w : PrivateFanVertex S D centres)
    (hvw : v ≠ w) :
    (∃ a : S.Atom (privateFanSort S D centres v)
        (privateFanSort S D centres w),
      (privateFanPuncturedDiagram S H D centres).edge v w hvw = some a) ↔
      privateFanPuncturedAdjacent S D centres v w := by
  classical
  constructor
  · rintro ⟨a, ha⟩
    unfold privateFanPuncturedDiagram at ha
    change
      (if h : privateFanPuncturedAdjacent S D centres v w then
        S.colour (privateFanNonrootTypedPoint S H D centres v)
          (privateFanNonrootTypedPoint S H D centres w)
      else none) = some a at ha
    split_ifs at ha with h
    · exact h
    · cases ha
  · rintro ⟨hv, hw, hAdj⟩
    have hSome : ∃ a : S.Atom (privateFanSort S D centres v)
        (privateFanSort S D centres w),
        S.colour (privateFanNonrootTypedPoint S H D centres v)
          (privateFanNonrootTypedPoint S H D centres w) = some a := by
      rcases hAdj with hOld | hPath
      · obtain ⟨c, d, hcd, rfl, rfl⟩ := hOld
        exact privateFan_punctured_old_centre_edge_has_atom
          S H D centres c d hcd
      · obtain ⟨o, p, q, hpq, rfl, rfl⟩ := hPath
        have hp : p.val ≠ 0 := by
          intro hp0
          have hstart : p = pathStart S (occurrenceWord S D o) :=
            Fin.ext hp0
          rw [hstart, privateFanAt_start S D centres o] at hv
          exact hv rfl
        have hq : q.val ≠ 0 := by
          intro hq0
          have hstart : q = pathStart S (occurrenceWord S D o) :=
            Fin.ext hq0
          rw [hstart, privateFanAt_start S D centres o] at hw
          exact hw rfl
        exact privateFan_punctured_word_edge_has_atom
          S H D centres o p q hp hq hpq
    obtain ⟨a, ha⟩ := hSome
    refine ⟨a, ?_⟩
    change
      (if h : privateFanPuncturedAdjacent S D centres v w then
        S.colour (privateFanNonrootTypedPoint S H D centres v)
          (privateFanNonrootTypedPoint S H D centres w)
      else none) = some a
    rw [dif_pos ⟨hv, hw, hAdj⟩]
    exact ha

end CCO.RawExact
