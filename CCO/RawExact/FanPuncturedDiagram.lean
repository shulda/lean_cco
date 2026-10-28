import CCO.RawExact.FanNonrootRealization
import Mathlib.Tactic

/-!
# B002 C12: one correctly coloured partial diagram off the formal root

There is a single source-point assignment to ALL formal private-fan
vertices other than the root: old marked centres keep their literal
actual points, and private interiors use independent reference walks.
The root's placeholder is deliberately unconstrained.

Retain only actual fan-graph edges whose endpoints are both
non-root. Their colours are obtained from the genuine old source,
and the resulting `PartialDiagram` satisfies its dependent converse
law automatically. This is a real diagram construction, not an
assumed colour-table representation. Root-incident spokes are NOT
included: adding them consistently is the next C12 obligation.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- The old reference point with its sort transported to exactly
the original sort attached to the chosen formal fan vertex. -/
noncomputable def privateFanNonrootTypedPoint
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v : PrivateFanVertex S D centres) :
    X (privateFanSort S D centres v) :=
  (privateFanNonrootReference_sort S H D centres v) ▸
    (privateFanNonrootReference S H D centres v).2

/-- Transport back to tagged original points changes no ACTUAL
vertex, only its dependent type index. -/
theorem privateFanNonrootTypedPoint_tag
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v : PrivateFanVertex S D centres) :
    (⟨privateFanSort S D centres v,
       privateFanNonrootTypedPoint S H D centres v⟩ : Sigma X) =
      privateFanNonrootReference S H D centres v := by
  unfold privateFanNonrootTypedPoint
  generalize hp : privateFanNonrootReference S H D centres v = p
  have hs : p.1 = privateFanSort S D centres v := by
    simpa only [← hp] using privateFanNonrootReference_sort S H D centres v
  cases hs
  rfl

/-- Only genuinely present formal fan edges away from the root
are retained. In particular no new extra edges arise between
independent reference paths even if their real points are
accidentally related in the original complete source language. -/
def privateFanPuncturedAdjacent
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v w : PrivateFanVertex S D centres) : Prop :=
  v ≠ privateFanRoot S D centres ∧
    w ≠ privateFanRoot S D centres ∧
    privateFanAdjacent S D centres v w

theorem privateFanPuncturedAdjacent_symm
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v w : PrivateFanVertex S D centres) :
    privateFanPuncturedAdjacent S D centres v w ↔
      privateFanPuncturedAdjacent S D centres w v := by
  constructor
  · rintro ⟨hv, hw, hAdj⟩
    exact ⟨hw, hv, (privateFanAdjacent_symm S D centres v w).mp hAdj⟩
  · rintro ⟨hw, hv, hAdj⟩
    exact ⟨hv, hw, (privateFanAdjacent_symm S D centres w v).mp hAdj⟩

/-- A fully typed and correctly converse-coloured old partial
diagram representing exactly the NON-ROOT edges of the actual
private fan. All its specified edges are realized by a SINGLE
old point assignment (the private-fan reference points). -/
noncomputable def privateFanPuncturedDiagram
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t)) :
    PartialDiagram S (PrivateFanVertex S D centres) where
  finite_type := privateFanVertex_finite S D centres
  vertexSort := privateFanSort S D centres
  edge := fun v w _ =>
    if h : privateFanPuncturedAdjacent S D centres v w then
      S.colour (privateFanNonrootTypedPoint S H D centres v)
        (privateFanNonrootTypedPoint S H D centres w)
    else
      none
  edge_reverse := by
    intro v w hvw a
    change
      (if h : privateFanPuncturedAdjacent S D centres v w then
        S.colour (privateFanNonrootTypedPoint S H D centres v)
          (privateFanNonrootTypedPoint S H D centres w)
      else none) = some a ↔
      (if h : privateFanPuncturedAdjacent S D centres w v then
        S.colour (privateFanNonrootTypedPoint S H D centres w)
          (privateFanNonrootTypedPoint S H D centres v)
      else none) = some (S.conv a)
    by_cases h : privateFanPuncturedAdjacent S D centres v w
    · have hRev :=
        (privateFanPuncturedAdjacent_symm S D centres v w).mp h
      simp only [dif_pos h, dif_pos hRev]
      exact S.colour_swap _ _ a
    · have hRev : ¬ privateFanPuncturedAdjacent S D centres w v := by
        intro hBack
        exact h ((privateFanPuncturedAdjacent_symm S D centres w v).mp hBack)
      simp only [dif_neg h, dif_neg hRev]

/-- The reference point assignment is a genuine old
`DiagramHom` of the punctured diagram. This is an UNCONDITIONAL
source construction from actual independent RAW reference walks;
no Helly conclusion is smuggled into the root placeholder. -/
noncomputable def privateFanPuncturedDiagram_realization
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t)) :
    DiagramHom (privateFanPuncturedDiagram S H D centres) where
  point := privateFanNonrootTypedPoint S H D centres
  preserves_edge := by
    intro v w hvw a ha
    change
      (if h : privateFanPuncturedAdjacent S D centres v w then
        S.colour (privateFanNonrootTypedPoint S H D centres v)
          (privateFanNonrootTypedPoint S H D centres w)
      else none) = some a at ha
    split_ifs at ha with h
    · exact ha
    · cases ha

end CCO.RawExact
