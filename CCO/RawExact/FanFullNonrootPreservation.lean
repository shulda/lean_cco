import CCO.RawExact.FanVariableNonrootColour
import CCO.RawExact.FanVariableTypedPoint
import CCO.RawExact.FanFullEdgeSemantics

/-!
# B002 C12: all full-fan edges away from root survive arbitrary RAW-walk swaps

The entire finite anchored fan has TRUE source atomic labels.
Away from its one formal root those labels are the original
colours of independently chosen genuine old RAW reference walks
and the literal complete old marked-centre diagram.

Any other family of actual RAW walks with the same prescribed
old centres consequently preserves every edge away from the
formal root, no matter what its various old starting points are.
Only root spokes require common-root pairwise ball witnesses.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- One typed candidate map obtained from ANY selected genuine
RAW walks preserves the FULL original diagram on every specified
nonroot edge. The exact hypotheses of source homogeneity H
serve only to pick the permanent reference walks; no SAP or
full exact-ball Helly provider appears. -/
theorem privateFanVariable_preserves_full_nonroot_edge
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (choice : FanWalkChoices S D centres)
    (xRoot : X root)
    (v w : PrivateFanVertex S D centres)
    (hv : v ≠ privateFanRoot S D centres)
    (hw : w ≠ privateFanRoot S D centres)
    (hvw : v ≠ w)
    (a : S.Atom (privateFanSort S D centres v)
        (privateFanSort S D centres w))
    (ha : (privateFanFullDiagram S H D centres).edge v w hvw = some a) :
    S.colour
      (privateFanVariableTypedPoint S D centres choice xRoot v)
      (privateFanVariableTypedPoint S D centres choice xRoot w) =
      some a := by
  have hPunct :
      (privateFanPuncturedDiagram S H D centres).edge v w hvw = some a := by
    rw [← privateFanFull_nonroot_edge_eq S H D centres
      v w hv hw hvw]
    exact ha
  have hAdj : privateFanAdjacent S D centres v w :=
    ((privateFanPuncturedDiagram_support_iff S H D centres
      v w hvw).mp ⟨a, hPunct⟩).2.2
  have hOldColour :
      S.colour
        (privateFanNonrootTypedPoint S H D centres v)
        (privateFanNonrootTypedPoint S H D centres w) = some a :=
    (privateFanPuncturedDiagram_realization S H D centres).preserves_edge
      v w hvw a hPunct
  have hTagged :=
    privateFanVariable_nonroot_adjacent_colour_eq_reference
      S H D centres choice xRoot v w hv hw hAdj
  have hTaggedTyped :
      taggedColour S
        (⟨privateFanSort S D centres v,
          privateFanVariableTypedPoint S D centres choice xRoot v⟩ : Sigma X)
        (⟨privateFanSort S D centres w,
          privateFanVariableTypedPoint S D centres choice xRoot w⟩ : Sigma X) =
      taggedColour S
        (⟨privateFanSort S D centres v,
          privateFanNonrootTypedPoint S H D centres v⟩ : Sigma X)
        (⟨privateFanSort S D centres w,
          privateFanNonrootTypedPoint S H D centres w⟩ : Sigma X) := by
    rw [privateFanVariableTypedPoint_tag S D centres choice xRoot v,
      privateFanVariableTypedPoint_tag S D centres choice xRoot w,
      privateFanNonrootTypedPoint_tag S H D centres v,
      privateFanNonrootTypedPoint_tag S H D centres w]
    exact hTagged
  have hColour :
      S.colour
        (privateFanVariableTypedPoint S D centres choice xRoot v)
        (privateFanVariableTypedPoint S D centres choice xRoot w) =
      S.colour
        (privateFanNonrootTypedPoint S H D centres v)
        (privateFanNonrootTypedPoint S H D centres w) := by
    simpa only [taggedColour, Sigma.mk.injEq, heq_eq_eq,
      true_and] using hTaggedTyped
  exact hColour.trans hOldColour

end CCO.RawExact
