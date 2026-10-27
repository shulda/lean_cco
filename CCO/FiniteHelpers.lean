import CCO.Finite

/-!
# Finite induced subset API

These are structural conversions for the actual source, not new age/SAP
hypotheses. In particular, a literal subset inclusion preserves *all*
ordered pair colours (including the logical diagonal), not just the
diversity atoms specified by a partial diagram.
-/

universe u v w

namespace CCO

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X)

namespace FiniteInduced

/-- An explicitly finite set of real tagged vertices determines its full
induced complete finite coloured structure. -/
def ofFinset (F : Finset (Sigma X)) : FiniteInduced (X := X) where
  vertices := (F : Set (Sigma X))
  finite_vertices := F.finite_toSet

end FiniteInduced

/-- A literal finite subset inclusion is an induced embedding of the
entire original complete pair-colouring, with unchanged named sort tags. -/
def inducedInclusion
    (A B : FiniteInduced (X := X))
    (hAB : A.vertices ⊆ B.vertices) :
    InducedEmbedding S A B where
  toEmbedding := {
    toFun := fun p => ⟨p.val, hAB p.property⟩
    inj' := by
      intro p q hpq
      apply Subtype.ext
      exact congrArg (fun r : ↥B.vertices => r.val) hpq
  }
  preserves_sort := by
    intro p
    rfl
  preserves_colours := by
    intro p q
    rfl

/-- The pointwise-inclusion map is literally the identity on real
vertices. Later SAP gluing uses this to align actual common bases. -/
theorem inducedInclusion_val
    (A B : FiniteInduced (X := X))
    (hAB : A.vertices ⊆ B.vertices)
    (p : ↥A.vertices) :
    ((inducedInclusion S A B hAB).toEmbedding p).val = p.val := by
  rfl

/-- An induced embedding never collapses two old real points, even when
their named sort labels agree. -/
theorem inducedEmbedding_ne
    {A B : FiniteInduced (X := X)}
    (e : InducedEmbedding S A B) {p q : ↥A.vertices}
    (hpq : p ≠ q) :
    e.toEmbedding p ≠ e.toEmbedding q := by
  exact fun h => hpq (e.toEmbedding.injective h)

end CCO
