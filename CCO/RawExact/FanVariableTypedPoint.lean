import CCO.RawExact.FanVariableReference
import Mathlib.Tactic

/-!
# B002 C12: type-safe original point assignment for any selected RAW walks

The one formal root is assigned an explicitly chosen original real
point; every marked centre retains its ACTUAL old value; each private
interior uses one realized typed RAW word occurrence. The resulting
Sigma-valued assignment has an original sort theorem, so it can be
converted to precisely the dependent point field of `DiagramHom`.

The construction does not assume the resulting map preserves all
root spokes; that property is established cycle-by-cycle using just
two pairwise-compatible word witnesses.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- Every formal vertex receives one genuinely old real point
of the precise ORIGINAL sort required by its finite fan position. -/
def privateFanVariableTypedPoint
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (choice : FanWalkChoices S D centres)
    (xRoot : X root)
    (v : PrivateFanVertex S D centres) :
    X (privateFanSort S D centres v) :=
  (privateFanVariableReference_sort S D centres choice xRoot v) ▸
    (privateFanVariableReference S D centres choice xRoot v).2

/-- The typed fan point really is the same ACTUAL tagged original
point chosen at each formal vertex; dependent casts cannot
change the value or invent a quotient-sort point. -/
theorem privateFanVariableTypedPoint_tag
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (choice : FanWalkChoices S D centres)
    (xRoot : X root)
    (v : PrivateFanVertex S D centres) :
    (⟨privateFanSort S D centres v,
      privateFanVariableTypedPoint S D centres choice xRoot v⟩ : Sigma X) =
      privateFanVariableReference S D centres choice xRoot v := by
  unfold privateFanVariableTypedPoint
  have cast_roundtrip (p : Sigma X) (s : ι) (h : p.1 = s) :
      (⟨s, h ▸ p.2⟩ : Sigma X) = p := by
    cases p with
    | mk i x =>
        cases h
        rfl
  exact cast_roundtrip
    (privateFanVariableReference S D centres choice xRoot v)
    (privateFanSort S D centres v)
    (privateFanVariableReference_sort S D centres choice xRoot v)

/-- Literal old equality and diversity colours are computed by
the same actual tagged points before and after the dependent
point coercions to their original fan sorts. -/
theorem privateFanVariableTypedPoint_taggedColour
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (choice : FanWalkChoices S D centres)
    (xRoot : X root)
    (v w : PrivateFanVertex S D centres) :
    taggedColour S
      (⟨_, privateFanVariableTypedPoint S D centres choice xRoot v⟩ : Sigma X)
      (⟨_, privateFanVariableTypedPoint S D centres choice xRoot w⟩ : Sigma X) =
    taggedColour S
      (privateFanVariableReference S D centres choice xRoot v)
      (privateFanVariableReference S D centres choice xRoot w) := by
  rw [privateFanVariableTypedPoint_tag S D centres choice xRoot v,
    privateFanVariableTypedPoint_tag S D centres choice xRoot w]

end CCO.RawExact
