import CCO.UnfilteredEP.RealExpansionEP

/-! Retain a hereditary subfamily of the SAME finite relational tables.
Every expanded embedding has the identical old vertex map. Nonemptiness
and restriction-closure are explicit; no Ramsey or reasonableness claim
is inferred merely from deleting allowed expansions. -/

universe u v w l k
namespace CCO.UnfilteredEP
open CCO.TerminalHiddenHN
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable (E : RealExpansionData.{u,v,w,l,k} S)
variable (K : ∀ A, E.Expansion A → Prop)
variable (nonempty : ∀ A, ∃ a, K A a)
variable (closed : ∀ {A B} (f : InducedEmbedding S A B) (b : E.Expansion B),
  K B b → K A (E.restrict f b))

def restrictedExpansion : RealExpansionData.{u,v,w,l,k} S where
  Unary := E.Unary
  Binary := E.Binary
  finiteUnary := E.finiteUnary
  finiteBinary := E.finiteBinary
  unarySort := E.unarySort
  leftSort := E.leftSort
  rightSort := E.rightSort
  Expansion A := {a : E.Expansion A // K A a}
  nonempty A := let ⟨a,ha⟩ := nonempty A; ⟨⟨a,ha⟩⟩
  unary a := E.unary a.val
  binary a := E.binary a.val
  unary_sorted a := E.unary_sorted a.val
  binary_sorted a := E.binary_sorted a.val
  faithful a b hu hb := Subtype.ext (E.faithful a.val b.val hu hb)
  restrict f b := ⟨E.restrict f b.val,closed f b.val b.property⟩
  restrict_unary f b := E.restrict_unary f b.val
  restrict_binary f b := E.restrict_binary f b.val

/-- Restricting allowed objects changes no embedding condition between
retained objects; both directions keep the SAME supplied old map. -/
def restrictedEmbeddingEquiv {A B : FiniteInduced (X := X)}
    (a : (restrictedExpansion E K nonempty closed).Expansion A)
    (b : (restrictedExpansion E K nonempty closed).Expansion B) :
    (restrictedExpansion E K nonempty closed).Embedding a b ≃ E.Embedding a.val b.val where
  toFun f := ⟨f.old,f.unary_iff,f.binary_iff⟩
  invFun f := ⟨f.old,f.unary_iff,f.binary_iff⟩
  left_inv _ := RealExpansionData.Embedding.ext (fun _ => rfl)
  right_inv _ := RealExpansionData.Embedding.ext (fun _ => rfl)

/-- The old-map projection is literal in both directions. -/
@[simp] theorem restrictedEmbeddingEquiv_old {A B : FiniteInduced (X := X)}
    (a : (restrictedExpansion E K nonempty closed).Expansion A)
    (b : (restrictedExpansion E K nonempty closed).Expansion B)
    (f : (restrictedExpansion E K nonempty closed).Embedding a b) :
    ((restrictedEmbeddingEquiv E K nonempty closed a b) f).old = f.old := rfl

/-- Convert actual universal-competitor arrows on retained tables to EP
of this exact relational class. The witness hypothesis is explicit and
must be proved by the concrete hidden-to-visible construction. -/
theorem restrictedExpansion_EP
    (arrows : ∀ (A : FiniteInduced (X := X))
      (a : (restrictedExpansion E K nonempty closed).Expansion A),
      ∃ B : FiniteInduced (X := X),
        ∀ b : (restrictedExpansion E K nonempty closed).Expansion B,
          Nonempty (E.Embedding a.val b.val)) :
    (restrictedExpansion E K nonempty closed).EP := by
  intro A a
  obtain ⟨B,hB⟩ := arrows A a
  refine ⟨B,?_⟩
  intro b
  obtain ⟨f⟩ := hB b
  exact ⟨(restrictedEmbeddingEquiv E K nonempty closed a b).symm f⟩

end CCO.UnfilteredEP
