import Mathlib.ModelTheory.PartialEquiv

/-! Countable back-and-forth from actual finite FULL-substructure extension.
In the packet application the language contains every literal owner name,
fine-colour name and unary packet function. Its substructures are therefore
closed under every packet function. Actual local finiteness and BOTH finite
extension properties must be supplied by the packet inflation construction;
no homogeneous-model or isomorphism provider is assumed here. -/

open scoped FirstOrder
open FirstOrder FirstOrder.Language

universe u v w z
namespace CCO.OwnerTransversal.PacketBackAndForth
variable (L : FirstOrder.Language.{u,v})
variable (X : Type w) (Y : Type z) [L.Structure X] [L.Structure Y]

/-- Every finitely generated substructure is finite. For a finite packet
group this follows from closure being the finite union of its full packets. -/
def LocallyFinite : Prop := ∀ A : L.Substructure X, A.FG → Finite A

/-- Every embedding of a finite full substructure extends over a finite
larger full substructure. All language functions and relation names are
preserved by the actual embeddings. -/
def FiniteExtension : Prop :=
  ∀ (A B : L.Substructure X) [Finite A] [Finite B] (hAB : A ≤ B)
    (f : A ↪[L] Y), ∃ g : B ↪[L] Y,
      g.comp (Substructure.inclusion hAB) = f

/-- Finite full-substructure extension supplies each genuine one-point
finitely generated partial-isomorphism extension used by back-and-forth. -/
theorem isExtensionPair_of_finiteExtension
    (finiteX : LocallyFinite L X) (extension : FiniteExtension L X Y) :
    L.IsExtensionPair X Y := by
  rw [isExtensionPair_iff_exists_embedding_closure_singleton_sup]
  intro A hA f x
  let B : L.Substructure X := Substructure.closure L {x} ⊔ A
  have hB : B.FG := (Substructure.fg_closure_singleton x).sup hA
  letI : Finite A := finiteX A hA
  letI : Finite B := finiteX B hB
  obtain ⟨g,hg⟩ := extension A B le_sup_right f
  exact ⟨g,hg.symm⟩

/-- Actual countable isomorphism preserving ALL language functions and
relations and extending the prescribed finite full-substructure embedding.
In particular every owner, fine colour and t_g is retained literally when
those are the symbols of L. Empty and finite structures are allowed. -/
theorem equiv_extending [Countable X] [Countable Y]
    (finiteX : LocallyFinite L X) (finiteY : LocallyFinite L Y)
    (forth : FiniteExtension L X Y) (back : FiniteExtension L Y X)
    (A : L.Substructure X) [Finite A] (f : A ↪[L] Y) :
    ∃ e : X ≃[L] Y, e.toEmbedding.comp A.subtype = f := by
  let p : L.FGEquiv X Y :=
    ⟨⟨A,f.toHom.range,f.equivRange⟩,Substructure.FG.of_finite⟩
  obtain ⟨e,he⟩ := equiv_between_cg (Structure.cg_of_countable (L := L) (M := X))
    (Structure.cg_of_countable (L := L) (M := Y)) p
    (isExtensionPair_of_finiteExtension L X Y finiteX forth)
    (isExtensionPair_of_finiteExtension L Y X finiteY back)
  refine ⟨e,?_⟩
  ext a
  have hp := PartialEquiv.toEquiv_inclusion_apply he a
  have hv := congrArg Subtype.val hp
  change e a.val = f a at hv
  exact hv

end CCO.OwnerTransversal.PacketBackAndForth
