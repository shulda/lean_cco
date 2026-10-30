import CCO.APCharacter.Towers.UnaryReduct
import Mathlib.CategoryTheory.EqToHom

/-! Literal global reduct projections and finite-age forgetful functors
compose coherently, not merely by an unspecified natural isomorphism. -/
universe u v w
namespace CCO.APCharacter.Towers.UnaryReduct
open CategoryTheory OwnerTransversal.CountableColour
variable {ι κ ν : Type u} {X : ι → Type v} {Y : κ → Type v} {Z : ν → Type v}
variable {S : AtomicSource.{u,v,w} ι X} {T : AtomicSource.{u,v,w} κ Y}
variable {U : AtomicSource.{u,v,w} ν Z}
noncomputable section

private theorem chart_ext' {M : MaskData S} {A B : Age.Chart S M}
    (size : A.size = B.size) (table : HEq A.table B.table) : A = B := by
  cases A
  cases B
  cases size
  cases eq_of_heq table
  rfl

private theorem embedding_heq' {L : FirstOrder.Language} {V W : Type}
    {A B : L.Structure V} {C D : L.Structure W} (h : A = B) (k : C = D)
    (f : @FirstOrder.Language.Embedding L V W A C)
    (g : @FirstOrder.Language.Embedding L V W B D)
    (hf : ∀ x, f.toFun x = g.toFun x) : HEq f g := by
  cases h
  cases k
  apply heq_of_eq
  apply FirstOrder.Language.Embedding.ext
  exact hf

theorem ownerMap_actual (P : UnaryReduct S T) (b : κ × Bit) :
    P.ownerMap (Age.ownerEquiv T b) = Age.ownerEquiv S (P.parent b.1,0) := by
  unfold ownerMap
  rw [Equiv.symm_apply_apply]

theorem colourMap_actual (P : UnaryReduct S T) (c : Age.Colour T) :
    P.colourMap (Age.colourEquiv T c) = Age.colourEquiv S
      ⟨P.parent c.1,P.parent c.2.1,Option.map (P.atom _ _) c.2.2⟩ := by
  unfold colourMap
  dsimp only
  rw [Equiv.symm_apply_apply]

theorem compose_mapTable (P : UnaryReduct S T) (Q : UnaryReduct T U)
    {V : Type} (F : Age.Table U V) :
    (P.compose Q).mapTable F = P.mapTable (Q.mapTable F) := by
  apply congrArg₂ Table.mk
  · funext x
    change (P.compose Q).ownerMap (F.owner x) = P.ownerMap (Q.ownerMap (F.owner x))
    obtain ⟨b,hb⟩ := (Age.ownerEquiv U).surjective (F.owner x)
    rw [← hb,ownerMap_actual,ownerMap_actual,ownerMap_actual]
    rfl
  · funext x y
    change (P.compose Q).colourMap (F.colour x y) = P.colourMap (Q.colourMap (F.colour x y))
    obtain ⟨c,hc⟩ := (Age.colourEquiv U).surjective (F.colour x y)
    rw [← hc,colourMap_actual,colourMap_actual,colourMap_actual]
    simp only [compose,Option.map_map,Function.comp_def]

/-- The two composed projections give EXACTLY the same actual old chart
and actual old embedding, not just equivalent chart representatives. -/
theorem compose_forget (P : UnaryReduct S T) (Q : UnaryReduct T U) :
    (P.compose Q).forget = Q.forget ⋙ P.forget := by
  apply Functor.hext
  · intro C
    exact chart_ext' rfl (heq_of_eq (compose_mapTable P Q C.table))
  · intro C D f
    apply embedding_heq'
      (congrArg Table.toStructure (compose_mapTable P Q C.table))
      (congrArg Table.toStructure (compose_mapTable P Q D.table))
    intro x
    rfl

/-- Zero-stage original names are unchanged because every old chart has
its actual dummy bit equal to zero, including the empty chart. -/
theorem identity_mapTable (C : Age.Chart S (Age.zeroMask S)) :
    (identity S).mapTable C.table = C.table := by
  rw [C.table_eq,map_actual]
  have hb : C.bits = (fun _ => 0) := funext C.legal.1
  rw [hb]
  rfl

theorem identity_forget (S : AtomicSource.{u,v,w} ι X) :
    (identity S).forget = 𝟭 (Age.Chart S (Age.zeroMask S)) := by
  apply Functor.hext
  · intro C
    exact chart_ext' rfl (heq_of_eq (identity_mapTable C))
  · intro C D f
    apply embedding_heq'
      (congrArg Table.toStructure (identity_mapTable C))
      (congrArg Table.toStructure (identity_mapTable D))
    intro x
    rfl

end
end CCO.APCharacter.Towers.UnaryReduct
