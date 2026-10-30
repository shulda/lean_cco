import CCO.PointGeneratedSAP.Original

/-! Complete induced objects with FULL finite real-generated carriers.
They are a subcategory of the unary age, not its orphan-base hereditary age. -/
universe u v
namespace CCO.PointGeneratedSAP
open UnaryFreshFrames
variable {L : Language.{u}} {V : Type v} {H : Structure L V} (O : Original L V H)

structure Piece where
  toPiece : H.Piece
  generated : H.closure {x | x ∈ toPiece.points ∧ O.realSort (H.sort x)} = toPiece.points

namespace Piece
variable {O}
abbrev points (A : Piece O) := A.toPiece.points
abbrev finite (A : Piece O) := A.toPiece.finite
abbrev closed (A : Piece O) := A.toPiece.closed
abbrev Embedding (A : Piece O) (B : Set V) := A.toPiece.Embedding B
instance (A : Piece O) : Finite A.points := A.toPiece.finite.to_subtype

def realBase (A : Piece O) : Set O.Real := {r | r.val ∈ A.points}
theorem finite_realBase (A : Piece O) : A.realBase.Finite :=
  A.finite.preimage Subtype.val_injective.injOn

theorem realBase_image (A : Piece O) :
    Subtype.val '' A.realBase = {x | x ∈ A.points ∧ O.realSort (H.sort x)} := by
  ext x
  constructor
  · rintro ⟨r,hr,rfl⟩
    exact ⟨hr,r.property⟩
  · rintro ⟨hx,hr⟩
    exact ⟨⟨x,hr⟩,hx,rfl⟩

theorem generated_realBase (A : Piece O) : H.closure (Subtype.val '' A.realBase) = A.points := by
  rw [A.realBase_image]
  exact A.generated

/-- Full closure of a finite real set; no extra real closure is presumed. -/
def ofReal (C : Interpretation H O) (D : Set O.Real) (hD : D.Finite) : Piece O where
  toPiece := ⟨H.closure (Subtype.val '' D), C.locallyFinite D hD, H.closure_closed _⟩
  generated := by
    apply Set.Subset.antisymm
    · exact H.closure_minimal (H.closure_closed _) (fun _ hx => hx.1)
    · apply H.closure_mono
      rintro _ ⟨r,hr,rfl⟩
      exact ⟨H.subset_closure _ ⟨r,hr,rfl⟩,r.property⟩

def empty : Piece O where
  toPiece := Structure.Piece.empty
  generated := by
    have he : {x : V | x ∈ (∅ : Set V) ∧ O.realSort (H.sort x)} = ∅ := by simp
    change H.closure {x : V | x ∈ (∅ : Set V) ∧ O.realSort (H.sort x)} = ∅
    rw [he,H.closure_empty]

def union (A B : Piece O) : Piece O where
  toPiece := A.toPiece.union B.toPiece
  generated := by
    have he : {x | x ∈ A.points ∪ B.points ∧ O.realSort (H.sort x)} =
        {x | x ∈ A.points ∧ O.realSort (H.sort x)} ∪
        {x | x ∈ B.points ∧ O.realSort (H.sort x)} := by
      ext x
      constructor
      · rintro ⟨hx | hx,hr⟩
        · exact Or.inl ⟨hx,hr⟩
        · exact Or.inr ⟨hx,hr⟩
      · rintro (⟨hx,hr⟩ | ⟨hx,hr⟩)
        · exact ⟨Or.inl hx,hr⟩
        · exact ⟨Or.inr hx,hr⟩
    change H.closure {x | x ∈ A.points ∪ B.points ∧ O.realSort (H.sort x)} = A.points ∪ B.points
    rw [he,H.closure_union,A.generated,B.generated]

namespace Embedding
variable {A B : Piece O} {T : Set V}

theorem eval_eq (f : A.Embedding T) {i j : L.Sorts} (t : Term L i j) (x : A.points) :
    f.point ⟨H.eval t x.val,H.eval_mem_closed A.closed t x.property⟩ = H.eval t (f.point x) := by
  induction t with
  | id => rfl
  | func F t ih =>
    exact (f.func_eq F ⟨H.eval t x.val,H.eval_mem_closed A.closed t x.property⟩).trans
      (congrArg (H.func F) ih)

def realRestriction (f : A.Embedding T) : O.Embedding A.realBase where
  point x := ⟨f.point ⟨x.val.val,x.property⟩,by rw [f.sort_eq]; exact x.val.property⟩
  injective := by
    intro x y he
    have h := f.injective (congrArg Subtype.val he)
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : A.points => z.val) h
  sort_eq x := f.sort_eq _
  rel_iff R _ xs := f.rel_iff R (fun i => ⟨(xs i).val.val,(xs i).property⟩)

/-- Induced embeddings carry a full generated carrier to a full generated carrier. -/
def image (f : A.Embedding T) : Piece O where
  toPiece := Structure.Piece.Embedding.image f
  generated := by
    apply Set.Subset.antisymm
    · exact H.closure_minimal (Structure.Piece.Embedding.image f).closed (fun _ hx => hx.1)
    · rintro _ ⟨x,rfl⟩
      have hx : x.val ∈ H.closure (Subtype.val '' A.realBase) := A.generated_realBase.symm ▸ x.property
      obtain ⟨r,⟨r,hr,rfl⟩,j,t,ht⟩ := hx
      have hr' : r.val ∈ A.points := hr
      have htx : (⟨H.eval t r.val,H.eval_mem_closed A.closed t hr'⟩ : A.points) = x := Subtype.ext ht
      rw [← htx, f.eval_eq t ⟨r.val,hr'⟩]
      apply H.eval_mem_closed (H.closure_closed _) t
      apply H.subset_closure
      refine ⟨⟨⟨r.val,hr⟩,rfl⟩,?_⟩
      rw [f.sort_eq]
      exact r.property

end Embedding

/-- Automorphic images and unions are actual induced point-generated objects. -/
def mapAut (g : H.Aut) (A : Piece O) : Piece O :=
  Embedding.image ((Structure.Piece.Embedding.identity A.toPiece).mapAut g)

end Piece
end CCO.PointGeneratedSAP
