import CCO.UnaryHN.RawEncoding.Basic

/-! Free decompositions are the SAME closed subset diagrams before and after
encoding. This proves irreducibility transport, rather than assuming it. -/
universe u v
namespace CCO.UnaryHN.Raw
open CCO.UnarySupport (Signature)
open StructuralRamsey.Structure

variable {L : Signature.{u}} {V : Type v} (C : Typed L V)

def typedDecomposition (d : ProperFreeDecomposition (encode C)) :
    CCO.UnarySupport.Structure.FreeDecomposition C where
  left := Set.range d.leftIn
  right := Set.range d.rightIn
  left_closed := (closed_encode_iff C _).mp d.leftIn.range_isClosed
  right_closed := (closed_encode_iff C _).mp d.rightIn.range_isClosed
  cover := by
    apply Set.eq_univ_of_forall
    intro x
    rcases d.free.covers x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl ⟨y, rfl⟩
    · exact Or.inr ⟨y, rfl⟩
  left_proper := by intro h; exact d.leftProper (Set.range_eq_univ.mp h)
  right_proper := by intro h; exact d.rightProper (Set.range_eq_univ.mp h)
  rel_local R xs hx := by
    rcases (d.free.rel_iff (.inl R) xs).mp hx with ⟨ys, _, heq⟩ | ⟨ys, _, heq⟩
    · exact Or.inl (fun i => ⟨ys i, (congrFun heq i).symm⟩)
    · exact Or.inr (fun i => ⟨ys i, (congrFun heq i).symm⟩)

def subsetEmbedding (D : Diagram L V) (S T : Set V)
    (hS : D.IsClosed S) (hT : D.IsClosed T) (hST : S ⊆ T) :
    Embedding (D.induce S hS) (D.induce T hT) where
  toFun x := ⟨x.val, hST x.property⟩
  injective := by intro x y h; exact Subtype.ext (congrArg (fun z : T => z.val) h)
  map_rel_iff _ _ := Iff.rfl
  map_func F xs := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      have hs : y.val ∈ S := hS F (Subtype.val ∘ xs) (fun i => (xs i).property) hy
      exact ⟨⟨y.val, hs⟩, hy, Subtype.ext rfl⟩

def encodedDecomposition (d : CCO.UnarySupport.Structure.FreeDecomposition C) :
    ProperFreeDecomposition (encode C) := by
  let A := encode C
  have hL : A.IsClosed d.left := (closed_encode_iff C _).mpr d.left_closed
  have hR : A.IsClosed d.right := (closed_encode_iff C _).mpr d.right_closed
  have hI : A.IsClosed (d.left ∩ d.right) := by
    intro F xs hx y hy
    exact ⟨hL F xs (fun i => (hx i).1) hy, hR F xs (fun i => (hx i).2) hy⟩
  let sL := subsetEmbedding A (d.left ∩ d.right) d.left hI hL (fun _ h => h.1)
  let sR := subsetEmbedding A (d.left ∩ d.right) d.right hI hR (fun _ h => h.2)
  let iL := inclusion A d.left hL
  let iR := inclusion A d.right hR
  have cover (x : V) : x ∈ d.left ∨ x ∈ d.right := by
    rw [← Set.mem_union, d.cover]
    trivial
  have localRel (R : (language L).RelSymbol) (xs : Fin ((language L).relArity R) → V)
      (hx : A.rel R xs) : (∀ i, xs i ∈ d.left) ∨ (∀ i, xs i ∈ d.right) := by
    cases R with
    | inl R => exact d.rel_local R xs hx
    | inr s =>
      rcases cover (xs 0) with hl | hr
      · left; intro i; have hi : i = 0 := Fin.eq_zero i; subst i; exact hl
      · right; intro i; have hi : i = 0 := Fin.eq_zero i; subst i; exact hr
  refine {
    Common := {x : V // x ∈ d.left ∩ d.right}
    Left := {x : V // x ∈ d.left}
    Right := {x : V // x ∈ d.right}
    common := A.induce (d.left ∩ d.right) hI
    left := A.induce d.left hL
    right := A.induce d.right hR
    toLeft := sL
    toRight := sR
    leftIn := iL
    rightIn := iR
    free := ?_
    leftProper := ?_
    rightProper := ?_ }
  · constructor
    · intro x
      rcases cover x with hl | hr
      · exact Or.inl ⟨⟨x, hl⟩, rfl⟩
      · exact Or.inr ⟨⟨x, hr⟩, rfl⟩
    · intro x y
      constructor
      · intro h
        change x.val = y.val at h
        exact ⟨⟨x.val, x.property, h.symm ▸ y.property⟩,
          Subtype.ext rfl, Subtype.ext h.symm⟩
      · rintro ⟨z, rfl, rfl⟩
        rfl
    · intro R xs
      constructor
      · intro hx
        rcases localRel R xs hx with hl | hr
        · exact Or.inl ⟨fun i => ⟨xs i, hl i⟩, hx, rfl⟩
        · exact Or.inr ⟨fun i => ⟨xs i, hr i⟩, hx, rfl⟩
      · rintro (⟨ys, hy, rfl⟩ | ⟨ys, hy, rfl⟩)
        · exact hy
        · exact hy
    · intro F xs y
      constructor
      · intro hy
        rcases cover (xs 0) with hl | hr
        · have hxs : ∀ i, xs i ∈ d.left := by
            intro i; have hi : i = 0 := Fin.eq_zero i; subst i; exact hl
          exact Or.inl ⟨fun i => ⟨xs i, hxs i⟩, ⟨y, hL F xs hxs hy⟩, hy, rfl, rfl⟩
        · have hxs : ∀ i, xs i ∈ d.right := by
            intro i; have hi : i = 0 := Fin.eq_zero i; subst i; exact hr
          exact Or.inr ⟨fun i => ⟨xs i, hxs i⟩, ⟨y, hR F xs hxs hy⟩, hy, rfl, rfl⟩
      · rintro (⟨ys, z, hz, rfl, rfl⟩ | ⟨ys, z, hz, rfl, rfl⟩)
        · exact hz
        · exact hz
  · intro hs
    apply d.left_proper
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, hy⟩ := hs x
    exact hy ▸ y.property
  · intro hs
    apply d.right_proper
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, hy⟩ := hs x
    exact hy ▸ y.property

theorem irreducible_encode_iff : (encode C).Irreducible ↔ C.Irreducible := by
  rw [irreducible_iff_noProperFreeDecomposition]
  constructor
  · intro h
    constructor
    intro d
    exact h ⟨encodedDecomposition C d⟩
  · intro h hd
    obtain ⟨d⟩ := hd
    exact h.false (typedDecomposition C d)

end CCO.UnaryHN.Raw
