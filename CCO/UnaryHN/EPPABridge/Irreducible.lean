import CCO.UnaryHN.EPPABridge.Encoding
import PartiteConstruction.Structure.FreeAmalgamationClass

/-! Closed substructures and free decompositions survive removal of nullary
symbols. Empty tuples lie in every side, including an empty side. -/

universe u v
namespace CCO.UnaryHN.Native.EPPABridge
open StructuralRamsey
open StructuralRamsey.Structure

theorem decode_closed_iff {L : Language.{u}} {V : Type v}
    (P : NullaryProfile L) (A : AllThoseEPPA.Structure (positiveLanguage L) V)
    (S : Set V) : (decode P A).IsClosed S ↔ A.IsClosed S := by
  simpa using (encode_closed_iff (decode P A) S).symm

theorem native_irreducible_of_encode {L : Language.{u}} {V : Type v}
    (A : Structure L V) (hA : (encode A).IsIrreducible) : A.Irreducible := by
  rw [irreducible_iff_noProperFreeDecomposition]
  rintro ⟨d⟩
  let S : Set V := Set.range d.leftIn
  let T : Set V := Set.range d.rightIn
  let split : AllThoseEPPA.Structure.FreeDecomposition (encode A) := {
    left := S
    right := T
    left_closed := (encode_closed_iff A S).mpr d.leftIn.range_isClosed
    right_closed := (encode_closed_iff A T).mpr d.rightIn.range_isClosed
    cover := by
      apply Set.eq_univ_of_forall
      intro x
      rcases d.free.covers x with ⟨a, ha⟩ | ⟨b, hb⟩
      · exact Or.inl ⟨a, ha.symm⟩
      · exact Or.inr ⟨b, hb.symm⟩
    left_proper := by intro h; exact d.leftProper (Set.range_eq_univ.mp h)
    right_proper := by intro h; exact d.rightProper (Set.range_eq_univ.mp h)
    rel_local := by
      intro n ⟨R, hR, hp⟩ xs hxs
      subst n
      rcases (d.free.rel_iff R xs).mp hxs with ⟨ys, _, he⟩ | ⟨ys, _, he⟩
      · exact Or.inl (fun i => ⟨ys i, (congrFun he i).symm⟩)
      · exact Or.inr (fun i => ⟨ys i, (congrFun he i).symm⟩)
    func_cross_empty := by
      intro n ⟨F, hF⟩ xs hcross
      subst n
      ext y
      constructor
      · intro hy
        rcases (d.free.func_iff F xs y).mp hy with ⟨ys, z, _, he, _⟩ | ⟨ys, z, _, he, _⟩
        · exact False.elim (hcross (Or.inl (fun i => ⟨ys i, (congrFun he i).symm⟩)))
        · exact False.elim (hcross (Or.inr (fun i => ⟨ys i, (congrFun he i).symm⟩)))
      · exact False.elim }
  exact hA.false split

def inducedEmbedding {L : Language.{u}} {V : Type v} (A : Structure L V)
    (S T : Set V) (hS : A.IsClosed S) (hT : A.IsClosed T) (hST : S ⊆ T) :
    Embedding (A.induce S hS) (A.induce T hT) where
  toFun x := ⟨x.1, hST x.2⟩
  injective := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : T => z.1) h)
  map_rel_iff := fun _ _ => Iff.rfl
  map_func := by
    intro F xs
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      have hyS : y.1 ∈ S := hS F (Subtype.val ∘ xs) (fun i => (xs i).2) hy
      exact ⟨⟨y.1, hyS⟩, hy, rfl⟩

theorem encode_irreducible_of_native {L : Language.{u}} {V : Type v}
    (A : Structure L V) (hA : A.Irreducible) : (encode A).IsIrreducible := by
  classical
  constructor
  intro d
  let S := d.left
  let T := d.right
  have hS : A.IsClosed S := (encode_closed_iff A S).mp d.left_closed
  have hT : A.IsClosed T := (encode_closed_iff A T).mp d.right_closed
  have hST : A.IsClosed (S ∩ T) := by
    intro F xs hxs y hy
    exact ⟨hS F xs (fun i => (hxs i).1) hy, hT F xs (fun i => (hxs i).2) hy⟩
  let fS := inducedEmbedding A (S ∩ T) S hST hS Set.inter_subset_left
  let fT := inducedEmbedding A (S ∩ T) T hST hT Set.inter_subset_right
  let iS := A.inclusion S hS
  let iT := A.inclusion T hT
  have hfree : IsFreeAmalgam fS fT iS iT := {
    covers := by
      intro x
      have hx : x ∈ S ∪ T := by rw [d.cover]; trivial
      rcases hx with hx | hx
      · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
      · exact Or.inr ⟨⟨x, hx⟩, rfl⟩
    overlap := by
      intro x y
      constructor
      · intro hxy
        have h : x.1 = y.1 := hxy
        refine ⟨⟨x.1, x.2, ?_⟩, ?_, ?_⟩
        · simpa [h] using y.2
        · rfl
        · apply Subtype.ext
          exact h.symm
      · rintro ⟨z, rfl, rfl⟩
        rfl
    rel_iff := by
      intro R xs
      constructor
      · intro hr
        have hsides : (∀ i, xs i ∈ S) ∨ (∀ i, xs i ∈ T) := by
          by_cases hp : 0 < L.relArity R
          · exact d.rel_local ⟨R, rfl, hp⟩ xs hr
          · left
            intro i
            have := i.2
            omega
        rcases hsides with hs | ht
        · exact Or.inl ⟨fun i => ⟨xs i, hs i⟩, hr, rfl⟩
        · exact Or.inr ⟨fun i => ⟨xs i, ht i⟩, hr, rfl⟩
      · rintro (⟨ys, hr, rfl⟩ | ⟨ys, hr, rfl⟩)
        · exact hr
        · exact hr
    func_iff := by
      intro F xs y
      constructor
      · intro hy
        by_cases hs : ∀ i, xs i ∈ S
        · exact Or.inl ⟨fun i => ⟨xs i, hs i⟩, ⟨y, hS F xs hs hy⟩, hy, rfl, rfl⟩
        · by_cases ht : ∀ i, xs i ∈ T
          · exact Or.inr ⟨fun i => ⟨xs i, ht i⟩, ⟨y, hT F xs ht hy⟩, hy, rfl, rfl⟩
          · have hemp := d.func_cross_empty ⟨F, rfl⟩ xs (not_or.mpr ⟨hs, ht⟩)
            have hym : y ∈ (encode A).func ⟨F, rfl⟩ xs := hy
            rw [hemp] at hym
            exact False.elim hym
      · rintro (⟨ys, z, hz, rfl, rfl⟩ | ⟨ys, z, hz, rfl, rfl⟩)
        · exact hz
        · exact hz }
  rcases hA hfree (Embedding.id A) with hs | ht
  · apply d.left_proper
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨z, hz⟩ := hs x
    change x ∈ S
    simpa [show x = z.1 from hz] using z.2
  · apply d.right_proper
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨z, hz⟩ := ht x
    change x ∈ T
    simpa [show x = z.1 from hz] using z.2

end CCO.UnaryHN.Native.EPPABridge
