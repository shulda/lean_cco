import CCO.GuardedTwoRoot.UnarySource

/-! A displayed GENUINE partial unary graph joins its own two OLD
endpoints into one generated closure. This does not join arbitrary
ancestors of related descendants and assumes no ambient completion. -/

universe u v
namespace CCO.GuardedTwoRoot
open CCO.UnarySupport CCO.UnarySupport.Structure
variable {L : Signature.{u}} {P : Type v} (F : Structure L P)

theorem displayed_unary_pair_closure (f : L.Func) (b c : P) (h : c ∈ F.func f b) :
    F.closure {b,c} = F.closure {b} := by
  apply Set.Subset.antisymm
  · apply F.closure_minimal (F.isClosed_closure {b})
    intro x hx
    rcases hx with hxb | hxc
    · rw [hxb]
      exact F.mem_closureAt b
    · have hxc' : x = c := hxc
      rw [hxc']
      exact F.isClosed_closure {b} f b (F.mem_closureAt b) h
  · apply F.closure_mono
    intro x hx
    exact Or.inl hx

theorem displayed_unary_pair_one_generated (f : L.Func) (b c : P) (h : c ∈ F.func f b) :
    (F.closureStructure {b,c}).OneGenerated := by
  let b' : F.closure {b,c} := ⟨b,F.subset_closure _ (by simp)⟩
  refine ⟨b',Set.eq_univ_of_forall ?_⟩
  intro x
  have hImage := F.closure_induce_image (F.isClosed_closure {b,c}) {b'}
  have hSeed : Subtype.val '' ({b'} : Set (F.closure {b,c})) = {b} := by
    simp only [Set.image_singleton,b']
  rw [hSeed] at hImage
  have hx : x.val ∈ F.closure {b} := displayed_unary_pair_closure F f b c h ▸ x.property
  obtain ⟨y,hy,he⟩ := hImage.symm ▸ hx
  exact (Subtype.ext he : y = x) ▸ hy

theorem displayed_unary_pair_irreducible (f : L.Func) (b c : P) (h : c ∈ F.func f b) :
    (F.closureStructure {b,c}).Irreducible := by
  obtain ⟨root,hRoot⟩ := displayed_unary_pair_one_generated F f b c h
  exact irreducible_of_generated _ root hRoot

end CCO.GuardedTwoRoot
