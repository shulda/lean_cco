import CCO.Selectors.Basic

/-! Typed contractions of current ORIGINAL exact families, and composition. -/
universe u v w
namespace CCO.Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

structure Contraction (J K : Family S) where
  toFun : ∀ {i j}, S.Menu i j → S.Menu i j
  maps : ∀ {i j} {D : S.Menu i j}, (⟨i,j,D⟩ : TaggedMenu S) ∈ J →
    (⟨i,j,toFun D⟩ : TaggedMenu S) ∈ K
  conservative : ∀ {i j} {D : S.Menu i j}, (⟨i,j,D⟩ : TaggedMenu S) ∈ J → toFun D ⊆ D
  opposite : ∀ {i j} {D : S.Menu i j}, (⟨i,j,D⟩ : TaggedMenu S) ∈ J →
    toFun (S.opposite D) = S.opposite (toFun D)
  heredity : ∀ {i j} {E D : S.Menu i j},
    (⟨i,j,E⟩ : TaggedMenu S) ∈ J → (⟨i,j,D⟩ : TaggedMenu S) ∈ J →
    E ⊆ D → (E ∩ toFun D).Nonempty → toFun E = E ∩ toFun D
  pc : ∀ {i j k} {A : S.Menu i j} {B : S.Menu j k} {C : S.Menu i k},
    (⟨i,j,A⟩ : TaggedMenu S) ∈ J → (⟨j,k,B⟩ : TaggedMenu S) ∈ J →
    (⟨i,k,C⟩ : TaggedMenu S) ∈ J → S.PC A B C → S.PC (toFun A) (toFun B) (toFun C)

namespace Contraction
variable {S} {J K L : Family S}

def id (J : Family S) : Contraction S J J where
  toFun D := D
  maps h := h
  conservative _ := Set.Subset.rfl
  opposite _ := rfl
  heredity _ _ h _ := (Set.inter_eq_left.mpr h).symm
  pc _ _ _ h := h

def comp (R : Contraction S J K) (T : Contraction S K L) : Contraction S J L where
  toFun D := T.toFun (R.toFun D)
  maps h := T.maps (R.maps h)
  conservative h := (T.conservative (R.maps h)).trans (R.conservative h)
  opposite h := by rw [R.opposite h, T.opposite (R.maps h)]
  heredity := by
    intro i j E D hE hD hsub hmeet
    have hTD := T.conservative (R.maps hD)
    have hm : (E ∩ R.toFun D).Nonempty := by
      obtain ⟨x,hx,hy⟩ := hmeet
      exact ⟨x,hx,hTD hy⟩
    have hRE := R.heredity hE hD hsub hm
    have hsub' : R.toFun E ⊆ R.toFun D := by rw [hRE]; exact Set.inter_subset_right
    have hm' : (R.toFun E ∩ T.toFun (R.toFun D)).Nonempty := by
      obtain ⟨x,hx,hy⟩ := hmeet
      exact ⟨x, hRE ▸ ⟨hx,hTD hy⟩, hy⟩
    rw [T.heredity (R.maps hE) (R.maps hD) hsub' hm', hRE]
    ext x
    exact ⟨fun h => ⟨h.1.1,h.2⟩, fun h => ⟨⟨h.1,hTD h.2⟩,h.2⟩⟩
  pc hA hB hC h := T.pc (R.maps hA) (R.maps hB) (R.maps hC) (R.pc hA hB hC h)

theorem exact (R : Contraction S J K) (hK : CurrentFamily S K)
    {i j} {D : S.Menu i j} (hD : (⟨i,j,D⟩ : TaggedMenu S) ∈ J) :
    StrongExact.Exact S (R.toFun D) := hK.exact (R.maps hD)

end Contraction
end CCO.Selectors
