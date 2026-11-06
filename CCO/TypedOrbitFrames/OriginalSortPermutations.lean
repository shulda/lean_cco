import CCO.TerminalPowers.FullSource
import Mathlib.Logic.Equiv.Basic

/-! Exact conversion of a sort-preserving permutation of the tagged
original universe to its family of named-sort permutations. Only actual
old colours enter the full original automorphism group. -/

namespace CCO.TypedOrbitFrames

universe u v w
variable {ι : Type u} {X : ι → Type v}

def originalSigmaFibreEquiv (i : ι) : X i ≃ {p : Sigma X // p.1 = i} where
  toFun x := ⟨⟨i,x⟩,rfl⟩
  invFun p := p.property ▸ p.val.2
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨⟨j,x⟩,h⟩
    change j = i at h
    cases h
    rfl

theorem original_sigma_fibre_equiv_symm_tag (i : ι) (p : {p : Sigma X // p.1 = i}) :
    (⟨i,(originalSigmaFibreEquiv i).symm p⟩ : Sigma X) = p.val := by
  rcases p with ⟨⟨j,x⟩,h⟩
  change j = i at h
  cases h
  rfl

def originalSigmaSortPermutation (e : Equiv.Perm (Sigma X))
    (hs : ∀ p, (e p).1 = p.1) (i : ι) : Equiv.Perm (X i) :=
  (originalSigmaFibreEquiv i).trans
    ((e.subtypeEquiv (fun p => by rw [hs p])).trans (originalSigmaFibreEquiv i).symm)

theorem original_sigma_sort_permutation_tag (e : Equiv.Perm (Sigma X))
    (hs : ∀ p, (e p).1 = p.1) (i : ι) (x : X i) :
    (⟨i,originalSigmaSortPermutation e hs i x⟩ : Sigma X) = e ⟨i,x⟩ :=
  original_sigma_fibre_equiv_symm_tag i ⟨e ⟨i,x⟩,hs ⟨i,x⟩⟩

def originalFullAutOfSigmaPermutation (S : AtomicSource.{u,v,w} ι X)
    (e : Equiv.Perm (Sigma X)) (hs : ∀ p, (e p).1 = p.1)
    (hc : ∀ p q, taggedColour S (e p) (e q) = taggedColour S p q) :
    TerminalPowers.FullAut S :=
  ⟨originalSigmaSortPermutation e hs,by
    intro i j x y
    have h := hc ⟨i,x⟩ ⟨j,y⟩
    rw [← original_sigma_sort_permutation_tag e hs i x,
      ← original_sigma_sort_permutation_tag e hs j y] at h
    simpa only [taggedColour,Sigma.mk.injEq,heq_eq_eq,true_and] using h⟩

end CCO.TypedOrbitFrames
