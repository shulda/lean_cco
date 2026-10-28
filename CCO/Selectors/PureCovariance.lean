import CCO.Selectors.PureAction
import Mathlib.Algebra.Group.PUnit

/-! Actual visible gates transport under pure tag actions because literal
names, parallel endpoints, and active filter menus all transport. -/
universe u v w z t
namespace CCO.Selectors
variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
namespace PureTagAction
variable {Λ : Type z} [Group Λ] {N : Type t} (A : PureTagAction S Λ N)

private theorem names_overlap_iff {i j} (P D : S.Menu i j) :
    (names S A.label ⟨i,j,P⟩ ∩ names S A.label ⟨i,j,D⟩).Nonempty ↔
      (P ∩ D).Nonempty := by
  rw [←A.names_inter]
  constructor
  · rintro ⟨n,a,ha,han⟩
    exact ⟨a,ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨A.label a,a,ha,rfl⟩

/-- A name-level description of the actual gate, with no cross-palette meet. -/
theorem mem_names_gateTag (F : Family S) (D : TaggedMenu S) (n : N) :
    n ∈ names S A.label (gateTag S F D) ↔
      n ∈ names S A.label D ∧
      ∀ T : TaggedMenu S, T ∈ F → Parallel S T D →
        (names S A.label T ∩ names S A.label D).Nonempty → n ∈ names S A.label T := by
  rcases D with ⟨i,j,D⟩
  constructor
  · rintro ⟨a,ha,han⟩
    refine ⟨⟨a,ha.1,han⟩,?_⟩
    rintro ⟨k,l,T⟩ hT ⟨hi,hj⟩ hm
    cases hi; cases hj
    have hTD : (T ∩ D).Nonempty := (A.names_overlap_iff T D).mp hm
    exact ⟨a,ha.2 T hT hTD,han⟩
  · rintro ⟨⟨a,ha,han⟩,h⟩
    refine ⟨a,⟨ha,?_⟩,han⟩
    intro T hT hTD
    obtain ⟨b,hb,hbn⟩ := h ⟨i,j,T⟩ hT ⟨rfl,rfl⟩ ((A.names_overlap_iff T D).mpr hTD)
    have hba : b = a := A.label_injective i j (hbn.trans han.symm)
    exact hba ▸ hb

private theorem names_gateTag_act_subset (F : Family S) (hF : A.Invariant F)
    (g : Λ) (D : TaggedMenu S) :
    names S A.label (gateTag S F D) ⊆ names S A.label (gateTag S F (A.act g D)) := by
  intro n hn
  obtain ⟨hnD,h⟩ := (A.mem_names_gateTag F D n).mp hn
  apply (A.mem_names_gateTag F (A.act g D) n).mpr
  refine ⟨?_,?_⟩
  · simpa only [A.literal] using hnD
  · intro T hT hp hm
    have hInvT : A.act g⁻¹ T ∈ F := hF g⁻¹ T hT
    have hp' : Parallel S (A.act g⁻¹ T) D := by
      simpa only [A.inv_act] using (A.parallel g⁻¹ T (A.act g D)).mpr hp
    have hm' : (names S A.label (A.act g⁻¹ T) ∩ names S A.label D).Nonempty := by
      simpa only [A.literal] using hm
    simpa only [A.literal] using h (A.act g⁻¹ T) hInvT hp' hm'

/-- Literal gate names are unchanged by a pure tag permutation. -/
theorem names_gateTag_act (F : Family S) (hF : A.Invariant F)
    (g : Λ) (D : TaggedMenu S) :
    names S A.label (gateTag S F (A.act g D)) = names S A.label (gateTag S F D) := by
  apply Set.Subset.antisymm
  · simpa only [A.inv_act] using A.names_gateTag_act_subset F hF g⁻¹ (A.act g D)
  · exact A.names_gateTag_act_subset F hF g D

/-- Covariance is PROVED for the actual gate, rather than being a selector premise. -/
theorem act_gateTag (F : Family S) (hF : A.Invariant F) (g : Λ) (D : TaggedMenu S) :
    A.act g (gateTag S F D) = gateTag S F (A.act g D) := by
  apply A.tagged_names_injective
  · constructor
    · rw [A.source]
      exact (A.source g D).symm
    · rw [A.target]
      exact (A.target g D).symm
  · rw [A.literal]
    exact (A.names_gateTag_act F hF g D).symm

theorem invariant_gateImage (F J : Family S) (hF : A.Invariant F) (hJ : A.Invariant J) :
    A.Invariant (gateImage S F J) := by
  rintro g _ ⟨D,hD,rfl⟩
  exact ⟨A.act g D,hJ g D hD,(A.act_gateTag F hF g D).symm⟩

theorem covariant_id (J : Family S) : A.Covariant (Contraction.id J) := by
  rintro g ⟨i,j,D⟩ hD
  rfl

theorem covariant_comp {J K L : Family S} {R : Contraction S J K} {T : Contraction S K L}
    (hR : A.Covariant R) (hT : A.Covariant T) : A.Covariant (R.comp T) := by
  intro g D hD
  have ht := hT g ⟨D.1,D.2.1,R.toFun D.2.2⟩ (R.maps hD)
  rw [hR g D hD] at ht
  exact ht

/-- Trivial tag actions use tagged actual atoms as their literal names. -/
def trivial : PureTagAction S PUnit.{1} (Σ i : ι, Σ j : ι, S.Atom i j) where
  tag _ := Equiv.refl _
  act _ := Equiv.refl _
  one _ := rfl
  mul _ _ _ := rfl
  source _ _ := rfl
  target _ _ := rfl
  label {i j} a := ⟨i,j,a⟩
  label_injective i j := by
    intro a b h
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using h
  literal _ _ := rfl
  exact _ _ := Iff.rfl
  opposite _ _ := rfl
  product := by intro g P Q R h; exact h

@[simp] theorem trivial_act (D : TaggedMenu S) (g : PUnit.{1}) :
    (trivial (S := S)).act g D = D := rfl

theorem trivial_covariant {J K : Family S} (R : Contraction S J K) :
    (trivial (S := S)).Covariant R := by
  intro g D hD
  rfl

end PureTagAction
end CCO.Selectors
