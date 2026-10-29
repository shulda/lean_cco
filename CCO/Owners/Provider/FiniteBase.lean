import CCO.Owners.Provider.Induced
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-! Ordinary EPPA, ambient realization, and a single finite-base host.
No coherence and no countability enter this generic branch. -/
namespace CCO.Owners.Provider
open Product
open scoped Pointwise
variable {G A O : Type*} [Group G] [MulAction G A] [MulAction G O]

/-- Ordinary EPPA of the actual age: an arbitrary finite induced input
embeds into one finite induced witness extending all its partial maps.
The embedding is not assumed to be the original inclusion. -/
def OrdinaryEPPA (G : Type*) [Group G] (A : Type*) [MulAction G A] : Prop :=
  ∀ T : Set A, T.Finite → ∃ C : Set A, C.Finite ∧
    ∃ e : T ↪ C,
      (∀ x y : T, GroupActions.orbital (G := G) x.val y.val (e x).val (e y).val) ∧
      ∀ p : OrbitalPartial (G := G) (Subtype.val : T → A),
        ∃ β : OrbitalAut G A (Subtype.val : C → A),
          ∀ x : p.domain, β.val (e x.val) = e (p.map x)

/-- Finite tuple homogeneity in the genuine original orbital language. -/
def OrbitalHomogeneous (G : Type*) [Group G] (A : Type*) [MulAction G A] : Prop :=
  ∀ T : Set A, T.Finite → ∀ f : T → A,
    (∀ x y : T, GroupActions.orbital (G := G) (f x) (f y) x.val y.val) →
    ∃ g : G, ∀ x : T, g • f x = x.val

theorem orbital_smul_both (g : G) {a b x y : A}
    (h : GroupActions.orbital (G := G) a b x y) :
    GroupActions.orbital (G := G) (g • a) (g • b) (g • x) (g • y) := by
  obtain ⟨k,hkx,hky⟩ := h
  refine ⟨g*k*g⁻¹,?_,?_⟩ <;> simp only [mul_smul,inv_smul_smul,hkx,hky]

noncomputable def translateEquiv (g : G) (C : Set A) : C ≃ ((fun x : A => g • x) '' C) where
  toFun x := ⟨g • x.val,by exact ⟨x.val,x.property,rfl⟩⟩
  invFun x := ⟨g⁻¹ • x.val,by
    obtain ⟨y,hy,hgy⟩ := x.property
    rw [← hgy,inv_smul_smul]
    exact hy⟩
  left_inv x := Subtype.ext (inv_smul_smul _ _)
  right_inv x := Subtype.ext (smul_inv_smul _ _)

noncomputable def translateAut (g : G) (C : Set A)
    (β : OrbitalAut G A (Subtype.val : C → A)) :
    OrbitalAut G A (Subtype.val : ((fun x : A => g • x) '' C) → A) := by
  let e := translateEquiv g C
  refine ⟨e.permCongr β.val,(mem_orbitalAut_iff _).mpr ?_⟩
  intro x y
  have hx : g • (e.symm x).val = x.val := congrArg Subtype.val (e.apply_symm_apply x)
  have hy : g • (e.symm y).val = y.val := congrArg Subtype.val (e.apply_symm_apply y)
  have heval : ∀ z : C, (e z).val = g • z.val := fun _ => rfl
  have hh := orbital_smul_both g (orbitalAut_pair β (e.symm x) (e.symm y))
  simpa only [hx,hy,Equiv.permCongr_apply,heval] using hh

@[simp] theorem translateAut_apply (g : G) (C : Set A)
    (β : OrbitalAut G A (Subtype.val : C → A))
    (x : (fun x : A => g • x) '' C) :
    ((translateAut g C β).val x).val =
      g • (β.val ((translateEquiv g C).symm x)).val := by
  simp only [translateAut,Equiv.permCongr_apply]
  rfl

/-- Homogeneity realizes the ordinary age witness over the ORIGINAL
finite subset. This is a proved change of embedding, not an extra EPPA premise. -/
theorem eppa_over_original (hom : OrbitalHomogeneous G A) (ep : OrdinaryEPPA G A)
    (T : Set A) (hT : T.Finite) :
    ∃ C : Set A, C.Finite ∧ ∃ hTC : T ⊆ C,
      ∀ p : OrbitalPartial (G := G) (Subtype.val : T → A),
      ∃ β : OrbitalAut G A (Subtype.val : C → A),
        ∀ x : p.domain, (β.val ⟨x.val.val,hTC x.val.property⟩).val =
          (p.map x).val := by
  obtain ⟨C,hC,e,he,hep⟩ := ep T hT
  have hrev : ∀ x y : T,
      GroupActions.orbital (G := G) (e x).val (e y).val x.val y.val := by
    intro x y
    obtain ⟨g,hgx,hgy⟩ := he x y
    exact ⟨g⁻¹,by rw [← hgx,inv_smul_smul],by rw [← hgy,inv_smul_smul]⟩
  obtain ⟨g,hg⟩ := hom T hT (fun x => (e x).val) hrev
  let D : Set A := (fun x : A => g • x) '' C
  have hD : D.Finite := hC.image (fun x : A => g • x)
  have hTD : T ⊆ D := by
    intro x hx
    exact ⟨(e ⟨x,hx⟩).val,(e ⟨x,hx⟩).property,hg ⟨x,hx⟩⟩
  refine ⟨D,hD,hTD,?_⟩
  intro p
  obtain ⟨β,hβ⟩ := hep p
  refine ⟨translateAut g C β,?_⟩
  intro x
  have hx : (translateEquiv g C).symm ⟨x.val.val,hTD x.val.property⟩ = e x.val := by
    apply (translateEquiv g C).injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext (hg x.val).symm
  rw [translateAut_apply]
  rw [hx,hβ x]
  exact hg (p.map x)

end CCO.Owners.Provider
