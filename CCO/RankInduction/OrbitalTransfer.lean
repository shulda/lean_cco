import CCO.RankInduction.OrbitalEquivalence
import CCO.Owners.Provider.FiniteBase

/-! Ordinary EPPA is unchanged by a literal equivariant identification
of ambient carriers. Every sparse partial request is transported, and
the finite witness is chosen once before those requests. -/

namespace CCO.RankInduction
noncomputable section
open Owners.Product Owners.Provider

variable {G A B U V : Type*} [Group G] [MulAction G A] [MulAction G B]
variable {ι : U → A} {κ : V → B}

def partialPullAlong (e : A ≃ B)
    (he : ∀ (g : G) a, e (g • a) = g • e a)
    (E : U ≃ V) (hE : ∀ u, κ (E u) = e (ι u))
    (p : OrbitalPartial (G := G) κ) : OrbitalPartial (G := G) ι where
  domain := E ⁻¹' p.domain
  map x := E.symm (p.map ⟨E x.val,x.property⟩)
  injective := by
    intro x y hxy
    apply Subtype.ext
    exact E.injective (congrArg Subtype.val (p.injective (E.symm.injective hxy)))
  pair x y := by
    apply (orbital_iff e he _ _ _ _).mpr
    have hb : ∀ v, κ v = e (ι (E.symm v)) := fun v => by
      simpa only [Equiv.apply_symm_apply] using hE (E.symm v)
    have hp := p.pair ⟨E x.val,x.property⟩ ⟨E y.val,y.property⟩
    simpa only [hb,Equiv.symm_apply_apply] using hp

theorem eppaFor_equiv (e : A ≃ B)
    (he : ∀ (g : G) a, e (g • a) = g • e a)
    (E : U ≃ V) (hE : ∀ u, κ (E u) = e (ι u)) (a : Set V)
    (ep : EPPAFor (G := G) (ι := ι) (E ⁻¹' a)) :
    EPPAFor (G := G) (ι := κ) a := by
  intro p dom ran
  let q := partialPullAlong e he E hE p
  have qdom : q.domain ⊆ E ⁻¹' a := fun _ hx => dom hx
  have qran : ∀ x, q.map x ∈ E ⁻¹' a := by
    intro x
    change E (E.symm (p.map ⟨E x.val,x.property⟩)) ∈ a
    rw [Equiv.apply_symm_apply]
    exact ran _
  obtain ⟨β,hβ⟩ := ep q qdom qran
  refine ⟨fullAutEquivOf e he E hE β,?_⟩
  intro x
  let x' : q.domain := ⟨E.symm x.val,by
    change E (E.symm x.val) ∈ p.domain
    simpa only [Equiv.apply_symm_apply] using x.property⟩
  have hmap : q.map x' = E.symm (p.map x) := by
    change E.symm (p.map ⟨E (E.symm x.val),_⟩) = E.symm (p.map x)
    congr 1
    apply congrArg p.map
    exact Subtype.ext (E.apply_symm_apply x.val)
  change E (β.val (E.symm x.val)) = p.map x
  calc
    _ = E (q.map x') := congrArg E (hβ x')
    _ = E (E.symm (p.map x)) := congrArg E hmap
    _ = _ := E.apply_symm_apply _

theorem ordinaryEPPA_equiv (e : A ≃ B)
    (he : ∀ (g : G) a, e (g • a) = g • e a)
    (ep : OrdinaryEPPA G A) : OrdinaryEPPA G B := by
  intro T finiteT
  let T' : Set A := e ⁻¹' T
  have finiteT' : T'.Finite := finiteT.preimage e.injective.injOn
  let E : T' ≃ T := {
    toFun x := ⟨e x.val,x.property⟩
    invFun x := ⟨e.symm x.val,by
      change e (e.symm x.val) ∈ T
      simpa only [Equiv.apply_symm_apply] using x.property⟩
    left_inv x := Subtype.ext (e.symm_apply_apply x.val)
    right_inv x := Subtype.ext (e.apply_symm_apply x.val) }
  obtain ⟨C,finiteC,f,pair,extensions⟩ := ep T' finiteT'
  let D := e '' C
  let F := subimageEquiv e C
  let embedding : T ↪ D := {
    toFun x := F (f (E.symm x))
    inj' := fun _ _ h => E.symm.injective (f.injective (F.injective h)) }
  refine ⟨D,finiteC.image e,embedding,?_,?_⟩
  · intro x y
    have hp := (orbital_iff e he _ _ _ _).mp (pair (E.symm x) (E.symm y))
    have hback (x : T) : e (E.symm x).val = x.val :=
      congrArg Subtype.val (E.apply_symm_apply x)
    change GroupActions.orbital (G := G) x.val y.val
      (e (f (E.symm x)).val) (e (f (E.symm y)).val)
    simpa only [hback] using hp
  · intro p
    let q := partialPullAlong e he E (fun _ => rfl) p
    obtain ⟨β,hβ⟩ := extensions q
    refine ⟨fullAutEquiv e he C β,?_⟩
    intro x
    let x' : q.domain := ⟨E.symm x.val,by
      change E (E.symm x.val) ∈ p.domain
      simpa only [Equiv.apply_symm_apply] using x.property⟩
    have hmap : q.map x' = E.symm (p.map x) := by
      change E.symm (p.map ⟨E (E.symm x.val),_⟩) = E.symm (p.map x)
      congr 1
      apply congrArg p.map
      exact Subtype.ext (E.apply_symm_apply x.val)
    change (fullAutEquiv e he C β).val (F (f (E.symm x.val))) =
      F (f (E.symm (p.map x)))
    rw [fullAutEquiv_apply]
    exact congrArg F ((hβ x').trans (congrArg f hmap))

end
end CCO.RankInduction
