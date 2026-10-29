import CCO.Owners.Provider.Canonical
import CCO.Owners.Product.Matching

/-! The constructed provider supplies the precise downstream B019
interfaces on arbitrary sparse input domains and on prescribed target points. -/
universe v w t
namespace CCO.Owners.Provider
open Product
variable {A O : Type v} {G : Type t} [Group G] [MulAction G A] [MulAction G O]
variable {S : AtomicSource.{0,v,w} Unit (fun _ => A)} {H : HomogeneousSource S G}
variable {π : A → O} {equivπ : ∀ (g : G) x, π (g • x) = g • π x}
variable {B : Set O} {T : Set A} {overT : ∀ x : T, π x.val ∈ B}
variable (W : OwnerWitness S H π equivπ B T overT)

/-- Actual sparse partial maps of the original input, viewed inside the
finite witness, extend with their prescribed ENTIRE owner component. -/
theorem OwnerWitness.prescribed_eppa :
    PrescribedEPPAFor W.quotient {x : W.carrier | x.val ∈ T} := by
  intro p hdom hmap γ hcompat
  let q : OrbitalPartial (G := G) (Subtype.val : T → A) := {
    domain := {x | (⟨x.val,W.contains x.property⟩ : W.carrier) ∈ p.domain}
    map := fun x => ⟨(p.map ⟨⟨x.val.val,W.contains x.val.property⟩,x.property⟩).val,
      hmap ⟨⟨x.val.val,W.contains x.val.property⟩,x.property⟩⟩
    injective := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      have hv := congrArg (fun z : T => z.val) hxy
      have hp := p.injective (Subtype.ext hv)
      exact congrArg (fun z : p.domain => z.val.val) hp
    pair := fun x y => p.pair
      ⟨⟨x.val.val,W.contains x.val.property⟩,x.property⟩
      ⟨⟨y.val.val,W.contains y.val.property⟩,y.property⟩ }
  let r : OwnerRequest (G := G) π T B overT := {
    part := q
    owner := γ
    compatible := by
      intro x
      have hh := hcompat ⟨⟨x.val.val,W.contains x.val.property⟩,x.property⟩
      exact congrArg Subtype.val hh }
  obtain ⟨β,hβ,howner⟩ := W.extensions r
  refine ⟨β,?_,howner⟩
  intro x
  let a : T := ⟨x.val.val,hdom x.property⟩
  let y : q.domain := ⟨a,x.property⟩
  apply Subtype.ext
  exact hβ y

/-- The genuine finite owner action supplies the second-factor point
provider of the independent nonnested B019 theorem. No T-to-owner map
and no group section are introduced. -/
theorem OwnerWitness.product_prescribed
    {KD GT Y Z : Type*} [Group KD] [Group GT] [MulAction KD Y] [MulAction GT Z]
    (ρ : KD →* OrbitalAut G O (Subtype.val : B → O)) (owner : Y → B)
    (eqOwner : ∀ g x, owner (g • x) = ρ g • owner x)
    (τ : KD →* GT) (target : Y → Z) (lift : GroupActions.PrescribedLift τ target) :
    letI := pullbackAction ρ W.quotient.action owner W.quotient.projection
      eqOwner (fun g x => (W.quotient.action_projection g x).symm)
    GroupActions.PrescribedLift (matchingTarget ρ W.quotient.action τ)
      (fun x : Pullback owner W.quotient.projection => target x.val.1) :=
  prescribed_nonnested ρ W.quotient.action owner W.quotient.projection
    eqOwner (fun g x => (W.quotient.action_projection g x).symm) τ target lift W.prescribed

end CCO.Owners.Provider
