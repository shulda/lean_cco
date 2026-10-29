import CCO.Owners.Provider.Requests

/-! A partial map on the original finite input remains a partial map
on an enlarged seed, with exactly the same sparse domain and values. -/
namespace CCO.Owners.Provider
open Product
variable {G A O U V : Type*} [Group G] [MulAction G A] [MulAction G O]
variable {ι : U → A} {κ : V → A}

noncomputable def partialDomainLift (e : U ↪ V) (p : OrbitalPartial (G := G) ι)
    (v : e '' p.domain) : p.domain :=
  ⟨Classical.choose v.property,(Classical.choose_spec v.property).1⟩

@[simp] theorem partialDomainLift_value (e : U ↪ V)
    (p : OrbitalPartial (G := G) ι) (v : e '' p.domain) :
    e (partialDomainLift e p v).val = v.val := (Classical.choose_spec v.property).2

noncomputable def pushPartial (e : U ↪ V) (he : ∀ u, κ (e u) = ι u)
    (p : OrbitalPartial (G := G) ι) : OrbitalPartial (G := G) κ where
  domain := e '' p.domain
  map v := e (p.map (partialDomainLift e p v))
  injective := by
    intro v w h
    have hw := p.injective (e.injective h)
    apply Subtype.ext
    exact (partialDomainLift_value e p v).symm.trans
      ((congrArg (fun x : p.domain => e x.val) hw).trans (partialDomainLift_value e p w))
  pair v w := by
    have hh := p.pair (partialDomainLift e p v) (partialDomainLift e p w)
    have hι (z : e '' p.domain) : κ z.val = ι (partialDomainLift e p z).val := by
      rw [← partialDomainLift_value e p z,he]
    simpa only [he,hι] using hh

@[simp] theorem pushPartial_map (e : U ↪ V) (he : ∀ u, κ (e u) = ι u)
    (p : OrbitalPartial (G := G) ι) (x : p.domain) :
    (pushPartial e he p).map ⟨e x.val,⟨x.val,x.property,rfl⟩⟩ = e (p.map x) := by
  change e (p.map (partialDomainLift e p _)) = e (p.map x)
  congr 1
  congr 1
  apply Subtype.ext
  apply e.injective
  exact partialDomainLift_value e p _

namespace OwnerRequest
variable {π : A → O} {T D : Set A} {B : Set O}
variable {hT : ∀ x : T, π x.val ∈ B} (r : OwnerRequest (G := G) π T B hT)

noncomputable def enlarge (inc : T ⊆ D) (hD : ∀ x : D, π x.val ∈ B) :
    OwnerRequest (G := G) π D B hD := by
  let e : T ↪ D := ⟨fun x => ⟨x.val,inc x.property⟩,
    fun _ _ h => Subtype.ext (congrArg (fun z : D => z.val) h)⟩
  let p := pushPartial (ι := (Subtype.val : T → A)) (κ := (Subtype.val : D → A)) e (fun _ => rfl) r.part
  refine ⟨p,r.owner,?_⟩
  intro x
  let a := partialDomainLift e r.part x
  have ha : (e a.val).val = x.val.val := congrArg Subtype.val (partialDomainLift_value e r.part x)
  change π (r.part.map a).val = (r.owner.val (ownerProjection π D B hD x.val)).val
  rw [r.compatible a]
  apply congrArg (fun b : B => (r.owner.val b).val)
  apply Subtype.ext
  exact congrArg π ha

noncomputable def enlargeDomain (inc : T ⊆ D)
    (hD : ∀ x : D, π x.val ∈ B) (x : r.part.domain) :
    (r.enlarge inc hD).part.domain :=
  ⟨⟨x.val.val,inc x.val.property⟩,⟨x.val,x.property,rfl⟩⟩

@[simp] theorem enlargeDomain_value (inc : T ⊆ D)
    (hD : ∀ x : D, π x.val ∈ B) (x : r.part.domain) :
    (r.enlargeDomain inc hD x).val.val = x.val.val := rfl

@[simp] theorem enlarge_map (inc : T ⊆ D)
    (hD : ∀ x : D, π x.val ∈ B) (x : r.part.domain) :
    ((r.enlarge inc hD).part.map (r.enlargeDomain inc hD x)).val =
      (r.part.map x).val := by
  let e : T ↪ D := ⟨fun x => ⟨x.val,inc x.property⟩,
    fun _ _ h => Subtype.ext (congrArg (fun z : D => z.val) h)⟩
  exact congrArg Subtype.val (pushPartial_map (ι := (Subtype.val : T → A)) (κ := (Subtype.val : D → A)) e (fun _ => rfl) r.part x)

end OwnerRequest
end CCO.Owners.Provider
