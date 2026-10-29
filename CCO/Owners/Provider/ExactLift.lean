import CCO.Owners.Provider.Requests
import CCO.Owners.Provider.FiniteBase
import CCO.RawExact.JointLiftingSource
import CCO.RawExact.ActualNestedMaps

/-! Compatibility produces a genuine complete joint partial map, then
the accepted countable joint exact-lifting theorem supplies its actual
ambient automorphism. Every owner of B is in the displayed joint domain. -/
universe v w t
namespace CCO.Owners.Provider
open Product RawExact
variable {A O : Type v} {G : Type t} [Group G] [MulAction G A] [MulAction G O]

theorem source_orbital_homogeneous (S : AtomicSource.{0,v,w} Unit (fun _ => A))
    (H : HomogeneousSource S G) : OrbitalHomogeneous G A := by
  intro T hT f hf
  letI : Finite T := hT.to_subtype
  have hcol : ∀ x y : T,
      taggedColour S (⟨(),f x⟩ : Sigma (fun _ : Unit => A)) ⟨(),f y⟩ =
        taggedColour S ⟨(),x.val⟩ ⟨(),y.val⟩ := by
    intro x y
    obtain ⟨g,hgx,hgy⟩ := hf x y
    have hh := H.preserves_colours g ⟨(),f x⟩ ⟨(),f y⟩
    simpa only [Sigma.smul_mk,hgx,hgy] using hh.symm
  obtain ⟨g,hg⟩ := H.extends_finite_diagram
    (fun x : T => (⟨(),f x⟩ : Sigma (fun _ : Unit => A)))
    (fun x : T => (⟨(),x.val⟩ : Sigma (fun _ : Unit => A))) hcol
  refine ⟨g,?_⟩
  intro x
  simpa only [Sigma.smul_mk,Sigma.mk.injEq,heq_eq_eq,true_and] using hg x

namespace OwnerRequest
variable {π : A → O} {D : Set A} {B : Set O}
variable {hD : ∀ x : D, π x.val ∈ B} (r : OwnerRequest (G := G) π D B hD)

noncomputable def realSend (a : A) : A := by
  classical
  exact if ha : a ∈ D then
    if hp : (⟨a,ha⟩ : D) ∈ r.part.domain then (r.part.map ⟨⟨a,ha⟩,hp⟩).val else a
  else a

noncomputable def ownerSend (b : O) : O := by
  classical
  exact if hb : b ∈ B then (r.owner.val ⟨b,hb⟩).val else b

@[simp] theorem realSend_domain (x : r.part.domain) :
    r.realSend x.val.val = (r.part.map x).val := by
  simp only [realSend,dif_pos x.val.property,dif_pos x.property]

@[simp] theorem ownerSend_base (b : B) : r.ownerSend b.val = (r.owner.val b).val := by
  simp only [ownerSend,dif_pos b.property]

abbrev Joint := JointFamily (fun _ : Unit => A) (fun _ : Unit => O)

def realTag (x : r.part.domain) : Sigma (Joint (A := A) (O := O)) := ⟨.inl (),x.val.val⟩
def ownerTag (r : OwnerRequest (G := G) π D B hD)
    (b : B) : Sigma (Joint (A := A) (O := O)) := ⟨.inr (),b.val⟩

noncomputable def send : ∀ p : Sigma (Joint (A := A) (O := O)),
    Joint (A := A) (O := O) p.1
  | ⟨.inl (),a⟩ => r.realSend a
  | ⟨.inr (),b⟩ => r.ownerSend b

/-- ALL mixed pairs are checked, even c outside the projected real domain. -/
theorem mixed_pair (S : AtomicSource.{0,v,w} Unit (fun _ => A))
    (H : HomogeneousSource S G) (ontoπ : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (x : r.part.domain) (b : B) :
    GroupActions.orbital (G := G) x.val.val b.val
      (r.part.map x).val (r.owner.val b).val := by
  apply (actual_nested_orbit_reduction_of_homogeneous S H (i := ()) id π π
    Function.surjective_id ontoπ (fun _ _ => rfl) equivπ equivπ
    (fun _ => rfl) x.val.val (r.part.map x).val b.val (r.owner.val b).val).mpr
  rw [r.compatible x]
  exact orbitalAut_pair r.owner (ownerProjection π D B hD x.val) b

/-- The actual complete joint map, with no unproved mixed-orbit provider. -/
noncomputable def jointMap (S : AtomicSource.{0,v,w} Unit (fun _ => A))
    (H : HomogeneousSource S G) (ontoπ : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    [Finite D] [Finite B] : FiniteJointPartialIso G (Joint (A := A) (O := O)) := by
  classical
  let U : Set (Sigma (Joint (A := A) (O := O))) :=
    Set.range r.realTag ∪ Set.range r.ownerTag
  have hu : U.Finite := (Set.finite_range r.realTag).union (Set.finite_range _)
  refine ⟨hu.toFinset,r.send,?_⟩
  intro p q hp hq
  have hp' : p ∈ U := hu.mem_toFinset.mp hp
  have hq' : q ∈ U := hu.mem_toFinset.mp hq
  rcases hp' with ⟨x,rfl⟩ | ⟨b,rfl⟩
  · rcases hq' with ⟨y,rfl⟩ | ⟨c,rfl⟩
    · change GroupActions.orbital (G := G) x.val.val y.val.val
        (r.realSend x.val.val) (r.realSend y.val.val)
      simpa only [realSend_domain] using r.part.pair x y
    · change GroupActions.orbital (G := G) x.val.val c.val
        (r.realSend x.val.val) (r.ownerSend c.val)
      simpa only [realSend_domain,ownerSend_base] using r.mixed_pair S H ontoπ equivπ x c
  · rcases hq' with ⟨y,rfl⟩ | ⟨c,rfl⟩
    · change GroupActions.orbital (G := G) b.val y.val.val
        (r.ownerSend b.val) (r.realSend y.val.val)
      obtain ⟨g,hgx,hgb⟩ := r.mixed_pair S H ontoπ equivπ y b
      exact ⟨g,by simpa only [ownerSend_base] using hgb,
        by simpa only [realSend_domain] using hgx⟩
    · change GroupActions.orbital (G := G) b.val c.val
        (r.ownerSend b.val) (r.ownerSend c.val)
      simpa only [ownerSend_base] using orbitalAut_pair r.owner b c

end OwnerRequest

/-- C05: compatibility is now discharged by one ACTUAL ambient lift.
Only this source lifting branch retains countability. -/
theorem exact_ambient_lift [Countable A]
    (S : AtomicSource.{0,v,w} Unit (fun _ => A))
    (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
    (π : A → O) (ontoπ : Function.Surjective π)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (K : NonemptyExact S () ())
    (hK : GroupActions.kernel π = evaluate S K.words)
    (D : Set A) (B : Set O) [Finite D] [Finite B]
    (hD : ∀ x : D, π x.val ∈ B)
    (r : OwnerRequest (G := G) π D B hD) :
    ∃ g : OrbitalAut G A (id : A → A),
      (∀ x : r.part.domain, g.val x.val.val = (r.part.map x).val) ∧
      (∀ (x : A) (hx : π x ∈ B),
        π (g.val x) = (r.owner.val ⟨π x,hx⟩).val) := by
  classical
  let f := r.jointMap S H ontoπ equivπ
  have realMem (x : r.part.domain) : r.realTag x ∈ f.domain := by
    change r.realTag x ∈ (r.jointMap S H ontoπ equivπ).domain
    simp only [OwnerRequest.jointMap,Set.Finite.mem_toFinset]
    exact Or.inl ⟨x,rfl⟩
  have ownerMem (b : B) : r.ownerTag b ∈ f.domain := by
    change r.ownerTag b ∈ (r.jointMap S H ontoπ equivπ).domain
    simp only [OwnerRequest.jointMap,Set.Finite.mem_toFinset]
    exact Or.inr ⟨b,rfl⟩
  obtain ⟨g,q,hcol,hπ,hext⟩ := one_sort_joint_lifting_of_CCO S H cco
    (fun _ : Unit => O) (fun _ => π) (fun _ => ontoπ) (fun _ => equivπ)
    (fun _ => K) (fun _ => hK) f
  have hgOrb : ∀ x y : A, GroupActions.orbital (G := G) x y (g x) (g y) := by
    intro x y
    exact S.pair_homogeneous_of_homogeneous H x (g x) y (g y) (hcol x y).symm
  let aut : OrbitalAut G A (id : A → A) := ⟨g,(mem_orbitalAut_iff g).mpr hgOrb⟩
  refine ⟨aut,?_,?_⟩
  · intro x
    have hh := hext (r.realTag x) (realMem x)
    change g x.val.val = r.realSend x.val.val at hh
    rw [OwnerRequest.realSend_domain] at hh
    exact hh
  · intro x hx
    have hh := hext (r.ownerTag ⟨π x,hx⟩) (ownerMem ⟨π x,hx⟩)
    have hq : q () (π x) = (r.owner.val ⟨π x,hx⟩).val := by
      change q () (π x) = r.ownerSend (π x) at hh
      rw [OwnerRequest.ownerSend,dif_pos hx] at hh
      exact hh
    exact (hπ () x).symm.trans hq

end CCO.Owners.Provider
