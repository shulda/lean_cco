import CCO.APCharacter.MaskReadout
import CCO.RawExact.Saturation
import CCO.PositiveWords

/-! B048 C13/C14. WHOLE actual represented semantic cylinders, without a
reachability or exact-presentation premise. Bridge identities are full
kernel identities; STRONG profiles are guarded only in their consumers. -/

universe u v w t
namespace CCO.FullPhaseLift.Detours
open APCharacter RigidGroupoid.Geometry
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G)

def cylinder {i j : ι} (K : Kernel S i) (L : Kernel S j) (a : S.Atom i j) : TRel X i j :=
  RawExact.saturate K.rel (S.atomRel a) L.rel

include H in
/-- Every invariant relation containing one actual diversity pair contains
its entire old canonical pair type. Exactness is not required. -/
theorem atom_subset_invariant {i j : ι} {R : TRel X i j}
    (hR : TRel.Invariant (G := G) R) (x : X i) (y : X j) (a : S.Atom i j)
    (hc : S.colour x y = some a) (hr : R x y) :
    ∀ p q, S.atomRel a p q → R p q := by
  intro p q hpq
  obtain ⟨g,hgx,hgy⟩ := S.pair_homogeneous_of_homogeneous H x p y q (hc.trans hpq.symm)
  simpa only [hgx,hgy] using hR g x y hr

theorem atom_subset_cylinder {i j : ι} (K : Kernel S i) (L : Kernel S j)
    (a : S.Atom i j) : ∀ x y, S.atomRel a x y → cylinder S K L a x y := by
  intro x y h
  exact ⟨y,⟨x,K.setoid.refl x,h⟩,L.setoid.refl y⟩

include H in
/-- A single rigid meeting fills the ENTIRE semantic cylinder. -/
theorem cylinder_eq_arrow_of_meet {i j : ι} {K : Kernel S i} {L : Kernel S j}
    (a : S.Atom i j) (R : Arrow S K L) {x : X i} {y : X j}
    (hc : cylinder S K L a x y) (hr : R.rel x y) : cylinder S K L a = R.rel := by
  obtain ⟨q,⟨p,hxp,hpq⟩,hqy⟩ := hc
  have hpy : R.rel p y := by
    rw [← R.left]
    exact ⟨x,K.setoid.symm hxp,hr⟩
  have hpq' : R.rel p q := by
    rw [← R.right]
    exact ⟨y,hpy,L.setoid.symm hqy⟩
  have he := R.rectangular H hpq'
  change S.colour p q = some a at hpq
  rw [hpq] at he
  exact he.symm

include H in
/-- This is a whole-cylinder dichotomy, not a classification of selected
representatives. Its nonrigid branch excludes EVERY rigid meeting. -/
theorem cylinder_rigid_or_nonrigid {i j : ι} (K : Kernel S i) (L : Kernel S j)
    (a : S.Atom i j) :
    (∃ R : Arrow S K L, cylinder S K L a = R.rel) ∨
      ∀ (R : Arrow S K L) x y, cylinder S K L a x y → ¬R.rel x y := by
  classical
  by_cases h : ∃ (R : Arrow S K L) (x : X i) (y : X j), cylinder S K L a x y ∧ R.rel x y
  · obtain ⟨R,x,y,hc,hr⟩ := h
    exact Or.inl ⟨R,cylinder_eq_arrow_of_meet S H a R hc hr⟩
  · exact Or.inr (fun R x y hc hr => h ⟨R,x,y,hc,hr⟩)

include H in
/-- The quotient logical identity cylinder is the WHOLE original kernel,
including all its real representatives. It is not original logical Id. -/
theorem cylinder_eq_kernel {i : ι} (K : Kernel S i) (a : S.Atom i i)
    {x y : X i} (hc : S.colour x y = some a) (hK : K.rel x y) :
    cylinder S K K a = K.rel := by
  exact cylinder_eq_arrow_of_meet S H a (Arrow.id K) (atom_subset_cylinder S K K a x y hc) hK

include H in
/-- All actual represented outputs of a three-edge bridge detour stay
inside the whole cylinder. This does not assume SAP, exactness or
reachability of the cylinder, or distinctness of quotient classes. -/
theorem three_edge_bound {r i j : ι} {A : Kernel S r} {K : Kernel S i} {L : Kernel S j}
    (Ba : Arrow S A K) (Bb : Arrow S A L)
    (a : S.Atom i j) (ra : S.Atom i r) (d : S.Atom r r) (rb : S.Atom r j)
    (x : X i) (y : X j) (u v : X r)
    (hBa : Ba.rel u x) (hBb : Bb.rel v y)
    (hc : S.colour x y = some a) (hra : S.colour x u = some ra)
    (hd : S.colour u v = some d) (hrb : S.colour v y = some rb) :
    ∀ p q, PositiveWord.represented S (.cons ra (.cons d (.single rb))) p q →
      cylinder S K L a p q := by
  have hleft := atom_subset_invariant S H (Ba.inv.exact.invariant S H) x u ra hra hBa
  have hright := atom_subset_invariant S H (Bb.exact.invariant S H) v y rb hrb hBb
  let M := TRel.comp (TRel.comp Ba.rel (S.atomRel a)) Bb.inv.rel
  have haInv : TRel.Invariant (G := G) (S.atomRel a) := by
    intro g p q hpq
    exact (S.colourInvariant_of_homogeneous H g p q).trans hpq
  have hMInv : TRel.Invariant (G := G) M :=
    TRel.invariant_comp _ _ (TRel.invariant_comp _ _ (Ba.exact.invariant S H) haInv)
      (Bb.inv.exact.invariant S H)
  have hmid := atom_subset_invariant S H hMInv u v d hd ⟨y,⟨x,hBa,hc⟩,hBb⟩
  rintro p q ⟨s,hps,t,hst,htq⟩
  obtain ⟨y',⟨x',hsx',hc'⟩,hty'⟩ := hmid s t hst
  have hK : K.rel p x' := by
    rw [← Ba.target]
    exact ⟨s,hleft p s hps,hsx'⟩
  have hL : L.rel y' q := by
    rw [← Bb.target]
    exact ⟨t,hty',hright t q htq⟩
  exact ⟨y',⟨x',hK,hc'⟩,hL⟩

include H in
/-- The semantic cylinder is precisely the full pullback of ONE actual
original-group quotient pair orbital. No quotient homogeneity or section
is presumed. -/
theorem cylinder_orbital_pullback {i j : ι} (K : Kernel S i) (L : Kernel S j)
    (a : S.Atom i j) (x : X i) (y : X j) (hc : S.colour x y = some a) :
    letI := K.action H
    letI := L.action H
    GroupActions.pullback K.project L.project
      (GroupActions.orbital (G := G) (K.project x) (L.project y)) = cylinder S K L a := by
  letI := K.action H
  letI := L.action H
  have hK : GroupActions.kernel K.project = K.rel := by
    funext p q
    exact propext Quotient.eq
  have hL : GroupActions.kernel L.project = L.rel := by
    funext p q
    exact propext Quotient.eq
  rw [RawExact.equivariant_orbit_pullback K.project L.project
    (K.project_equivariant H) (L.project_equivariant H) x y,hK,hL,
    RawExact.actual_pair_orbital_of_homogeneous S H x y,hc]
  rfl

variable {S H} {C : ExactCalculus S} {r : ι} {A : Kernel S r}

/-- An allowed old atom makes EVERY optional pair colour in its entire
semantic cylinder allowed. Nonrigid cylinders are phase-flexible; a rigid
cylinder retains the unique phase already forced at the requested atom. -/
theorem cylinder_allows (P : SourcePhase S H C A) (b c : Reached S A)
    (a : S.Atom b.val c.val) (ε η : Bit) (ha : P.allows (some a) ε η) :
    ∀ x y, cylinder S (Reached.kernel H C b) (Reached.kernel H C c) a x y →
      P.allows (S.colour x y) ε η := by
  intro x y hxy
  apply (P.allows_actual_iff x y ε η).mpr
  refine ⟨ha.1,ha.2.1,?_⟩
  intro hi hj R hR
  have he := cylinder_eq_arrow_of_meet S H a R hxy hR
  obtain ⟨p,q,hpq⟩ := S.realized a
  have hRpq : R.rel p q := by
    rw [← he]
    exact atom_subset_cylinder S _ _ a p q hpq
  exact ha.2.2 p q hpq b.property c.property R hRpq

end
end CCO.FullPhaseLift.Detours
