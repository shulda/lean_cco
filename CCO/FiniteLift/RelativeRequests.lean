import CCO.FiniteLift.ThreeSort
import CCO.FiniteLift.WitnessBasics

/-! C22–C23: every compatible source request, including every empty
real request with an arbitrary ENTIRE owner action, extends in the same
full preimage. Onto/kernel transitivity of the owner map is not used. -/

universe v w t
namespace CCO.FiniteLift
open Owners.Product OwnerCover

section Pure
variable {G A O : Type*} [Group G] [MulAction G A] [MulAction G O]

structure RelativeWitness {D : Set A} {B : Set O}
    (Q : OrbitalQuotient (G := G) (Subtype.val : D → A) (Subtype.val : B → O))
    (cl : Set A → Set A) (safe : A → A → Prop) (A0 : Set A) : Prop where
  finite : D.Finite
  closure : cl A0 ⊆ D
  extensions : PrescribedEPPAFor Q {x | x.val ∈ A0}
  roots : ∀ (Z : Set D), Unsafe (fun x y : D => safe x.val y.val) Z →
    ∀ z ∈ Z, ∃ α : OrbitalAut G A (Subtype.val : D → A),
      (∀ x ∈ Z, (α.val x).val ∈ cl A0) ∧ (α.val z).val ∈ A0

end Pure

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A] [Countable A]
variable (HS : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (K H : ExactKernel S G)

/-- The actual square commutes at EVERY real point. -/
theorem owner_square (Dbar : Set K.Q) (Bbar : Set (J S HS cco K H).Q)
    (imageD : rK S HS cco K H '' Dbar = Bbar)
    (x : fullPreimage K.proj Dbar) :
    (quotientOwner S HS cco K H Dbar Bbar imageD).projection
        (fullProjection K.proj Dbar x) =
      (fullOwnerQuotient S HS cco K H Bbar).projection
        ((realOwner S HS cco K H Dbar Bbar imageD).projection x) := rfl

/-- C22: sparse source requests project to compatible quotient requests
with the ACTUAL entire coarse component of the GIVEN owner action. -/
theorem projected_owner_request (Dbar : Set K.Q) (Bbar : Set (J S HS cco K H).Q)
    (imageD : rK S HS cco K H '' Dbar = Bbar)
    (p : OrbitalPartial (G := G) (Subtype.val : fullPreimage K.proj Dbar → A))
    (γ : OrbitalAut G H.Q (Subtype.val : ((rH S HS cco K H) ⁻¹' Bbar) → H.Q))
    (comp : ∀ x : p.domain,
      (realOwner S HS cco K H Dbar Bbar imageD).projection (p.map x) =
        γ.val ((realOwner S HS cco K H Dbar Bbar imageD).projection x.val)) :
    ∀ q : ((fullQuotient K.proj K.onto K.proj_smul Dbar).projectedPartial p).domain,
      (quotientOwner S HS cco K H Dbar Bbar imageD).projection
          (((fullQuotient K.proj K.onto K.proj_smul Dbar).projectedPartial p).map q) =
        (ownerAction S HS cco K H Bbar γ).val
          ((quotientOwner S HS cco K H Dbar Bbar imageD).projection q.val) := by
  intro q
  let Q := fullQuotient K.proj K.onto K.proj_smul Dbar
  let R := realOwner S HS cco K H Dbar Bbar imageD
  let P := quotientOwner S HS cco K H Dbar Bbar imageD
  let C := fullOwnerQuotient S HS cco K H Bbar
  let x := Q.domainLift p q
  change P.projection (Q.projection (p.map x)) =
    (C.action γ).val (P.projection q.val)
  calc
    P.projection (Q.projection (p.map x)) = C.projection (R.projection (p.map x)) := rfl
    _ = C.projection (γ.val (R.projection x.val)) := congrArg C.projection (comp x)
    _ = (C.action γ).val (C.projection (R.projection x.val)) :=
      (C.action_projection γ (R.projection x.val)).symm
    _ = (C.action γ).val (P.projection (Q.projection x.val)) := rfl
    _ = (C.action γ).val (P.projection q.val) :=
      congrArg (fun b => (C.action γ).val (P.projection b)) (Q.projection_domainLift p q)

/-- C23: no onto/kernel premise is needed because gamma is ALREADY
prescribed on the entire complete finite owner set. -/
theorem relative_extensions (finiteK : K.FiniteClasses)
    (Dbar : Set K.Q) (Bbar : Set (J S HS cco K H).Q)
    (finiteDbar : Dbar.Finite) (finiteBbar : Bbar.Finite)
    (imageD : rK S HS cco K H '' Dbar = Bbar) (A0 : Set A)
    (ep : PrescribedEPPAFor (quotientOwner S HS cco K H Dbar Bbar imageD)
      {q | q.val ∈ K.proj '' A0}) :
    PrescribedEPPAFor (realOwner S HS cco K H Dbar Bbar imageD) {x | x.val ∈ A0} := by
  intro p hDom hRan γ hcomp
  let Q := fullQuotient K.proj K.onto K.proj_smul Dbar
  let pbar := Q.projectedPartial p
  have hbarDom : pbar.domain ⊆ {q | q.val ∈ K.proj '' A0} := by
    rintro q ⟨x,hx,rfl⟩
    exact ⟨x.val,hDom hx,rfl⟩
  have hbarRan : ∀ q : pbar.domain, pbar.map q ∈ {q | q.val ∈ K.proj '' A0} := by
    intro q
    exact ⟨(p.map (Q.domainLift p q)).val,hRan _,rfl⟩
  obtain ⟨β,hβ,hβowner⟩ := ep pbar hbarDom hbarRan
    (ownerAction S HS cco K H Bbar γ)
    (projected_owner_request S HS cco K H Dbar Bbar imageD p γ hcomp)
  have compK : ∀ x : p.domain,
      K.proj (p.map x).val = (β.val (fullProjection K.proj Dbar x.val)).val := by
    intro x
    have hh := hβ ⟨Q.projection x.val,⟨x.val,x.property,rfl⟩⟩
    rw [Q.partial_projection p x] at hh
    exact (congrArg Subtype.val hh).symm
  obtain ⟨α,hp,_,hαH⟩ := three_sort_lift S HS cco K H finiteK Dbar Bbar
    finiteDbar finiteBbar imageD p β γ hβowner.symm compK
    (fun x => congrArg Subtype.val (hcomp x))
  exact ⟨α,hp,hαH⟩

end CCO.FiniteLift
