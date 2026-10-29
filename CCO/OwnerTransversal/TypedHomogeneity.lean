import CCO.OwnerTransversal.TypedPalette
import Mathlib.Algebra.Group.Subgroup.Defs

universe v w t
namespace CCO.OwnerTransversal
open ParityHasse.Original RawExact FinitePackets.Normalization
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable (E : ColourEq S ()) {B : Type} [Fintype B] (q : B → Quotient E.val)

def ownerFixer : Subgroup G := by
  letI := originalQuotientAction S H E
  exact {
    carrier := {g | ∀ b, g • q b = q b}
    one_mem' := fun b => one_smul _ _
    mul_mem' := by intro g h hg hh b; rw [mul_smul,hh b,hg b]
    inv_mem' := by
      intro g hg b
      have hh := congrArg (fun p : Quotient E.val => g⁻¹ • p) (hg b)
      simpa only [inv_smul_smul] using hh.symm }

@[instance_reducible] def ownerCarrierAction (b : B) :
    MulAction (ownerFixer S H E q) (OwnerCarrier S E q b) where
  smul g x := ⟨g.val • x.val,by
    letI := originalQuotientAction S H E
    rw [quotient_projection_equivariant S H E,x.property]
    exact g.property b⟩
  one_smul x := Subtype.ext (one_smul _ _)
  mul_smul g h x := Subtype.ext (mul_smul g.val h.val x.val)

variable (hq : Function.Injective q)

include H in
/-- C14: fixing EVERY owner gives literal named-owner homogeneity.
This holds for B empty as well; no nonempty-slot convention is used. -/
theorem typedOwner_homogeneous [Countable M]
    (cco : SemanticCCO.{0,v,0,w} S) (hE : ExactCRT.IsExactEq S (i := ()) E.val) :
    letI : ∀ b, MulAction (ownerFixer S H E q) (OwnerCarrier S E q b) :=
      ownerCarrierAction S H E q
    HomogeneousSource (typedOwnerSource S E q hq) (ownerFixer S H E q) := by
  classical
  letI := originalQuotientAction S H E
  letI : ∀ b, MulAction (ownerFixer S H E q) (OwnerCarrier S E q b) :=
    ownerCarrierAction S H E q
  refine {
    preserves_sort := fun g p => rfl
    preserves_colours := ?_
    extends_finite_diagram := ?_ }
  · rintro g ⟨b,x⟩ ⟨c,y⟩
    apply congrArg (fun col => (⟨b,c,col⟩ : Σ b, Σ c, Option (OwnerAtom S E q b c)))
    apply (typedOwner_colour_iff S E q hq _ _ _ _).mpr
    exact S.colourInvariant_of_homogeneous H g.val x.val y.val
  · intro V _ f h hcol
    have hs (x : V) : (f x).1 = (h x).1 :=
      congrArg (fun col : Σ b, Σ c, Option (OwnerAtom S E q b c) => col.1) (hcol x x)
    have hraw (x y : V) : S.colour (i := ()) (j := ()) (f x).2.val (f y).2.val =
        S.colour (h x).2.val (h y).2.val := by
      have hh := congrArg
        (fun col : Σ b, Σ c, Option (OwnerAtom S E q b c) => col.2.2.map Subtype.val) (hcol x y)
      simpa only [taggedColour,typedOwnerSource,ownerColour_map] using hh
    have hCover (x : V) : ∃ b, q b = Quotient.mk'' (f x).2.val ∧
        q b = Quotient.mk'' (h x).2.val := by
      refine ⟨(f x).1,(f x).2.property.symm,?_⟩
      rw [hs]
      exact (h x).2.property.symm
    obtain ⟨g,hg,hqg⟩ := finite_real_owner_lifting S H cco E hE
      (fun x => (f x).2.val) (fun x => (h x).2.val) q q hraw
      (fun b c => ⟨1,one_smul _ _,one_smul _ _⟩) hCover
    let k : ownerFixer S H E q := ⟨g,hqg⟩
    refine ⟨k,?_⟩
    intro x
    cases hf : f x with | mk b a =>
      cases hh : h x with | mk c d =>
        have hbc := hs x
        rw [hf,hh] at hbc
        change b = c at hbc
        subst c
        apply congrArg (Sigma.mk b)
        apply Subtype.ext
        have hValue := hg x
        rw [hf,hh] at hValue
        exact hValue

include H in
/-- The ordinary actual typed age has AP. This conclusion uses no SAP. -/
theorem typedOwner_ageAP [Countable M]
    (cco : SemanticCCO.{0,v,0,w} S) (hE : ExactCRT.IsExactEq S (i := ()) E.val) :
    AgeAP (typedOwnerSource S E q hq) := by
  letI : ∀ b, MulAction (ownerFixer S H E q) (OwnerCarrier S E q b) :=
    ownerCarrierAction S H E q
  exact ageAP_of_homogeneous _ (typedOwner_homogeneous S H E q hq cco hE)

end CCO.OwnerTransversal
