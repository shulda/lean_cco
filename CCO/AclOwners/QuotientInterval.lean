import CCO.FinitePackets.Normalization.QuotientThin
import CCO.RealClosure.Bounds.Packet
import CCO.Owners.Product.Orbitals
import Mathlib.Algebra.Group.Action.End

/-! The FULL canonical quotient invariant interval.  Old-group pair
orbitals and full language automorphisms give the same invariant relations;
no surjectivity onto the full quotient automorphism group is used. -/
universe v w t
namespace CCO.AclOwners
open ParityHasse.Original FinitePackets.Normalization RealHull.Geometry
open Owners.Product

section FullCanonical
variable {G Q : Type*} [Group G] [MulAction G Q]

/-- Every old-group motion is an automorphism of the complete orbital language. -/
noncomputable def canonicalAut (g : G) : OrbitalAut G Q (id : Q → Q) :=
  ⟨MulAction.toPerm g, (mem_orbitalAut_iff _).mpr (fun x y => ⟨g,rfl,rfl⟩)⟩

/-- The full group has exactly the named old-group pair orbitals. -/
theorem fullCanonical_pair_iff (a b x y : Q) :
    (∃ f : OrbitalAut G Q (id : Q → Q), f.val a = x ∧ f.val b = y) ↔
      GroupActions.orbital (G := G) a b x y := by
  constructor
  · rintro ⟨f,rfl,rfl⟩
    exact orbitalAut_pair f a b
  · rintro ⟨g,hga,hgb⟩
    exact ⟨canonicalAut g,hga,hgb⟩

/-- This includes arbitrary nonexact invariant equivalences. -/
theorem fullCanonical_invariant_iff (E : Setoid Q) :
    (∀ (f : OrbitalAut G Q (id : Q → Q)) x y,
      E x y → E (f.val x) (f.val y)) ↔
    (∀ (g : G) x y, E x y → E (g • x) (g • y)) := by
  constructor
  · intro h g x y hxy
    exact h (canonicalAut g) x y hxy
  · intro h f x y hxy
    obtain ⟨g,hgx,hgy⟩ := orbitalAut_pair f x y
    change g • x = f.val x at hgx
    change g • y = f.val y at hgy
    rw [← hgx,← hgy]
    exact h g x y hxy
end FullCanonical

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable (K : ColourEq S ())

/-- Literal pullback of an invariant quotient equivalence. -/
def quotientPullback (E : ColourEq (actualQuotientSource S H K) ()) : ColourEq S () :=
  ⟨Setoid.comap (Quotient.mk'' : M → Quotient K.val) E.val, by
    intro x y x' y' hc
    obtain ⟨g,hgx,hgy⟩ := S.pair_homogeneous_of_homogeneous H x x' y y' hc
    letI := originalQuotientAction S H K
    apply E.property
    apply (actualQuotientSource_colour_orbital S H K _ _ _ _).mpr
    exact ⟨g,congrArg Quotient.mk'' hgx,congrArg Quotient.mk'' hgy⟩⟩

@[simp] theorem quotientPullback_apply
    (E : ColourEq (actualQuotientSource S H K) ()) (x y : M) :
    quotientPullback S H K E x y ↔ E (Quotient.mk'' x) (Quotient.mk'' y) := Iff.rfl

theorem le_quotientPullback (E : ColourEq (actualQuotientSource S H K) ()) :
    K ≤ quotientPullback S H K E := by
  intro x y hxy
  change E (Quotient.mk'' x) (Quotient.mk'' y)
  have he : (Quotient.mk'' x : Quotient K.val) = Quotient.mk'' y := Quotient.sound hxy
  rw [he]

/-- The induced equivalence uses the actual quotient, with the entire
source equivalence rather than a selected invariant sublattice. -/
def quotientColourEq (F : ColourEq S ()) (hKF : K ≤ F) :
    ColourEq (actualQuotientSource S H K) () := by
  letI := originalQuotientAction S H K
  refine ⟨quotientPacket S K F hKF,?_⟩
  intro q r q' r' hc
  obtain ⟨g,hgq,hgr⟩ := (actualQuotientSource_colour_orbital S H K q r q' r').mp hc
  have inv (g : G) (q r : Quotient K.val) :
      quotientPacket S K F hKF q r → quotientPacket S K F hKF (g • q) (g • r) := by
    induction q using Quotient.inductionOn with | _ x =>
      induction r using Quotient.inductionOn with | _ y =>
        intro hxy
        apply (quotientPacket_projection S H K F hKF _ _).mpr
        exact colourInvariant_groupInvariant S H F.property g x y
          ((quotientPacket_projection S H K F hKF x y).mp hxy)
  rw [← hgq,← hgr]
  exact ⟨inv g q r,fun h => by simpa only [inv_smul_smul] using inv g⁻¹ _ _ h⟩

@[simp] theorem quotientColourEq_projection (F : ColourEq S ()) (hKF : K ≤ F) (x y : M) :
    quotientColourEq S H K F hKF (Quotient.mk'' x) (Quotient.mk'' y) ↔ F x y :=
  quotientPacket_projection S H K F hKF x y

/-- The FULL original invariant interval, including arbitrary nonexact
owners.  The target names every old-group orbital. -/
def quotientColourInterval : Set.Ici K ≃o ColourEq (actualQuotientSource S H K) () where
  toFun E := quotientColourEq S H K E.val E.property
  invFun E := ⟨quotientPullback S H K E,le_quotientPullback S H K E⟩
  left_inv E := by
    apply Subtype.ext
    apply ColourEq.ext
    intro x y
    exact quotientColourEq_projection S H K E.val E.property x y
  right_inv E := by
    apply ColourEq.ext
    intro q r
    induction q using Quotient.inductionOn with | _ x =>
      induction r using Quotient.inductionOn with | _ y =>
        exact quotientColourEq_projection S H K (quotientPullback S H K E)
          (le_quotientPullback S H K E) x y
  map_rel_iff' := by
    intro E F
    constructor
    · intro h x y hxy
      exact (quotientColourEq_projection S H K F.val F.property x y).mp
        (h ((quotientColourEq_projection S H K E.val E.property x y).mpr hxy))
    · intro h q r hqr
      induction q using Quotient.inductionOn with | _ x =>
        induction r using Quotient.inductionOn with | _ y =>
          exact (quotientColourEq_projection S H K F.val F.property x y).mpr
            (h ((quotientColourEq_projection S H K E.val E.property x y).mp hqr))

/-- An actual quotient class IS the relative class set of original points. -/
noncomputable def quotientClassEquiv (F : ColourEq S ()) (hKF : K ≤ F) (x : M) :
    RelativeClass K.val F.val x ≃
      ClassPoint (actualQuotientSource S H K) () (quotientColourEq S H K F hKF)
        (Quotient.mk'' x) := by
  let f : RelativeClass K.val F.val x →
      ClassPoint (actualQuotientSource S H K) () (quotientColourEq S H K F hKF)
        (Quotient.mk'' x) :=
    Quotient.lift (fun y => ⟨Quotient.mk'' y.val,
      (quotientColourEq_projection S H K F hKF x y.val).mpr y.property⟩)
      (fun y z h => Subtype.ext (Quotient.sound h))
  apply Equiv.ofBijective f
  constructor
  · intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro y z h
    have hh : (Quotient.mk'' y.val : Quotient K.val) = Quotient.mk'' z.val := congrArg Subtype.val h
    apply Quotient.sound
    change K y.val z.val
    exact Quotient.exact hh
  · rintro ⟨q,hq⟩
    revert hq
    refine Quotient.inductionOn q ?_
    intro y hy
    exact ⟨Quotient.mk _ ⟨y,(quotientColourEq_projection S H K F hKF x y).mp hy⟩,rfl⟩

theorem quotient_finiteClasses_iff (F : ColourEq S ()) (hKF : K ≤ F) :
    RealClosure.Bounds.FiniteClasses (actualQuotientSource S H K)
      (quotientColourEq S H K F hKF) ↔ FinitePackets.Geometry.FiniteIndex S K F := by
  constructor
  · intro h x
    letI := h (Quotient.mk'' x)
    exact Finite.of_equiv _ (quotientClassEquiv S H K F hKF x).symm
  · intro h q
    induction q using Quotient.inductionOn with | _ x =>
      letI := h x
      exact Finite.of_equiv _ (quotientClassEquiv S H K F hKF x)

/-- Original relative indices are literal quotient class counts. -/
theorem quotient_class_card (F : ColourEq S ()) (hKF : K ≤ F) (x : M) :
    Nat.card (ClassPoint (actualQuotientSource S H K) ()
      (quotientColourEq S H K F hKF) (Quotient.mk'' x)) = relativeIndex K.val F.val x :=
  (Nat.card_congr (quotientClassEquiv S H K F hKF x)).symm

end CCO.AclOwners
