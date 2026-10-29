import CCO.ExactCRT.SourceLattice
import CCO.Owners.Product.SourceGeometry

/-! Actual indexed exact quotients: set realization and fine pair readout
are proved separately. Repeated kernels and logical equality are retained. -/
universe u v w t z
namespace CCO.Owners.Joint
open RawExact ExactCRT RawExact.CanonicalQuotients

section General
variable {G A I : Type*} [Group G] [MulAction G A]
variable (E : I → Setoid A) [∀ i, Invariant G (E i)]

instance familyMeetInvariant : Invariant G (Abstract.familyMeet E) where
  invariant g x y h i := Invariant.invariant g x y (h i)

theorem quotient_family_coordinates_injective :
    Function.Injective (Abstract.coordinates E) := Abstract.coordinates_injective E

theorem quotient_compare_eq_iff {E F J : Setoid A}
    (hE : E ≤ J) (hF : F ≤ J) (eq : E ⊔ F = J)
    (q : Quotient E) (r : Quotient F) :
    Abstract.quotientMap hE q = Abstract.quotientMap hF r ↔
      Abstract.quotientMap (show E ≤ E ⊔ F from le_sup_left) q =
        Abstract.quotientMap (show F ≤ E ⊔ F from le_sup_right) r := by
  induction q using Quotient.inductionOn with
  | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
      change Quotient.mk J x = Quotient.mk J y ↔
        Quotient.mk (E ⊔ F) x = Quotient.mk (E ⊔ F) y
      rw [Quotient.eq, Quotient.eq, eq]

end General

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
variable {i : ι} {I : Type z} [Finite I]
variable (C T : I → ExactEq S H cco i)
variable (hCT : ∀ k, C k ≤ T k)

local instance exactInvariantC (k : I) : Invariant G (C k).val :=
  Product.exactInvariant S H cco (C k)
local instance exactInvariantT (k : I) : Invariant G (T k).val :=
  Product.exactInvariant S H cco (T k)

/-- The literal owner test; it is not replaced by onto marginal images. -/
def ActualCompatible (q : ∀ k, Quotient (C k).val) : Prop :=
  ∀ k l,
    Abstract.quotientMap (show (C k).val ≤ (T k).val ⊔ (T l).val from
      (hCT k).trans le_sup_left) (q k) =
    Abstract.quotientMap (show (C l).val ≤ (T k).val ⊔ (T l).val from
      (hCT l).trans le_sup_right) (q l)

/-- JOG changes exactly the CRT comparison tests. The diagonal-index
case is automatic and does not need the gate. -/
theorem actualCompatible_iff
    (gate : ∀ k l, k ≠ l → (C k).val ⊔ (C l).val = (T k).val ⊔ (T l).val)
    (q : ∀ k, Quotient (C k).val) :
    ActualCompatible S H cco C T hCT q ↔
      Abstract.Compatible (fun k => (C k).val) q := by
  classical
  constructor
  · intro h k l
    by_cases he : k = l
    · subst l; rfl
    · exact (quotient_compare_eq_iff ((hCT k).trans le_sup_left)
        ((hCT l).trans le_sup_right) (gate k l he) (q k) (q l)).mp (h k l)
  · intro h k l
    by_cases he : k = l
    · subst l; rfl
    · exact (quotient_compare_eq_iff ((hCT k).trans le_sup_left)
        ((hCT l).trans le_sup_right) (gate k l he) (q k) (q l)).mpr (h k l)

/-- C06: every full compatible coordinate tuple is an original point.
The proof uses actual finite CRT and no colour reconstruction. -/
theorem actual_tuple_realization
    (gate : ∀ k l, k ≠ l → (C k).val ⊔ (C l).val = (T k).val ⊔ (T l).val)
    (q : ∀ k, Quotient (C k).val)
    (hq : ActualCompatible S H cco C T hCT q) :
    ∃ x : X i, ∀ k, Quotient.mk (C k).val x = q k :=
  exactCRT_real_representative S H cco i C q
    ((actualCompatible_iff S H cco C T hCT gate q).mp hq)

/-- C06's uniqueness is the original meet-equals-identity hypothesis. -/
theorem original_coordinates_injective
    (meet_id : ∀ x y : X i, (∀ k, (C k).val x y) → x = y) :
    Function.Injective (fun x : X i => fun k => Quotient.mk (C k).val x) := by
  intro x y h
  exact meet_id x y (fun k => Quotient.exact (congrFun h k))

/-- C09: the complete coordinate orbital tuple determines the ORIGINAL
fine pair orbital, independently of JOG and tuple realization. -/
theorem original_fine_readout
    (meet_id : ∀ x y : X i, (∀ k, (C k).val x y) → x = y)
    (a b x y : X i) :
    (∀ k, GroupActions.orbital (G := G)
      (Quotient.mk (C k).val a) (Quotient.mk (C k).val b)
      (Quotient.mk (C k).val x) (Quotient.mk (C k).val y)) ↔
      GroupActions.orbital (G := G) a b x y := by
  let E : I → NonemptyExact S i i := fun k => exactPresentation S (C k).property
  have hE : ∀ k, evaluate S (E k).words = (C k).val.r :=
    fun k => exactPresentation_represents S (C k).property
  have hπ : ∀ k, GroupActions.kernel
      (Quotient.mk'' : X i → Quotient (C k).val) = evaluate S (E k).words := by
    intro k
    rw [hE k]
    funext x y
    exact propext Quotient.eq
  have hκ : GroupActions.kernel (id : X i → X i) =
      RawExact.familyMeet (fun k => evaluate S (E k).words) := by
    funext x y
    apply propext
    constructor
    · intro he k
      change x = y at he
      rw [hE k, he]
    · intro h
      exact meet_id x y (fun k => by simpa only [hE] using h k)
  exact actual_fine_pair_orbit_of_CCO S H cco E
    (fun k => Quotient (C k).val) (fun _ => Quotient.mk'') id
    (fun _ _ _ => rfl) (fun _ _ => rfl) hπ hκ a b x y

end CCO.Owners.Joint
