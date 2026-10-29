import CCO.AclOwners.QuotientInterval

/-! Source-free full invariant quotient correspondence.  No finite language,
homogeneity, CCO, countability or automorphism lifting is required here. -/
namespace CCO.AclOwners
open RawExact.CanonicalQuotients ParityHasse.Original Owners.Product
variable {G A Q : Type*} [Group G] [MulAction G A] [MulAction G Q]

abbrev ActionInvariantEq (G : Type*) [Group G] (A : Type*) [MulAction G A] :=
  {E : Setoid A // ∀ (g : G) x y, E x y → E (g • x) (g • y)}

/-- Old-group and FULL canonical-language invariant equivalences are
literally the same relations, ordered by the same inclusion. -/
def fullCanonicalInvariantEquiv : ActionInvariantEq G Q ≃o
    ActionInvariantEq (OrbitalAut G Q (id : Q → Q)) Q where
  toFun E := ⟨E.val,(fullCanonical_invariant_iff E.val).mpr E.property⟩
  invFun E := ⟨E.val,(fullCanonical_invariant_iff E.val).mp E.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Literal quotient transport restricted to ALL old-group invariants. -/
def actionQuotientInterval (K : ActionInvariantEq G A) :
    letI : Invariant G K.val := ⟨K.property⟩
    Set.Ici K ≃o ActionInvariantEq G (Quotient K.val) := by
  letI : Invariant G K.val := ⟨K.property⟩
  refine {
    toFun := fun E => ⟨Setoid.correspondence K.val ⟨E.val.val,E.property⟩,?_⟩
    invFun := fun E => ⟨⟨Setoid.comap (Quotient.mk'' : A → Quotient K.val) E.val,?_⟩,?_⟩
    left_inv := ?_
    right_inv := ?_
    map_rel_iff' := ?_ }
  · intro g q r
    induction q using Quotient.inductionOn with | _ x =>
      induction r using Quotient.inductionOn with | _ y =>
        exact E.val.property g x y
  · intro g x y h
    exact E.property g (Quotient.mk'' x) (Quotient.mk'' y) h
  · intro x y h
    change E.val (Quotient.mk'' x) (Quotient.mk'' y)
    have he : (Quotient.mk'' x : Quotient K.val) = Quotient.mk'' y := Quotient.sound h
    rw [he]
  · intro E
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro E
    apply Subtype.ext
    apply Setoid.ext
    intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro x y
    rfl
  · intro E F
    constructor
    · intro h x y hxy
      exact h (x := Quotient.mk'' x) (y := Quotient.mk'' y) hxy
    · intro h q r
      refine Quotient.inductionOn₂ q r ?_
      exact fun x y hxy => h hxy

/-- C35 in the generic setting of A11, with the genuine FULL target group. -/
def fullInvariantQuotientInterval (K : ActionInvariantEq G A) :
    letI : Invariant G K.val := ⟨K.property⟩
    Set.Ici K ≃o ActionInvariantEq
      (OrbitalAut G (Quotient K.val) (id : Quotient K.val → Quotient K.val))
      (Quotient K.val) := by
  letI : Invariant G K.val := ⟨K.property⟩
  exact (actionQuotientInterval K).trans fullCanonicalInvariantEquiv

section Counts
variable {M : Type*} (K E F : Setoid M) (hKE : K ≤ E) (hKF : K ≤ F)

/-- The relative-class bijection is a map of actual classes, independent
of every group and source hypothesis. -/
noncomputable def quotientRelativeClassEquiv (x : M) :
    RelativeClass E F x ≃
      RelativeClass ((Setoid.correspondence K) ⟨E,hKE⟩)
        ((Setoid.correspondence K) ⟨F,hKF⟩) (Quotient.mk'' x) := by
  let f : RelativeClass E F x →
      RelativeClass ((Setoid.correspondence K) ⟨E,hKE⟩)
        ((Setoid.correspondence K) ⟨F,hKF⟩) (Quotient.mk'' x) :=
    Quotient.map (fun y => ⟨Quotient.mk'' y.val,y.property⟩) (fun y z h => h)
  apply Equiv.ofBijective f
  constructor
  · intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro y z h
    apply Quotient.sound
    have he := Quotient.exact h
    change E y.val z.val at he
    exact he
  · intro q
    refine Quotient.inductionOn q ?_
    rintro ⟨p,hp⟩
    revert hp
    refine Quotient.inductionOn p ?_
    intro y hy
    exact ⟨Quotient.mk _ ⟨y,hy⟩,rfl⟩

/-- Therefore relative finite-index assertions agree under quotient transport. -/
theorem quotient_relative_finite_iff (x : M) :
    Finite (RelativeClass E F x) ↔
      Finite (RelativeClass ((Setoid.correspondence K) ⟨E,hKE⟩)
        ((Setoid.correspondence K) ⟨F,hKF⟩) (Quotient.mk'' x)) := by
  constructor
  · intro h
    letI := h
    exact Finite.of_equiv _ (quotientRelativeClassEquiv K E F hKE hKF x)
  · intro h
    letI := h
    exact Finite.of_equiv _ (quotientRelativeClassEquiv K E F hKE hKF x).symm

theorem quotient_relative_index_eq (x : M) :
    relativeIndex E F x =
      relativeIndex ((Setoid.correspondence K) ⟨E,hKE⟩)
        ((Setoid.correspondence K) ⟨F,hKF⟩) (Quotient.mk'' x) :=
  Nat.card_congr (quotientRelativeClassEquiv K E F hKE hKF x)
end Counts
end CCO.AclOwners
