import CCO.AclOwners.FiniteExact
import CCO.FinitePackets.Normalization.QuotientThin
import CCO.RawExact.ActualNestedMaps
import CCO.RawExact.FiniteRealignment

/-! Genuine finite original-real/exact-owner requests. All named owner
classes are fixed individually; the lift is one original group element.
No full quotient automorphism surjectivity is asserted. -/
universe v w t
namespace CCO.AclOwners
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization RawExact
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

def CutColour (E : ColourEq S ()) (c : FullColour S) : Prop :=
  ∀ x y, E x y → colourSquare S c x y → x = y

def correspondence (E : ColourEq S ()) (x y : M) : Prop :=
  CutColour S E (col S x y)

theorem cutColour_none (E : ColourEq S ()) : CutColour S E none := by
  rintro x y _ ⟨z,hxz,hzy⟩
  exact ((col_none S x z).mp hxz).trans ((col_none S z y).mp hzy)

theorem correspondence_refl (E : ColourEq S ()) (x : M) : correspondence S E x x := by
  change CutColour S E (col S x x)
  rw [(col_none S x x).mpr rfl]
  exact cutColour_none S E

theorem correspondence_symm (E : ColourEq S ()) {x y : M}
    (hxy : correspondence S E x y) : correspondence S E y x := by
  unfold correspondence at *
  rwa [col_symm S y x]

/-- C07: functionality is within one specified owner class, including
the equality orbital. -/
theorem cutColour_functional (E : ColourEq S ()) (c : FullColour S)
    (hc : CutColour S E c) {z x y : M}
    (hx : col S z x = c) (hy : col S z y = c) (hE : E x y) : x = y :=
  hc x y hE ⟨z,(col_symm S x z).trans hx,hy⟩

/-- C08 in a stronger finite-domain form: an arbitrary finite real
partial isomorphism which fixes its E-projections extends while fixing
every requested finite collection of E-classes. -/
theorem finite_fixed_owner_lift [Countable M] [DecidableEq M]
    (cco : SemanticCCO.{0,v,0,w} S) (E : ColourEq S ())
    (hE : ExactCRT.IsExactEq S (i := ()) E.val) (A : Finset M) (f : M → M)
    (hcol : ∀ x ∈ A, ∀ y ∈ A, col S (f x) (f y) = col S x y)
    (hfix : ∀ x ∈ A, E x (f x)) (B : Finset (Quotient E.val)) :
    letI := originalQuotientAction S H E
    ∃ g : G, (∀ x ∈ A, g • x = f x) ∧ ∀ q ∈ B, g • q = q := by
  classical
  letI := originalQuotientAction S H E
  let Q : Unit → Type v := fun _ => Quotient E.val
  let π : M → Quotient E.val := Quotient.mk''
  have hπ (g : G) (x : M) : π (g • x) = g • π x := rfl
  have reduce := actual_nested_orbit_reduction_of_homogeneous S H (i := ())
    (id : M → M) π π Function.surjective_id Quotient.mk''_surjective
    (fun _ _ => rfl) hπ hπ (fun _ => rfl)
  let F := JointFamily (fun _ : Unit => M) Q
  let real : M → Sigma F := fun x => ⟨.inl (),x⟩
  let owner : Quotient E.val → Sigma F := fun q => ⟨.inr (),q⟩
  let domain := A.image real ∪ B.image owner
  let send : ∀ p : Sigma F, F p.1 := fun p => match p with
    | ⟨.inl _,x⟩ => f x
    | ⟨.inr _,q⟩ => q
  have real_mem (x : M) : real x ∈ domain ↔ x ∈ A := by
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hr | ho
      · obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hr
        have hax : a = x := eq_of_heq (Sigma.mk.inj he).2
        exact hax ▸ ha
      · obtain ⟨a,_,he⟩ := Finset.mem_image.mp ho
        have hh : Sum.inr () = (Sum.inl () : Unit ⊕ Unit) := congrArg Sigma.fst he
        cases hh
    · intro hx
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
  have hpairs : ∀ p q : Sigma F, p ∈ domain → q ∈ domain →
      GroupActions.orbital (G := G) p.2 q.2 (send p) (send q) := by
    rintro ⟨k,x⟩ ⟨l,y⟩ hx hy
    cases k with
    | inl k =>
      cases k
      have hxA := (real_mem x).mp hx
      cases l with
      | inl l =>
        cases l
        have hyA := (real_mem y).mp hy
        exact S.pair_homogeneous_of_homogeneous H x (f x) y (f y)
          (hcol x hxA y hyA).symm
      | inr l =>
        cases l
        apply (reduce x (f x) y y).mpr
        have he : π x = π (f x) := Quotient.sound (hfix x hxA)
        rw [← he]
        exact GroupActions.orbital_nonempty _ _
    | inr k =>
      cases k
      cases l with
      | inl l =>
        cases l
        have hyA := (real_mem y).mp hy
        obtain ⟨g,hgy,hgx⟩ := (reduce y (f y) x x).mpr (by
          have he : π y = π (f y) := Quotient.sound (hfix y hyA)
          rw [← he]
          exact GroupActions.orbital_nonempty _ _)
        exact ⟨g,hgx,hgy⟩
      | inr l => cases l; exact GroupActions.orbital_nonempty _ _
  let request : FiniteJointPartialIso G F := ⟨domain,send,hpairs⟩
  obtain ⟨D,hD⟩ := hE
  have hker : GroupActions.kernel π = evaluate S D.words := by
    rw [hD]
    funext x y
    exact propext Quotient.eq
  obtain ⟨g,hg⟩ := finite_joint_group_lifting_of_CCO S H
    (semanticCCO_change_universe S cco) Q (fun _ => ()) (fun _ => π)
    (fun _ => Quotient.mk''_surjective) (fun _ => hπ) (fun _ => D)
    (fun _ => hker) request
  refine ⟨g,fun x hx => hg (real x) ((real_mem x).mpr hx),?_⟩
  intro q hq
  exact hg (owner q) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩))

end CCO.AclOwners
