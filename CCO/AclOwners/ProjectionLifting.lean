import CCO.AclOwners.QuotientSource
import CCO.RawExact.ActualNestedMaps
import CCO.RawExact.QuotientFiniteHomogeneity
import CCO.RealClosure.Bounds.Algebraicity

/-! Exact algebraicity projection uses a genuine finite real/owner lift.
The target action is the full canonical quotient automorphism group. -/
universe v w t
namespace CCO.AclOwners
open ParityHasse.Original FinitePackets.Normalization RealClosure.Bounds
open RawExact Owners.Product
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable (K : ColourEq S ()) (B : NonemptyExact S () ())
variable (hB : evaluate S B.words = K.val.r)

include B hB in
/-- Every finite compatible fixed-real/moving-owner request has one
original motion. The quotient automorphism need not lift globally. -/
theorem exact_owner_point_lift [Countable M]
    (cco : SemanticCCO.{0,v,0,w} S) (A : Finset M) (x : M) :
    letI := originalQuotientAction S H K
    ∀ (γ : OrbitalAut G (Quotient K.val) (id : Quotient K.val → Quotient K.val)),
      (∀ a ∈ A, γ.val (Quotient.mk'' a) = Quotient.mk'' a) →
      ∃ g : G, (∀ a ∈ A, g • a = a) ∧
        (Quotient.mk'' (g • x) : Quotient K.val) = γ.val (Quotient.mk'' x) := by
  classical
  letI := originalQuotientAction S H K
  intro γ hγ
  let Q : Bool → Type v | false => M | true => Quotient K.val
  letI : ∀ k, MulAction G (Q k) := fun k => by cases k <;> dsimp [Q] <;> infer_instance
  let π : ∀ k, M → Q k | false => id | true => Quotient.mk''
  let E : ∀ _ : Bool, NonemptyExact S () ()
    | false => exactIdentityAtom S () | true => B
  have onto : ∀ k, Function.Surjective (π k) := by
    intro k; cases k
    · exact Function.surjective_id
    · exact Quotient.mk''_surjective
  have equiv : ∀ k (g : G) c, π k (g • c) = g • π k c := by
    intro k; cases k <;> intro g c <;> rfl
  have ker : ∀ k, GroupActions.kernel (π k) = evaluate S (E k).words := by
    intro k; cases k
    · exact (exactIdentityAtom_relation S ()).symm
    · funext a b
      exact propext (Quotient.eq.trans (Iff.of_eq (congrFun (congrFun hB a) b)).symm)
  let I := ↥A ⊕ Unit
  let sort : I → Bool | .inl _ => false | .inr _ => true
  let left : ∀ i, Q (sort i) | .inl a => a.val | .inr _ => Quotient.mk'' x
  let right : ∀ i, Q (sort i) | .inl a => a.val | .inr _ => γ.val (Quotient.mk'' x)
  have nested (a : M) (q r : Quotient K.val) :
      GroupActions.orbital (G := G) a q a r ↔
        GroupActions.orbital (G := G) (Quotient.mk'' a : Quotient K.val) q
          (Quotient.mk'' a) r :=
    actual_nested_orbit_reduction_of_homogeneous S H (i := ()) id
      (Quotient.mk'' : M → Quotient K.val) Quotient.mk''
      Function.surjective_id Quotient.mk''_surjective
      (fun _ _ => rfl) (quotient_projection_equivariant S H K)
      (quotient_projection_equivariant S H K) (fun _ => rfl) a a q r
  have pair : ∀ i j, GroupActions.orbital (G := G) (left i) (left j) (right i) (right j) := by
    intro i j
    cases i with
    | inl a =>
      cases j with
      | inl b => exact GroupActions.orbital_nonempty _ _
      | inr b =>
        apply (nested a.val (Quotient.mk'' x) (γ.val (Quotient.mk'' x))).mpr
        simpa only [id_eq,hγ a.val a.property] using
          orbitalAut_pair γ (Quotient.mk'' a.val) (Quotient.mk'' x)
    | inr b =>
      cases j with
      | inl a =>
        apply (RawExact.QuotientPalette.orbital_swap_iff _ _ _ _).mpr
        apply (nested a.val (Quotient.mk'' x) (γ.val (Quotient.mk'' x))).mpr
        simpa only [id_eq,hγ a.val a.property] using
          orbitalAut_pair γ (Quotient.mk'' a.val) (Quotient.mk'' x)
      | inr c => exact orbitalAut_pair γ (Quotient.mk'' x) (Quotient.mk'' x)
  obtain ⟨g,hg⟩ := finite_quotient_tuple_lifting_of_CCO S H (semanticCCO_change_universe S cco)
    Q (fun _ => ()) π onto equiv E ker sort left right pair
  exact ⟨g,fun a ha => hg (.inl ⟨a,ha⟩),hg (.inr ())⟩

include B hB in
/-- APJ for the FULL target group. The finite pointwise-base orbit in
the quotient is contained in the image of the original real stabilizer orbit. -/
theorem exact_projection_algebraic_full [Countable M]
    (cco : SemanticCCO.{0,v,0,w} S) (A : Finset M) (x : M) (hx : x ∈ Acl G A) :
    letI := originalQuotientAction S H K
    letI := Classical.decEq (Quotient K.val)
    (Quotient.mk'' x : Quotient K.val) ∈
      Acl (OrbitalAut G (Quotient K.val) (id : Quotient K.val → Quotient K.val))
        (A.image Quotient.mk'') := by
  classical
  letI := originalQuotientAction S H K
  letI : DecidableEq (Quotient K.val) := Classical.decEq _
  change (orbitOver _ (A.image Quotient.mk'') (Quotient.mk'' x : Quotient K.val)).Finite
  apply (hx.image (Quotient.mk'' : M → Quotient K.val)).subset
  rintro q ⟨γ,hγ,hq⟩
  obtain ⟨g,hg,hgx⟩ := exact_owner_point_lift S H K B hB cco A x γ
    (fun a ha => hγ _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩))
  exact ⟨g • x,⟨g,hg,rfl⟩,hgx.trans hq⟩

include B hB in
/-- The same APJ in the existing actual-old-G acl interface. -/
theorem exact_projection_algebraic [Countable M]
    (cco : SemanticCCO.{0,v,0,w} S) (A : Finset M) (x : M) (hx : x ∈ Acl G A) :
    letI := originalQuotientAction S H K
    letI := Classical.decEq (Quotient K.val)
    (Quotient.mk'' x : Quotient K.val) ∈ Acl G (A.image Quotient.mk'') := by
  classical
  letI := originalQuotientAction S H K
  letI : DecidableEq (Quotient K.val) := Classical.decEq _
  change (orbitOver G (A.image Quotient.mk'') (Quotient.mk'' x : Quotient K.val)).Finite
  apply (hx.image (Quotient.mk'' : M → Quotient K.val)).subset
  rintro q ⟨γ,hγ,hq⟩
  obtain ⟨g,hg,hgx⟩ := exact_owner_point_lift S H K B hB cco A x (canonicalAut γ)
    (fun a ha => hγ _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩))
  exact ⟨g • x,⟨g,hg,rfl⟩,hgx.trans hq⟩
end CCO.AclOwners
