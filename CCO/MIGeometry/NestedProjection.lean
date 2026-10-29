import CCO.MIGeometry.Spectrum
import CCO.RawExact.ActualNestedMaps
import CCO.RawExact.QuotientFiniteHomogeneity

/-! Algebraicity projection between actual nested exact quotient sorts.
The finite lift fixes the whole fine-sort base and moves one coarse owner;
there is no global automorphism lifting assertion. -/
universe v w t
namespace CCO.MIGeometry
open ParityHasse.Original RealClosure.Bounds AclOwners
open RawExact ExactCRT FinitePackets.Normalization
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] (cco : SemanticCCO.{0,v,0,w} S)
variable (C J : ColourEq S ()) (hCJ : C.val ≤ J.val)
variable (BC BJ : NonemptyExact S () ())
variable (hC : evaluate S BC.words = C.val.r) (hJ : evaluate S BJ.words = J.val.r)
include cco BC BJ hC hJ

/-- APJ for the actual map M/C → M/J. Exactness of both original kernels
supplies the finite simultaneous lift in the original source. -/
theorem nested_projection_algebraic
    (A : Finset (Quotient C.val)) (x : Quotient C.val) :
    letI := originalQuotientAction S H C
    letI := originalQuotientAction S H J
    letI := Classical.decEq (Quotient J.val)
    x ∈ Acl G A → Abstract.quotientMap hCJ x ∈
      Acl G (A.image (Abstract.quotientMap hCJ)) := by
  classical
  letI := originalQuotientAction S H C
  letI := originalQuotientAction S H J
  letI : DecidableEq (Quotient J.val) := Classical.decEq _
  let owner := Abstract.quotientMap hCJ
  intro hx
  change (orbitOver G (A.image owner) (owner x)).Finite
  apply (hx.image owner).subset
  rintro q ⟨γ,hγ,hq⟩
  let Q : Bool → Type v | false => Quotient C.val | true => Quotient J.val
  letI : ∀ k, MulAction G (Q k) := fun k => by cases k <;> dsimp [Q] <;> infer_instance
  let π : ∀ k, M → Q k | false => Quotient.mk'' | true => Quotient.mk''
  let E : ∀ _ : Bool, NonemptyExact S () () | false => BC | true => BJ
  have onto : ∀ k, Function.Surjective (π k) := by
    intro k; cases k <;> exact Quotient.mk''_surjective
  have equiv : ∀ k (g : G) c, π k (g • c) = g • π k c := by
    intro k; cases k <;> intro g c <;> rfl
  have ker : ∀ k, GroupActions.kernel (π k) = evaluate S (E k).words := by
    intro k; cases k
    · funext a b
      exact propext (Quotient.eq.trans (Iff.of_eq (congrFun (congrFun hC a) b)).symm)
    · funext a b
      exact propext (Quotient.eq.trans (Iff.of_eq (congrFun (congrFun hJ a) b)).symm)
  have eqowner (g : G) (y : Quotient C.val) : owner (g • y) = g • owner y := by
    induction y using Quotient.inductionOn with | _ a => rfl
  have nested (a : Quotient C.val) (q r : Quotient J.val) :
      GroupActions.orbital (G := G) a q a r ↔
        GroupActions.orbital (G := G) (owner a) q (owner a) r :=
    actual_nested_orbit_reduction_of_homogeneous S H (i := ())
      (Quotient.mk'' : M → Quotient C.val) (Quotient.mk'' : M → Quotient J.val) owner
      Quotient.mk''_surjective Quotient.mk''_surjective
      (quotient_projection_equivariant S H C) (quotient_projection_equivariant S H J)
      eqowner (fun _ => rfl) a a q r
  let I := ↥A ⊕ Unit
  let sort : I → Bool | .inl _ => false | .inr _ => true
  let left : ∀ i, Q (sort i) | .inl a => a.val | .inr _ => owner x
  let right : ∀ i, Q (sort i) | .inl a => a.val | .inr _ => γ • owner x
  have pair : ∀ i j, GroupActions.orbital (G := G) (left i) (left j) (right i) (right j) := by
    intro i j
    cases i with
    | inl a =>
      cases j with
      | inl b => exact GroupActions.orbital_nonempty _ _
      | inr b =>
        apply (nested a.val (owner x) (γ • owner x)).mpr
        exact ⟨γ,hγ _ (Finset.mem_image.mpr ⟨a.val,a.property,rfl⟩),rfl⟩
    | inr b =>
      cases j with
      | inl a =>
        apply (RawExact.QuotientPalette.orbital_swap_iff _ _ _ _).mpr
        apply (nested a.val (owner x) (γ • owner x)).mpr
        exact ⟨γ,hγ _ (Finset.mem_image.mpr ⟨a.val,a.property,rfl⟩),rfl⟩
      | inr c => exact ⟨γ,rfl,rfl⟩
  obtain ⟨g,hg⟩ := finite_quotient_tuple_lifting_of_CCO S H (semanticCCO_change_universe S cco)
    Q (fun _ => ()) π onto equiv E ker sort left right pair
  refine ⟨g • x,⟨g,fun a ha => hg (.inl ⟨a,ha⟩),rfl⟩,?_⟩
  exact (eqowner g x).trans ((hg (.inr ())).trans hq)

end CCO.MIGeometry
