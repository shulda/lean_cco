import CCO.ExactCRT.ExactLattice
import CCO.RawExact.QuotientFiniteHomogeneity
import CCO.RawExact.ActualNestedMaps
import CCO.FinitePackets.Normalization.QuotientThin
import CCO.RawExact.DiagramReindex

/-! Finite real maps with their ENTIRE recorded exact-owner component.
Mixed pairs are checked by the actual nested-orbital theorem before the
accepted joint exact-sort lifting theorem is applied. -/
universe v w t z r
namespace CCO.OwnerTransversal
open ParityHasse.Original RawExact FinitePackets.Normalization

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M]

/-- Actual accepted joint-exact support. The index J includes unused owners, and I may be empty. Thus
the conclusion extends the whole specified owner component at once. -/
theorem actual_joint_real_owner_lifting
    (cco : SemanticCCO.{0,v,0,w} S) (E : ColourEq S ())
    (hE : ExactCRT.IsExactEq S (i := ()) E.val)
    {I : Type z} [Finite I] {J : Type r} [Finite J]
    (source target : I → M) (q q' : J → Quotient E.val)
    (hReal : ∀ i j, S.colour (i := ()) (j := ()) (source i) (source j) =
      S.colour (target i) (target j))
    (hOwners : letI := originalQuotientAction S H E
      ∀ j k, GroupActions.orbital (G := G) (q j) (q k) (q' j) (q' k))
    (hCover : ∀ i, ∃ j, q j = Quotient.mk'' (source i) ∧
      q' j = Quotient.mk'' (target i)) :
    letI := originalQuotientAction S H E
    ∃ g : G, (∀ i, g • source i = target i) ∧ (∀ j, g • q j = q' j) := by
  classical
  letI := originalQuotientAction S H E
  let Q : Bool → Type v := fun b => if b then Quotient E.val else M
  letI : ∀ b, MulAction G (Q b) := fun b => by
    cases b <;> simp only [Q, Bool.false_eq_true, ↓reduceIte] <;> infer_instance
  let root : Bool → Unit := fun _ => ()
  let π : ∀ b, M → Q b := fun b => by
    cases b
    · exact id
    · exact Quotient.mk''
  have hπ : ∀ b (g : G) x, π b (g • x) = g • π b x := by
    intro b g x
    cases b <;> rfl
  let B : ∀ b : Bool, NonemptyExact S () () := fun b =>
    if b then ExactCRT.exactPresentation S hE else exactIdentityAtom S ()
  have hB : ∀ b, GroupActions.kernel (π b) = evaluate S (B b).words := by
    intro b
    cases b
    · change Eq = evaluate S (exactIdentityAtom S ()).words
      rw [exactIdentityAtom_relation]
      rfl
    · change GroupActions.kernel (Quotient.mk'' : M → Quotient E.val) =
        evaluate S (ExactCRT.exactPresentation S hE).words
      rw [ExactCRT.exactPresentation_represents]
      funext x y
      exact propext Quotient.eq
  let sort : I ⊕ J → Bool := Sum.elim (fun _ => false) (fun _ => true)
  let src : ∀ i, Q (sort i) := fun i => match i with
    | .inl i => source i
    | .inr j => q j
  let dst : ∀ i, Q (sort i) := fun i => match i with
    | .inl i => target i
    | .inr j => q' j
  have hMixed (i : I) (j : J) : GroupActions.orbital (G := G)
      (source i) (q j) (target i) (q' j) := by
    obtain ⟨k,hk,hk'⟩ := hCover i
    apply (actual_nested_orbit_reduction_of_homogeneous S H
      (id : M → M) (Quotient.mk'' : M → Quotient E.val) Quotient.mk''
      Function.surjective_id Quotient.mk''_surjective
      (fun _ _ => rfl) (quotient_projection_equivariant S H E)
      (quotient_projection_equivariant S H E) (fun _ => rfl)
      (i := ()) (source i) (target i) (q j) (q' j)).mpr
    rw [← hk,← hk']
    exact hOwners k j
  have hPair : ∀ i j, GroupActions.orbital (G := G)
      (src i) (src j) (dst i) (dst j) := by
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => exact S.pair_homogeneous_of_homogeneous H _ _ _ _ (hReal i j)
      | inr j => exact hMixed i j
    | inr i =>
      cases j with
      | inl j =>
        obtain ⟨g,hg,hg'⟩ := hMixed j i
        exact ⟨g,hg',hg⟩
      | inr j => exact hOwners i j
  obtain ⟨g,hg⟩ := finite_quotient_tuple_lifting_of_CCO S H
    (semanticCCO_change_universe S cco) Q root π
    (fun b => by cases b; exact Function.surjective_id; exact Quotient.mk''_surjective)
    hπ B hB sort src dst hPair
  exact ⟨g,fun i => hg (.inl i),fun j => hg (.inr j)⟩

end CCO.OwnerTransversal
