import CCO.DirectOwnerClosure.Basic
import CCO.FinitePackets.Geometry.ExactCutSource
import CCO.RawExact.QuotientFiniteHomogeneity
import CCO.RawExact.ActualNestedMaps
import CCO.FinitePackets.Normalization.QuotientThin

/-! Separate ancillary homogeneity of the full owner-named union.  The
countability premise belongs only to the one joint-lifting invocation here;
none of the three closure equalities depends on this module. -/
universe v w t z
namespace CCO.DirectOwnerClosure
open ParityHasse.Original RealHull.Geometry FinitePackets.Geometry RawExact
open FinitePackets.Normalization

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

/-- C22: equality of actual owner values preserves the mixed orbital with
EVERY owner, including owners not incident with the real partial domain. -/
theorem mixed_pair_of_owner_eq (E : ColourEq S ()) (x y : M)
    (hxy : owner S E x = owner S E y) (b : Owner S E) :
    letI := originalQuotientAction S H E
    GroupActions.orbital (G := G) x b y b := by
  letI := originalQuotientAction S H E
  apply (actual_nested_orbit_reduction_of_homogeneous S H
    (id : M → M) (Quotient.mk'' : M → Owner S E) Quotient.mk''
    Function.surjective_id Quotient.mk''_surjective
    (fun _ _ => rfl) (quotient_projection_equivariant S H E)
    (quotient_projection_equivariant S H E) (fun _ => rfl)
    (i := ()) x y b b).mpr
  change GroupActions.orbital (G := G) (owner S E x) b (owner S E y) b
  rw [hxy]
  exact GroupActions.orbital_nonempty _ _

/-- An original motion fixing each displayed imaginary owner restricts to
the FULL named language.  No countability or packet invariance is used. -/
def restrict_motion (E : ColourEq S ()) (B : Finset (Owner S E)) (g : G)
    (hg : letI := originalQuotientAction S H E; ∀ b ∈ B, g • b = b) :
    NamedAut S E B := by
  letI := originalQuotientAction S H E
  have ho (k : G) (x : M) : owner S E (k • x) = k • owner S E x := rfl
  have hginv (b : Owner S E) (hb : b ∈ B) : g⁻¹ • b = b :=
    (congrArg (fun z => g⁻¹ • z) (hg b hb).symm).trans (inv_smul_smul g b)
  let e : Equiv.Perm (OwnerUnion S E B) := {
    toFun x := ⟨g • x.val, by rw [ho,hg _ x.property]; exact x.property⟩
    invFun x := ⟨g⁻¹ • x.val, by rw [ho,hginv _ x.property]; exact x.property⟩
    left_inv x := Subtype.ext (inv_smul_smul g x.val)
    right_inv x := Subtype.ext (smul_inv_smul g x.val) }
  refine ⟨e,?_,?_⟩
  · intro b x
    change owner S E (g • x.val) = b ↔ owner S E x.val = b
    rw [ho,hg _ x.property]
  · intro c x y
    change col S (g • x.val) (g • y.val) = c ↔ col S x.val y.val = c
    rw [col_invariant S H]

variable [Countable M]

/-- C23: ONE actual joint lift fixes the ENTIRE finite owner set.  The
mixed-orbit obligation is discharged before the lifting theorem is called. -/
theorem joint_real_owner_fixing (cco : SemanticCCO.{0,v,0,w} S)
    (E : ColourEq S ()) (hE : MinimalInfiniteCut S E)
    {I : Type z} [Finite I] (source target : I → M)
    (hReal : ∀ i j, col S (source i) (source j) = col S (target i) (target j))
    (hOwner : ∀ i, owner S E (source i) = owner S E (target i))
    (B : Finset (Owner S E)) :
    letI := originalQuotientAction S H E
    ∃ g : G, (∀ i, g • source i = target i) ∧ (∀ b ∈ B, g • b = b) := by
  classical
  letI := originalQuotientAction S H E
  let Q : Bool → Type v := fun b => if b then Owner S E else M
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
  let presentation : ∀ b : Bool, NonemptyExact S () () := fun b =>
    if b then coreExact S H E else exactIdentityAtom S ()
  have hPresentation : ∀ b, GroupActions.kernel (π b) = evaluate S (presentation b).words := by
    intro b
    cases b
    · change Eq = evaluate S (exactIdentityAtom S ()).words
      rw [exactIdentityAtom_relation]
      rfl
    · change GroupActions.kernel (Quotient.mk'' : M → Owner S E) =
        evaluate S (coreExact S H E).words
      rw [minimal_cut_exact_represents S H cco hE]
      funext x y
      exact propext Quotient.eq
  let sort : I ⊕ ↥B → Bool := Sum.elim (fun _ => false) (fun _ => true)
  let src : ∀ i, Q (sort i) := fun i => match i with
    | .inl i => source i
    | .inr b => b.val
  let dst : ∀ i, Q (sort i) := fun i => match i with
    | .inl i => target i
    | .inr b => b.val
  have hMixed (i : I) (b : ↥B) : GroupActions.orbital (G := G)
      (source i) b.val (target i) b.val :=
    mixed_pair_of_owner_eq S H E _ _ (hOwner i) b.val
  have hPair : ∀ i j, GroupActions.orbital (G := G)
      (src i) (src j) (dst i) (dst j) := by
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => exact S.pair_homogeneous_of_homogeneous H _ _ _ _ (hReal i j)
      | inr b => exact hMixed i b
    | inr b =>
      cases j with
      | inl j =>
        obtain ⟨g,hg,hb⟩ := hMixed j b
        exact ⟨g,hb,hg⟩
      | inr c => exact GroupActions.orbital_nonempty _ _
  obtain ⟨g,hg⟩ := finite_quotient_tuple_lifting_of_CCO S H
    (semanticCCO_change_universe S cco) Q root π
    (fun b => by cases b; exact Function.surjective_id; exact Quotient.mk''_surjective)
    hπ presentation hPresentation sort src dst hPair
  exact ⟨g,fun i => hg (.inl i),fun b hb => hg (.inr ⟨b,hb⟩)⟩

include H in
/-- C24: the full owner-named union is homogeneous in the separate
countable lifting scope.  No normalization, owner-translation invariance,
closure equality, or nonempty-union premise is required. -/
theorem named_homogeneous (cco : SemanticCCO.{0,v,0,w} S)
    (E : ColourEq S ()) (hE : MinimalInfiniteCut S E) (B : Finset (Owner S E)) :
    (namedStructure S E B).Homogeneous := by
  classical
  intro A f _ hu hb
  by_cases hB : B = ∅
  · refine ⟨1,?_⟩
    intro a
    have hn : B.Nonempty := ⟨owner S E a.val.val,a.val.property⟩
    have hf : (∅ : Finset (Owner S E)).Nonempty := hB ▸ hn
    exact False.elim (Finset.not_nonempty_empty hf)
  · let source : ↥A → M := fun a => a.val.val
    let target : ↥A → M := fun a => (f a).val
    have hReal : ∀ i j, col S (source i) (source j) = col S (target i) (target j) := by
      intro i j
      exact ((hb (col S (source i) (source j)) i j).mpr rfl).symm
    have hOwner : ∀ i, owner S E (source i) = owner S E (target i) := by
      intro i
      exact ((hu (owner S E i.val.val) i).mpr rfl).symm
    obtain ⟨g,hg,hfix⟩ := joint_real_owner_fixing S H cco E hE source target hReal hOwner B
    refine ⟨restrict_motion S H E B g hfix,?_⟩
    intro a
    exact Subtype.ext (hg a)

end CCO.DirectOwnerClosure
