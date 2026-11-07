import CCO.OldIdempotentForest.ReconstructionRequests
import CCO.GuardedOldSeams.IdempotentBoundary
import CCO.GuardedOldSeams.SeamBoundary
import CCO.UnaryTermsReturn.CommonBlockMalformedObstruction

/-! Source16 scope boundaries. The direct envelope and the exact
original requests remain separate from any finer cut or unrelated
anchor. Stopped pruning retains the original ordered payload and counts
both endpoints of every kept letter. The accepted common-block diagnostic
concerns malformed inverse-transition inputs, outside unary admissibility.

The finite-SEMIGROUP forest theorem is received and instantiated by the
imported source adapter. Bounded control enumeration is not its proof.
No HN/HKN receiving theorem or higher-arity support gate is supplied here.
-/

universe u v w r z
namespace CCO.OldIdempotentForest
open CCO.GuardedOldSeams CCO.GuardedTwoRoot
open CCO.UnaryTermsReturn CCO.TransitionClosure CCO.ParityHasse.Original
open CCO.HiddenSAPReadings CCO.TypedOrbitFrames CCO.UnaryFreshFrames
open CCO.UnarySupport CCO.UnarySupport.Structure
noncomputable section
/-! The following is a faithful TWO-TRANSITION REDUCT packaging of the
accepted B052 malformed cycle, with exactly the same Fin n indices and
actual commonBlockForward/commonBlockBackward quotient maps. It is not
a new original atomic model or a full hidden-language provider. -/

def malformedTransitionSignature : Signature where
  Sorts := Bool
  Func := Bool
  Rel := Empty
  input := id
  output := Bool.not
  arity R := nomatch R
  argument R := nomatch R
  finiteSort := inferInstance
  finiteFunc := inferInstance
  finiteRel := inferInstance

def malformedTransitionSort {A B : Type*} : A ⊕ B → Bool
  | .inl _ => false
  | .inr _ => true

def malformedTransitionFunc (n : ℕ) :
    Bool → (Fin n ⊕ Fin n) → Set (Fin n ⊕ Fin n)
  | false, .inl i => {.inr i}
  | true, .inr i => {.inl (malformedCycleStep n i)}
  | _, _ => ∅

def malformedTransitionCycle (n : ℕ) :
    Structure malformedTransitionSignature (Fin n ⊕ Fin n) where
  sort := malformedTransitionSort
  func := malformedTransitionFunc n
  functional F x y z hy hz := by
    cases F <;> cases x <;> simp_all [malformedTransitionFunc]
  func_sorted F x y hy := by
    cases F <;> cases x <;>
      simp_all [malformedTransitionFunc, malformedTransitionSort,
        malformedTransitionSignature]
  rel R := nomatch R
  rel_sorted R := nomatch R

def commonBlockTransitionFunc : Bool →
    (Quotient (commonBlockOldSetoid false) ⊕ Quotient (commonBlockOldSetoid true)) →
    Set (Quotient (commonBlockOldSetoid false) ⊕ Quotient (commonBlockOldSetoid true))
  | false, .inl q => {.inr (commonBlockForward q)}
  | true, .inr q => {.inl (commonBlockBackward q)}
  | _, _ => ∅

def commonBlockTransitionTarget : Structure malformedTransitionSignature
    (Quotient (commonBlockOldSetoid false) ⊕ Quotient (commonBlockOldSetoid true)) where
  sort := malformedTransitionSort
  func := commonBlockTransitionFunc
  functional F x y z hy hz := by
    cases F <;> cases x <;> simp_all [commonBlockTransitionFunc]
  func_sorted F x y hy := by
    cases F <;> cases x <;>
      simp_all [commonBlockTransitionFunc, malformedTransitionSort,
        malformedTransitionSignature]
  rel R := nomatch R
  rel_sorted R := nomatch R

theorem malformed_transition_total (n : ℕ) :
    (malformedTransitionCycle n).Total := by
  intro F x hx
  cases F <;> cases x <;>
    simp_all [malformedTransitionCycle, malformedTransitionSort,
      malformedTransitionSignature, malformedTransitionFunc]

/-- The actual accepted closed-pair condition is exactly the two
displayed transition closure conditions of this reduct. -/
theorem malformed_transition_closed_pair {n : ℕ}
    (A : Set (Fin n ⊕ Fin n))
    (hA : (malformedTransitionCycle n).IsClosed A) :
    MalformedCycleClosed {i | Sum.inl i ∈ A} {i | Sum.inr i ∈ A} := by
  constructor
  · intro i hi
    exact hA false (.inl i) hi (by rfl)
  · intro i hi
    exact hA true (.inr i) hi (by rfl)

theorem malformed_transition_closed_nonempty_full {n : ℕ}
    (hn : 2 ≤ n) (A : Set (Fin n ⊕ Fin n))
    (hA : (malformedTransitionCycle n).IsClosed A) (hne : A.Nonempty) :
    A = Set.univ := by
  have hp : ({i | Sum.inl i ∈ A} : Set (Fin n)).Nonempty ∨
      ({i | Sum.inr i ∈ A} : Set (Fin n)).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    rcases x with i | i
    · exact Or.inl ⟨i,hx⟩
    · exact Or.inr ⟨i,hx⟩
  obtain ⟨hleft,hright⟩ := malformed_cycle_closed_nonempty_is_full hn _ _
    (malformed_transition_closed_pair A hA) hp
  apply Set.eq_univ_of_forall
  intro x
  rcases x with i | i
  · exact (Set.eq_univ_iff_forall.mp hleft) i
  · exact (Set.eq_univ_iff_forall.mp hright) i

theorem malformed_transition_singleton_full {n : ℕ} (hn : 2 ≤ n)
    (x : Fin n ⊕ Fin n) :
    (malformedTransitionCycle n).closureAt x = Set.univ :=
  malformed_transition_closed_nonempty_full hn _
    ((malformedTransitionCycle n).isClosed_closure {x})
    ⟨x,(malformedTransitionCycle n).mem_closureAt x⟩

/-- Preservation of the ACTUAL named inverse pair already rules out
injectivity; no reflection or binary-relation premise is necessary. -/
theorem malformed_transition_no_injective_hom {n : ℕ} (hn : 2 ≤ n)
    (e : Hom (malformedTransitionCycle n) commonBlockTransitionTarget) :
    ¬ Function.Injective e.point := by
  intro hinj
  have hpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  let i : Fin n := ⟨0,hpos⟩
  have hf := e.map_func false (.inl i) (.inr i) (by rfl)
  have hg := e.map_func true (.inr i) (.inl (malformedCycleStep n i)) (by rfl)
  have hs := e.sort_eq (.inl i)
  cases hq : e.point (.inl i) with
  | inl q =>
    have hforward : e.point (.inr i) = Sum.inr (commonBlockForward q) := by
      simpa only [commonBlockTransitionTarget, commonBlockTransitionFunc,
        hq, Set.mem_singleton_iff] using hf
    have hreturn : e.point (.inl (malformedCycleStep n i)) = Sum.inl q := by
      simpa only [commonBlockTransitionTarget, commonBlockTransitionFunc,
        hforward, commonBlockMixedNamedReturnA, Set.mem_singleton_iff] using hg
    exact malformed_cycle_step_ne_self hn i
      (Sum.inl.inj (hinj (hreturn.trans hq.symm)))
  | inr q =>
    change malformedTransitionSort (e.point (.inl i)) = false at hs
    rw [hq] at hs
    cases hs

/-- Minimal negative proof: two immediate OLD function steps already
lie in the chosen singleton closure. Full-orbit closure is unnecessary. -/
theorem malformed_transition_not_unary_admissible {n : ℕ} (hn : 2 ≤ n) :
    ¬ UnaryAdmissible (malformedTransitionCycle n) commonBlockTransitionTarget := by
  intro hadm
  have hpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  let i : Fin n := ⟨0,hpos⟩
  let root : Fin n ⊕ Fin n := .inl i
  obtain ⟨e⟩ := hadm root
  have hroot : root ∈ (malformedTransitionCycle n).closureAt root :=
    (malformedTransitionCycle n).mem_closureAt root
  have hnextB : Sum.inr i ∈ (malformedTransitionCycle n).closureAt root :=
    (malformedTransitionCycle n).isClosed_closure {root} false root hroot (by rfl)
  have hnextA : Sum.inl (malformedCycleStep n i) ∈
      (malformedTransitionCycle n).closureAt root :=
    (malformedTransitionCycle n).isClosed_closure {root} true (.inr i) hnextB (by rfl)
  let a : (malformedTransitionCycle n).closureAt root := ⟨root,hroot⟩
  let b : (malformedTransitionCycle n).closureAt root := ⟨.inr i,hnextB⟩
  let a' : (malformedTransitionCycle n).closureAt root :=
    ⟨.inl (malformedCycleStep n i),hnextA⟩
  have hf := e.map_func false a b (by rfl)
  have hg := e.map_func true b a' (by rfl)
  have hs := e.sort_eq a
  cases hq : e.point a with
  | inl q =>
    have hforward : e.point b = Sum.inr (commonBlockForward q) := by
      simpa only [commonBlockTransitionTarget, commonBlockTransitionFunc,
        hq, Set.mem_singleton_iff] using hf
    have hreturn : e.point a' = Sum.inl q := by
      simpa only [commonBlockTransitionTarget, commonBlockTransitionFunc,
        hforward, commonBlockMixedNamedReturnA, Set.mem_singleton_iff] using hg
    have hsame : a' = a := e.injective (hreturn.trans hq.symm)
    exact malformed_cycle_step_ne_self hn i
      (Sum.inl.inj (congrArg Subtype.val hsame))
  | inr q =>
    change malformedTransitionSort (e.point a) = false at hs
    rw [hq] at hs
    cases hs


theorem malformed_transition_irreducible {n : ℕ} (hn : 2 ≤ n) :
    (malformedTransitionCycle n).Irreducible := by
  let root : Fin n ⊕ Fin n := .inl ⟨0,by omega⟩
  exact irreducible_of_generated _ root (malformed_transition_singleton_full hn root)

theorem malformed_transition_no_HE {n : ℕ} (hn : 2 ≤ n)
    (f : Hom (malformedTransitionCycle n) commonBlockTransitionTarget) :
    ¬ f.HomEmbedding := by
  intro hf
  apply malformed_transition_not_unary_admissible hn
  intro x
  exact ⟨f.restrictionEmbedding ((malformedTransitionCycle n).isClosed_closure {x})
    (hf _ ((malformedTransitionCycle n).isClosed_closure {x})
      ((malformedTransitionCycle n).singleton_irreducible x))⟩

/-- C67 on the SAME accepted original common-block SAP+CCO source.
The exact displayed malformed cycles form an unbounded total-unary,
one-generated irreducible reduct family. They are not unary-admissible,
have no homomorphism-embedding into the actual inverse-transition
target reduct, and have no nonempty bounded closed obstruction. -/
theorem forest_commonBlock_unbounded_malformed (N : ℕ) :
    AgeSAP commonBlockOriginalAtomicSource ∧
    SemanticCCO.{0,0,0,0} commonBlockOriginalAtomicSource ∧
    ∃ n : ℕ, 2 ≤ n ∧ N < Fintype.card (Fin n ⊕ Fin n) ∧
      (malformedTransitionCycle n).Total ∧
      (malformedTransitionCycle n).Irreducible ∧
      ¬ UnaryAdmissible (malformedTransitionCycle n) commonBlockTransitionTarget ∧
      (∀ f : Hom (malformedTransitionCycle n) commonBlockTransitionTarget, ¬ f.HomEmbedding) ∧
      (∀ A, (malformedTransitionCycle n).IsClosed A → A.Nonempty → A = Set.univ) ∧
      (∀ A, (malformedTransitionCycle n).IsClosed A → A.ncard ≤ N → A = ∅) := by
  refine ⟨commonBlockOriginalAgeSAP,commonBlockOriginalSemanticCCO,?_⟩
  let n := N+2
  have hn : 2 ≤ n := by omega
  have hlarge : N < Fintype.card (Fin n ⊕ Fin n) := by
    rw [malformed_cycle_carrier_card]
    omega
  refine ⟨n,hn,hlarge,malformed_transition_total n,malformed_transition_irreducible hn,
    malformed_transition_not_unary_admissible hn,malformed_transition_no_HE hn,
    fun A hA hne => malformed_transition_closed_nonempty_full hn A hA hne,?_⟩
  intro A hA hsmall
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hne
  rw [malformed_transition_closed_nonempty_full hn A hA hne] at hsmall
  simp only [Set.ncard_univ,Nat.card_eq_fintype_card] at hsmall
  exact Nat.not_le_of_lt hlarge hsmall

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

/-- C60: a strictly finer equivalence genuinely excludes a pair in the
gap envelope. This is quantified by the strict inclusion, not an assertion
that such a strict cut exists in every original source. -/
theorem forest_envelope_not_finer {i : ι} (e : S.Menu i i)
    (idem : S.product e e = e) (J : ColourEq S i)
    (strict : J < envelope S e idem) :
    ∃ x y, envelope S e idem x y ∧ S.menuRel e x y ∧ ¬ J x y := by
  classical
  have hn : ¬ envelope S e idem ≤ J := not_le_of_gt strict
  by_contra h
  apply hn
  intro x y hE
  by_contra hJ
  have hne : x ≠ y := by
    intro he
    exact hJ (he ▸ J.val.refl x)
  exact h ⟨x,y,hE,(envelope_distinct_iff S e idem hne).mp hE,hJ⟩

/-- C61: true identity belongs to the RAW envelope and never belongs to
the diversity profile, even when that profile is a strong idempotent. -/
theorem forest_envelope_restores_identity {i : ι} (e : S.Menu i i)
    (idem : S.product e e = e) (x : X i) :
    envelope S e idem x x ∧ ¬ S.menuRel e x x :=
  ⟨Or.inl rfl,diversity_irreflexive S e x⟩

variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)

include H sap in
/-- C64: an actual atom admitted by the EXACT complementary word need
not satisfy a different one-letter anchor. The endpoint base is the actual
complete induced original two-point base. No simple-cycle claim is made. -/
theorem forest_fixed_anchor_not_forced {i j : ι} (word : PositiveWord S i j)
    (a b : S.Atom i j) (hne : a ≠ b) (ha : a ∈ PositiveWord.profile S word) :
    ∃ (x : X i) (y : X j) (base : FiniteInduced (X := X)),
      (⟨i,x⟩ : Sigma X) ∈ base.vertices ∧ (⟨j,y⟩ : Sigma X) ∈ base.vertices ∧
      S.atomRel a x y ∧ PositiveWord.represented S word x y ∧
        ¬ PositiveWord.represented S (.single b) x y := by
  obtain ⟨x,y,hxy⟩ := S.realized a
  let base : FiniteInduced (X := X) :=
    ⟨{(⟨i,x⟩ : Sigma X),⟨j,y⟩},(Set.finite_singleton _).insert _⟩
  refine ⟨x,y,base,by simp [base],by simp [base],hxy,?_,?_⟩
  · exact CCO.StrongExact.profile_realizes_prescribed_pair_of_SAP S H sap word a ha x y hxy
  · intro hb
    exact hne (Option.some.inj (hxy.symm.trans hb))

/-- C63: two kept leaves separated by a whole deleted interval really
have four retained OLD root positions. The false leaf-count-plus-one
estimate fails even on this elementary stopped-pruning shape. -/
def separatedLeafPruning : PruningTree Unit :=
  .branch (.leaf ()) [(),(),()] (.leaf ())

theorem separated_leaf_root_count :
    (separatedLeafPruning.retainedRoots 0).card = 2 * separatedLeafPruning.leaves ∧
      separatedLeafPruning.leaves + 1 < (separatedLeafPruning.retainedRoots 0).card := by
  decide

/-- C72: the one-letter path needs no deletion and retains both literal
endpoints at height zero. No empty positive word is introduced. -/
theorem forest_singleton_boundary {A : Type u} (a : A) :
    Prunes (.leaf a) (.leaf a) ∧
      (PruningTree.leaf a).height = 0 ∧
      (PruningTree.leaf a).pieces = [.kept a] ∧
      (PruningTree.leaf a).retainedRoots 0 = {0,1} :=
  ⟨.leaf a,rfl,rfl,rfl⟩

variable (nr2 : Selectors.OriginalNR2 S)
variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
variable {n : ℕ} (C : SupportedMacroChain S H sap nr2 F n)

/-- C62/C65: STOP gives disjoint located intervals and the literal
original payload, regardless of equal semigroup values or word profiles. -/
theorem forest_source_exact_disjoint_payload
    (R : SourcePrunedForest S H sap nr2 F C) {B : Type*} (payload : Fin n → List B) :
    (locate 0 R.pruning.pieces).Pairwise
      (fun p q => ∀ i, p.start ≤ i → i < p.stop → ¬ (q.start ≤ i ∧ i < q.stop)) ∧
      R.pruning.pieces.flatMap (fun p => p.word.flatMap payload) =
        (List.finRange n).flatMap payload := by
  refine ⟨locate_disjoint _ _,?_⟩
  exact (R.prunes.exact_original_payload payload).trans
    (congrArg (List.flatMap payload) R.forest.original_yield)

end
end CCO.OldIdempotentForest
