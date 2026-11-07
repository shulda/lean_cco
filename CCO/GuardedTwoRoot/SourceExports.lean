import CCO.GuardedTwoRoot.BoundedSourcePair
import CCO.GuardedTwoRoot.SourceAnchorSupport
import CCO.GuardedTwoRoot.G1CCO
import CCO.GuardedTwoRoot.G1HiddenSAP
import CCO.GuardedTwoRoot.G1HiddenOrbitals
import CCO.GuardedTwoRoot.G1WordClassification
import CCO.GuardedTwoRoot.G1FiniteIndex
import CCO.GuardedTwoRoot.MergedPrivateBranches

/-! Source14 exports on the precise bounded LOCAL old support.
The complete-pattern premise is only BoundedPairTest for the actual
irreducible endpoint support, with its size derived from real unary
admissibility. No global JoinedAdmissible or hidden completion is used.
Uniform size includes the ENTIRE old functional anchor closure. The
binary reflection export retains EVERY surviving atom and exact source
closed-image isomorphism; higher-support tuples are outside this language.
The pure private-graph export is provided separately after actual merging
of repeated direct branches, with no semantic source premise. -/

universe u v w r z
namespace CCO.GuardedTwoRoot
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
open CCO.StrongExact
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
local notation "Lang" => originalCompletedLanguage S H sap nr2
local notation "Hidden" => originalCompletedStructure S H sap nr2
local notation "Target" => originalPartialTarget S H sap nr2

/-- Source14 first result, including the actual old support bound.
This alias preserves the complete bounded-local-test quantifiers. -/
theorem typed_one_source_support_per_guarded_pair
    {P : Type z} [Finite P]
    (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (hUnary : UnaryAdmissible F (Target)) (b c : P) (hbc : b ≠ c)
    (hirr : (F.closureStructure {b,c}).Irreducible)
    (hTest : BoundedPairTest S H sap nr2 F b c) :
    let b' : F.closure {b,c} := ⟨b,F.subset_closure _ (by simp)⟩
    let c' : F.closure {b,c} := ⟨c,F.subset_closure _ (by simp)⟩
    Nat.card (F.closure {b,c}) ≤ 2 * originalSourceUniformNormalCodeBudget S H ∧
    ∃ e : CCO.UnarySupport.Structure.Embedding (F.closureStructure {b,c}) (Target),
      (pairMenu S H sap nr2 (factorRecords S H sap nr2
        ⟨e.point b',e.sort_eq b'⟩ ⟨e.point c',e.sort_eq c'⟩)).Nonempty := by
  exact bounded_pair_source_factor S H sap nr2 F hUnary b c hbc hirr hTest

/-- A source-only language bound for theta vertices and the ENTIRE
functional closure of every direct/branch-forced old anchor. -/
def sourcePairBudget : ℕ :=
  canonicalThetaBudget S H sap + (Nat.card (TypedPrefix.State S) - 1) +
    2 * originalSourceUniformNormalCodeBudget S H

/-- The actual source root package supplies its own anchor bound;
no unproved anchor-count premise is passed to the uniform result. -/
theorem actual_theta_and_all_anchors_bound
    {C D : (Lang).Sorts} {q : (Hidden).Carrier C} {s : (Hidden).Carrier D}
    (T : SourceThetaRootPackage S H sap nr2 q s) :
    Nat.card (thetaVertices S T.words) + ((Hidden).closure T.signatureAnchors).ncard ≤
      sourcePairBudget S H sap :=
  Nat.add_le_add T.size_bound T.full_anchor_closure_bound

/-- Tie this SAME actual source theta and its surviving fine pair to
one full old-factor image. Every functional signature anchor has a
literal preimage in that OLD two-generated source, not a new generator. -/
theorem one_factor_signature_old_preimages
    {P : Type z}
    (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (e : CCO.UnarySupport.Structure.Embedding F (Target))
    (b c : P) (hGenerated : F.closure {b,c} = Set.univ)
    (T : SourceThetaRootPackage S H sap nr2
      (⟨e.point b,e.sort_eq b⟩ : (Hidden).Carrier (F.sort b))
      (⟨e.point c,e.sort_eq c⟩ : (Hidden).Carrier (F.sort c))) :
    ∃ f : CCO.UnarySupport.Structure.Embedding F (Target),
      Nonempty (CCO.UnarySupport.Structure.DiagramIso F
        ((Target).induce (Set.range f.point) (SourceSupport.embedding_range_closed f))) ∧
      ∀ anchor ∈ (Hidden).closure T.signatureAnchors, ∃ old : P, f.point old = anchor := by
  obtain ⟨f,hb,hc,_,hIso⟩ := one_factor_complete_closed_image S H sap nr2
    F e b c T.survives T.fine
  have hRange := embedding_two_generated_range (Hidden) F f b c hGenerated
  rw [hb,hc] at hRange
  let leftRoot := (Hidden).eval (rootBaseTerm S H sap nr2 (F.sort b))
    (.inl ⟨(F.sort b).down.1,T.x⟩)
  let rightRoot := (Hidden).eval (rootBaseTerm S H sap nr2 (F.sort c))
    (.inl ⟨(F.sort c).down.1,T.y⟩)
  have hSupport : T.oldAnchorSupport = Set.range f.point := by
    calc
      T.oldAnchorSupport = (Hidden).closure {leftRoot} ∪ (Hidden).closure {rightRoot} := rfl
      _ = (Hidden).closure ({leftRoot} ∪ {rightRoot}) :=
        ((Hidden).closure_union {leftRoot} {rightRoot}).symm
      _ = (Hidden).closure {leftRoot,rightRoot} := by congr 1
      _ = (Target).closure {leftRoot,rightRoot} := (partialTarget_closure (Hidden) _).symm
      _ = Set.range f.point := hRange.symm
  refine ⟨f,hIso,?_⟩
  intro anchor hAnchor
  have hMem := T.full_anchor_closure_subset_old hAnchor
  rw [hSupport] at hMem
  exact hMem

/-- Source14 uniform-size result for every ACTUALLY used irreducible
old endpoint support. The chosen theta retains the FULL source menu and
all represented FULL-kernel signatures; its size includes all old anchors.
The source support test is requested only after its actual 2m_typ bound. -/
theorem typed_two_root_uniform_size
    (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))
    {P : Type z} [Finite P]
    (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (hUnary : UnaryAdmissible F (Target)) (b c : P) (hbc : b ≠ c)
    (hirr : (F.closureStructure {b,c}).Irreducible)
    (hTest : BoundedPairTest S H sap nr2 F b c) :
    let b' : F.closure {b,c} := ⟨b,F.subset_closure _ (by simp)⟩
    let c' : F.closure {b,c} := ⟨c,F.subset_closure _ (by simp)⟩
    Nat.card (F.closure {b,c}) ≤ 2 * originalSourceUniformNormalCodeBudget S H ∧
    ∃ e : CCO.UnarySupport.Structure.Embedding (F.closureStructure {b,c}) (Target),
      ∃ T : SourceThetaRootPackage S H sap nr2
        (⟨e.point b',e.sort_eq b'⟩ : (Hidden).Carrier (F.sort b))
        (⟨e.point c',e.sort_eq c'⟩ : (Hidden).Carrier (F.sort c)),
        (Nat.card (thetaVertices S T.words) + ((Hidden).closure T.signatureAnchors).ncard ≤
          sourcePairBudget S H sap) ∧
        ∃ f : CCO.UnarySupport.Structure.Embedding (F.closureStructure {b,c}) (Target),
          Nonempty (CCO.UnarySupport.Structure.DiagramIso (F.closureStructure {b,c})
            ((Target).induce (Set.range f.point) (SourceSupport.embedding_range_closed f))) ∧
          ∀ anchor ∈ (Hidden).closure T.signatureAnchors,
            ∃ old : F.closure {b,c}, f.point old = anchor := by
  dsimp only
  have hBound := actual_pair_support_bound S H sap nr2 F hUnary b c
  obtain ⟨e⟩ := hTest hirr hBound
  let b' : F.closure {b,c} := ⟨b,F.subset_closure _ (by simp)⟩
  let c' : F.closure {b,c} := ⟨c,F.subset_closure _ (by simp)⟩
  have hRoots : b' ≠ c' := fun he => hbc (congrArg Subtype.val he)
  let T := oneFactorRootPackage S H sap nr2 hCover (F.closureStructure {b,c}) e b' c' hRoots
  obtain ⟨f,hIso,hAnchors⟩ := one_factor_signature_old_preimages S H sap nr2
    (F.closureStructure {b,c}) e b' c' (pair_support_generated S H sap nr2 F b c) T
  exact ⟨hBound,e,T,actual_theta_and_all_anchors_bound S H sap nr2 T,f,hIso,hAnchors⟩

/-- Source14 complete-reflection result: EVERY surviving atom,
EVERY real pair of that atom, full DiagramIso onto EXACTLY the two
canonical target-root closure. The LOCAL bounded source scope is literal. -/
theorem typed_two_root_complete_reflection
    {P : Type z} [Finite P]
    (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (hUnary : UnaryAdmissible F (Target)) (b c : P) (hbc : b ≠ c)
    (hirr : (F.closureStructure {b,c}).Irreducible)
    (hTest : BoundedPairTest S H sap nr2 F b c) :
    let b' : F.closure {b,c} := ⟨b,F.subset_closure _ (by simp)⟩
    let c' : F.closure {b,c} := ⟨c,F.subset_closure _ (by simp)⟩
    Nat.card (F.closure {b,c}) ≤ 2 * originalSourceUniformNormalCodeBudget S H ∧
    ∃ e : CCO.UnarySupport.Structure.Embedding (F.closureStructure {b,c}) (Target),
      let q : (Hidden).Carrier (F.sort b) := ⟨e.point b',e.sort_eq b'⟩
      let s : (Hidden).Carrier (F.sort c) := ⟨e.point c',e.sort_eq c'⟩
      (pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)).Nonempty ∧
      ∀ a ∈ pairMenu S H sap nr2 (factorRecords S H sap nr2 q s),
        ∀ (x : X (F.sort b).down.1) (y : X (F.sort c).down.1), S.atomRel a x y →
        ∃ f : CCO.UnarySupport.Structure.Embedding (F.closureStructure {b,c}) (Target),
          f.point b' = (Hidden).eval (rootBaseTerm S H sap nr2 (F.sort b))
            (.inl ⟨(F.sort b).down.1,x⟩) ∧
          f.point c' = (Hidden).eval (rootBaseTerm S H sap nr2 (F.sort c))
            (.inl ⟨(F.sort c).down.1,y⟩) ∧
          Set.range f.point = (Target).closure
            {(Hidden).eval (rootBaseTerm S H sap nr2 (F.sort b)) (.inl ⟨(F.sort b).down.1,x⟩),
             (Hidden).eval (rootBaseTerm S H sap nr2 (F.sort c)) (.inl ⟨(F.sort c).down.1,y⟩)} ∧
          Nonempty (CCO.UnarySupport.Structure.DiagramIso (F.closureStructure {b,c})
            ((Target).induce (Set.range f.point) (SourceSupport.embedding_range_closed f))) := by
  exact bounded_pair_every_atom_complete_image S H sap nr2 F hUnary b c hbc hirr hTest

/-- Actual finite-index diagnostic, combining the genuine old source
SAP/semantic CCO with hereditary coarse-hidden SAP and the FG1 failure.
It does not assert that this nonterminal source satisfies full-cover
infinitude, or that its coarse J is FULL RAW exact. -/
theorem finite_index_hidden_sap_G1_failure :
    CCO.AgeSAP G1.source ∧ SemanticCCO.{0,0,z,0} G1.source ∧
      G1.Hidden.model.Homogeneous ∧ G1.Hidden.model.AgeSAP ∧
      (∀ a, relativeIndex G1.fineSetoid G1.coarseSetoid a = 2) ∧
      G1.source.diversityGuard (i := ()) (j := ())
        (fun x y : G1.Real => G1.block x = G1.block y) = ({G1.p,G1.q} : Set G1.Atom) ∧
      (∀ i j (word : PositiveWord G1.source i j),
        PositiveWord.profile G1.source word ≠ ({G1.p,G1.q} : Set G1.Atom)) ∧
      (∀ P : RawExact.Presentation G1.source () (),
        RawExact.evaluate G1.source P ≠ (fun x y : G1.Real => G1.block x = G1.block y)) :=
  ⟨G1.old_ageSAP,G1.semanticCCO,G1.Hidden.homogeneous,G1.Hidden.ageSAP,
    G1.coarse_fine_relative_index,G1.coarse_diagonal_diversity_guard,
    fun _ _ word => G1.no_positive_coarse_diagonal word,G1.coarse_block_not_raw_exact⟩

/-- C49: TWO directly imposed singleton labels agree because ONE
actual common fine atom lies in both, BEFORE graph-edge merging. -/
theorem common_menu_direct_labels_agree
    {i j : ι} (A : S.Menu i j) (hA : A.Nonempty) (a b : S.Atom i j)
    (ha : A ⊆ PositiveWord.profile S (.single a))
    (hb : A ⊆ PositiveWord.profile S (.single b)) : a = b := by
  obtain ⟨c,hc⟩ := hA
  have hca : c = a := ha hc
  have hcb : c = b := hb hc
  exact hca.symm.trans hcb

/-- Source14 pure private-cycle export AFTER actual graph-preserving
merge normalization. No merge provider or semantic-source premise is
an input. Outside one theta every retained theta contributes at most
one WHOLE positive branch with its literal OLD endpoint witnesses. -/
theorem typed_private_theta_cycle_source
    {Roots : Type u} {Gadgets : Type v} {Branches : Type w} {V : Type z}
    (P : PrivateBranchSystem Roots Gadgets Branches V) (C : P.Cycle) :
    (∃ g, C.ContainedInTheta g) ∨
      ((∀ b c : {b : Branches // P.KeptBranch b},
          C.UsedBranch b.val → C.UsedBranch c.val → P.owner b.val = P.owner c.val → b = c) ∧
        ∀ b : {b : Branches // P.KeptBranch b}, C.UsedBranch b.val →
          C.WholeBranch b.val ∧
          C.On (P.root (P.left (P.owner b.val))) ∧
          C.On (P.root (P.right (P.owner b.val)))) := by
  rcases P.merged_private_theta_cycle_dichotomy C with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h,?_⟩
    intro b hb
    exact ⟨C.used_branch_whole b.val hb,C.used_branch_old_endpoints b.val hb⟩

end
end CCO.GuardedTwoRoot
