import CCO.GuardedTwoRoot.JoinedFactorComparisons

/-! Complete binary source readback for EVERY surviving fine atom.
For each actual ordered pair of descendant term values, its source
orbital (including literal equality) is transferred to the target.
This gives reflection of every named comparison, without treating
one-way positive preservation as a whole closed-image isomorphism. -/

universe u v w r
namespace CCO.GuardedTwoRoot
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
open CCO.GroupActions
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
local notation "Lang" => originalCompletedLanguage S H sap nr2
local notation "Hidden" => originalCompletedStructure S H sap nr2

/-- The complete source family forces the SAME actual original orbital
for each ordered term pair. If the source values coincide, the actual
equality record is used; otherwise actual full binary coverage supplies
its unique off-diagonal orbital. No higher tuple motion is asserted. -/
theorem term_pair_motion_of_surviving_atom
    {C D E F : (Lang).Sorts} (q : (Hidden).Carrier C) (s : (Hidden).Carrier D)
    {a : S.Atom C.down.1 D.down.1}
    (ha : a ∈ pairMenu S H sap nr2 (factorRecords S H sap nr2 q s))
    {x : X C.down.1} {y : X D.down.1} (hxy : S.atomRel a x y)
    (left : Term Lang C E) (right : Term Lang D F) :
    ∃ g : G,
      originalCompletedNamedAct S H g ((Hidden).eval left q.val) =
        (namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 left) x).val ∧
      originalCompletedNamedAct S H g ((Hidden).eval right s.val) =
        (namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 right) y).val := by
  classical
  by_cases he : (Hidden).eval left q.val = (Hidden).eval right s.val
  · have hSort : E = F := ((Hidden).eval_sort left q.property).symm.trans
      ((congrArg (Hidden).sort he).trans ((Hidden).eval_sort right s.property))
    subst F
    let record : RootedComparison S H sap nr2 C D := {
      leftSort := E
      rightSort := E
      left := left
      right := right
      predicate := fun u v => u = v
      named := .equality E }
    have hSource : record.Holds q s := Subtype.ext he
    have hTarget := factorRecords_readback S H sap nr2 q s ha hxy record hSource
    change namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 left) x =
      namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 right) y at hTarget
    letI (T : (Lang).Sorts) : MulAction G ((Hidden).Carrier T) :=
      completedSortAction S H sap nr2 T
    obtain ⟨g,hg⟩ := completed_sort_transitive S H sap nr2 E ((Hidden).typedEval left q)
      (namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 left) x)
    refine ⟨g,congrArg Subtype.val hg,?_⟩
    change originalCompletedNamedAct S H g ((Hidden).eval right s.val) = _
    rw [← he]
    exact (congrArg Subtype.val hg).trans (congrArg Subtype.val hTarget)
  · obtain ⟨name,hSource⟩ := original_completed_distinct_pair_binary_exists S H sap
      ((Hidden).eval left q.val) ((Hidden).eval right s.val) he
    let record : RootedComparison S H sap nr2 C D := {
      leftSort := E
      rightSort := F
      left := left
      right := right
      predicate := fun u v => originalCompletedCylinderBinaryPredicate S H name u.val v.val
      named := .binary name }
    have hTarget := factorRecords_readback S H sap nr2 q s ha hxy record hSource
    exact same_binary_motion S H name hSource hTarget

/-- Reflection as well as preservation of EVERY allowed complete named
comparison, on EVERY pair of the surviving original atom. In particular
this includes equality and all named unary transition graph values. -/
theorem complete_named_pair_reflection
    {C D : (Lang).Sorts} (q : (Hidden).Carrier C) (s : (Hidden).Carrier D)
    {a : S.Atom C.down.1 D.down.1}
    (ha : a ∈ pairMenu S H sap nr2 (factorRecords S H sap nr2 q s))
    {x : X C.down.1} {y : X D.down.1} (hxy : S.atomRel a x y)
    (record : RootedComparison S H sap nr2 C D) :
    record.pullback.Holds x y ↔ record.Holds q s := by
  constructor
  · intro hTarget
    letI (T : (Lang).Sorts) : MulAction G ((Hidden).Carrier T) :=
      completedSortAction S H sap nr2 T
    obtain ⟨g,hLeft,hRight⟩ := term_pair_motion_of_surviving_atom S H sap nr2
      q s ha hxy record.left record.right
    have hLeft' : g • (Hidden).typedEval record.left q =
        namedRealTermMap S H sap nr2 record.pullback.left x := Subtype.ext hLeft
    have hRight' : g • (Hidden).typedEval record.right s =
        namedRealTermMap S H sap nr2 record.pullback.right y := Subtype.ext hRight
    have hOrb := named_comparison_is_one_orbital S H sap nr2 record.named
      (namedRealTermMap S H sap nr2 record.pullback.left x)
      (namedRealTermMap S H sap nr2 record.pullback.right y) hTarget
    change record.predicate _ _
    rw [hOrb]
    refine ⟨g⁻¹,?_,?_⟩
    · exact (congrArg (fun z : (Hidden).Carrier record.leftSort => g⁻¹ • z) hLeft'.symm).trans
        (inv_smul_smul g ((Hidden).typedEval record.left q))
    · exact (congrArg (fun z : (Hidden).Carrier record.rightSort => g⁻¹ • z) hRight'.symm).trans
        (inv_smul_smul g ((Hidden).typedEval record.right s))
  · exact factorRecords_readback S H sap nr2 q s ha hxy record

end
end CCO.GuardedTwoRoot
