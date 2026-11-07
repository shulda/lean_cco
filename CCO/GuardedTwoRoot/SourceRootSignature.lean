import CCO.GuardedTwoRoot.SourceExactMenu
import CCO.UnaryTermsReturn.RootSignatureThetaBundle
import CCO.TransitionClosure.OriginalNamedAtomicBranch

/-! Actual complete root signatures of the SAME vetted factor. One
bounded actual source-record branch is retained in addition to the fixed
exact-menu theta. This matters when the fixed presentation is empty:
the intersection of zero diversity relations would include real equality.
The retained positive branch keeps the literal real diagonal excluded.
Every represented proper FULL functional kernel and every branch is kept.
Locating every resulting anchor in the OLD root term closures remains
a separate support/kernel-inclusion obligation. -/

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

/-- A mandatory binary identity-root record exists in the ACTUAL
complete diagram of every distinct source endpoint pair. -/
theorem factorRecords_nonempty {C D : (Lang).Sorts}
    (q : (Hidden).Carrier C) (s : (Hidden).Carrier D) (hne : q.val ≠ s.val) :
    (factorRecords S H sap nr2 q s).Nonempty := by
  obtain ⟨R,hR⟩ := original_completed_distinct_pair_binary_exists S H sap q.val s.val hne
  let d : RootedComparison S H sap nr2 C D := {
    leftSort := C
    rightSort := D
    left := .id C
    right := .id D
    predicate x y := originalCompletedCylinderBinaryPredicate S H R x.val y.val
    named := .binary R }
  exact ⟨d.pullback,d,hR,rfl⟩

/-- A nonempty list is essential for equality at ALL original pairs.
No logical real equality is silently inserted into a STRONG menu. -/
theorem menuRel_present_iff {i j : ι} (words : List (PositiveWord S i j))
    (hne : words ≠ []) (x : X i) (y : X j) :
    S.menuRel (present S words) x y ↔
      ∀ k : Fin words.length, S.menuRel (PositiveWord.profile S (words.get k)) x y := by
  constructor
  · rintro ⟨a,ha,hxy⟩ k
    exact ⟨a,ha _ (List.get_mem words k),hxy⟩
  · intro h
    have hLength : 0 < words.length := List.length_pos_iff.mpr hne
    obtain ⟨a,_,hxy⟩ := h ⟨0,hLength⟩
    refine ⟨a,?_,hxy⟩
    intro word hword
    obtain ⟨k,rfl⟩ := List.mem_iff_get.mp hword
    obtain ⟨b,hb,hbxy⟩ := h k
    have hab : a = b := Option.some.inj (hxy.symm.trans hbxy)
    exact hab ▸ hb

theorem theta_vertices_cons {i j : ι} (word : PositiveWord S i j)
    (words : List (PositiveWord S i j)) :
    Nat.card (thetaVertices S (word :: words)) =
      Nat.card (thetaVertices S words) + (TypedPrefix.length S word - 1) := by
  rw [theta_vertices_card,theta_vertices_card]
  simp only [List.length_cons,Fin.sum_univ_succ,List.get_cons_zero]
  have hTail : (∑ k : Fin words.length,
      (TypedPrefix.length S ((word :: words).get k.succ) - 1)) =
        ∑ k : Fin words.length, (TypedPrefix.length S (words.get k) - 1) := by
    apply Finset.sum_congr rfl
    intro k _
    rfl
  rw [hTail]
  omega

def nonemptyMenuRelation {i j : ι} (A : S.Menu i j) (hA : A.Nonempty) :
    OriginalNonemptyInvariantTypedRel (X := X) (G := G) i j := by
  refine ⟨⟨S.menuRel A,?_⟩,?_⟩
  · rintro g x y ⟨a,ha,hxy⟩
    exact ⟨a,ha,(S.colourInvariant_of_homogeneous H g x y).trans hxy⟩
  · obtain ⟨a,ha⟩ := hA
    obtain ⟨x,y,hxy⟩ := S.realized a
    exact ⟨x,y,a,ha,hxy⟩

/-- Construction from the actual source presentation, including its
whole-pair intersection and the actual surviving fine root edge. -/
def thetaRootDataOfPresentation {i j : ι}
    (A : S.Menu i j) (words : List (PositiveWord S i j))
    (hne : words ≠ []) (hWords : present S words = A)
    (x : X i) (y : X j) (a : S.Atom i j) (ha : a ∈ A) (hxy : S.atomRel a x y) :
    OriginalActualThetaRootData S H x y (Fin words.length) where
  direct := nonemptyMenuRelation S H A ⟨a,ha⟩
  branch k := originalPositiveStrongBranchRelation S H sap (words.get k)
  intersection x' y' := by
    change S.menuRel A x' y' ↔
      ∀ k : Fin words.length, S.menuRel (PositiveWord.profile S (words.get k)) x' y'
    rw [← hWords]
    exact menuRel_present_iff S words hne x' y'
  edge := ⟨a,ha,hxy⟩

/-- One finite source package, with its actual root edge and exactly
the real diversity direct/branch relations. Every kernel remains typed. -/
structure SourceThetaRootPackage {C D : (Lang).Sorts}
    (q : (Hidden).Carrier C) (s : (Hidden).Carrier D) where
  x : X C.down.1
  y : X D.down.1
  atom : S.Atom C.down.1 D.down.1
  fine : S.atomRel atom x y
  survives : atom ∈ pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)
  words : List (PositiveWord S C.down.1 D.down.1)
  nonempty : words ≠ []
  menu : present S words = pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)
  data : OriginalActualThetaRootData S H x y (Fin words.length)
  direct_eq : data.direct.val.val = S.menuRel
    (pairMenu S H sap nr2 (factorRecords S H sap nr2 q s))
  branch_eq : ∀ k, (data.branch k).val.val = S.menuRel (PositiveWord.profile S (words.get k))
  word_length : ∀ word ∈ words, TypedPrefix.length S word ≤ Nat.card (TypedPrefix.State S)
  size_bound : Nat.card (thetaVertices S words) ≤
    canonicalThetaBudget S H sap + (Nat.card (TypedPrefix.State S) - 1)

/-- Source-facing instance. No theta, common survivor, positive
pullback, invented quotient chart or global completion is an input. -/
def oneFactorRootPackage
    (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))
    {P : Type z} [Finite P]
    (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (e : CCO.UnarySupport.Structure.Embedding F (originalPartialTarget S H sap nr2))
    (b c : P) (hbc : b ≠ c) :
    let q : (Hidden).Carrier (F.sort b) := ⟨e.point b,e.sort_eq b⟩
    let s : (Hidden).Carrier (F.sort c) := ⟨e.point c,e.sort_eq c⟩
    SourceThetaRootPackage S H sap nr2 q s := by
  apply Classical.choice
  dsimp only
  classical
  let q : (Hidden).Carrier (F.sort b) := ⟨e.point b,e.sort_eq b⟩
  let s : (Hidden).Carrier (F.sort c) := ⟨e.point c,e.sort_eq c⟩
  obtain ⟨x,y,a,hxy,ha⟩ := one_factor_all_comparisons S H sap nr2 F e b c hbc
  obtain ⟨record,hRecord⟩ := factorRecords_nonempty S H sap nr2 q s
    (fun he => hbc (e.injective he))
  obtain ⟨seed,hSeed⟩ := record.profile_positive hCover hxy
    (all_atoms_read_all_comparisons S H sap nr2 _ ha hxy record hRecord)
  let E : ExactMenu S := ⟨(F.sort b).down.1,(F.sort c).down.1,
    pairMenu S H sap nr2 (factorRecords S H sap nr2 q s),
    one_factor_exact_record_menu S H sap nr2 hCover F e b c hbc⟩
  let words := shortWord S H sap seed :: fixedTheta S H sap E
  have hWords : present S words = pairMenu S H sap nr2 (factorRecords S H sap nr2 q s) := by
    rw [present_cons,shortWord_profile,hSeed,fixedTheta_menu]
    exact Set.inter_eq_right.mpr (fun t ht => ht record hRecord)
  exact ⟨{
    x := x
    y := y
    atom := a
    fine := hxy
    survives := ha
    words := words
    nonempty := List.cons_ne_nil _ _
    menu := hWords
    data := thetaRootDataOfPresentation S H sap _ words (List.cons_ne_nil _ _) hWords x y a ha hxy
    direct_eq := rfl
    branch_eq := fun _ => rfl
    word_length := by
      intro word hword
      rcases List.mem_cons.mp hword with hword | hword
      · subst word
        exact shortWord_length S H sap seed
      · exact fixedTheta_word_length S H sap E word hword
    size_bound := by
      rw [theta_vertices_cons]
      exact Nat.add_le_add (fixedTheta_vertices_le S H sap E)
        (Nat.sub_le_sub_right (shortWord_length S H sap seed) 1) }⟩

namespace SourceThetaRootPackage
variable {S H sap nr2} {C D : (originalCompletedLanguage S H sap nr2).Sorts}
variable {q : (originalCompletedStructure S H sap nr2).Carrier C}
variable {s : (originalCompletedStructure S H sap nr2).Carrier D}
variable (T : SourceThetaRootPackage S H sap nr2 q s)

/-- ALL direct and branch-forced equations, over EVERY represented
proper FULL functional kernel, hold at the SAME actual source pair. -/
theorem all_equations :
    ∀ d ∈ originalActualThetaRootSignature S H T.x T.y T.data,
      OriginalActualRootEquation S H sap nr2 d :=
  original_actual_theta_root_all_equations S H sap nr2 T.x T.y T.data

/-- The complete named unary closure is discharged for ANY finite
continuation term from each actual canonical transported target. -/
theorem all_named_continuations :
    ∀ d ∈ originalActualThetaRootSignature S H T.x T.y T.data,
      ∀ {k : ι} (F : OriginalNamedHiddenCoordinate S H k)
        (word : OriginalNamedRawUnaryTerm S H sap nr2
          (originalRootNamedTarget S H sap nr2 d.J d.T) F),
        OriginalNamedRawUnaryTerm.eval S H sap nr2 word
          (d.T.quotientEquiv (Quotient.mk d.J.val.val T.x)) =
        OriginalNamedRawUnaryTerm.eval S H sap nr2 word
          (Quotient.mk (originalRootNamedTarget S H sap nr2 d.J d.T).val.val T.y) :=
  original_actual_theta_root_all_named_continuations S H sap nr2 T.x T.y T.data

end SourceThetaRootPackage
end
end CCO.GuardedTwoRoot
