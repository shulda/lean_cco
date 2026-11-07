import CCO.GuardedTwoRoot.JoinedFactorComparisons
import CCO.GuardedTwoRoot.UniformTheta

/-! The common source witness is already proved in JoinedFactorComparisons.
Only now do we deduplicate the actual record spectra, choose positive
word representatives and recognize the entire source menu as exact.
Every old record remains readable from this finite presentation. There
is no Helly or global-completion premise. Root-signature consistency is
not asserted by the formal theta vertex bound proved here. -/

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

/-- Distinct ACTUAL old pullback profiles from the entire factor, not
a finite syntax assumption on its unary term words. -/
def FactorProfiles {C D : (Lang).Sorts}
    (q : (Hidden).Carrier C) (s : (Hidden).Carrier D) :=
  {P : S.Menu C.down.1 D.down.1 //
    ∃ c ∈ factorRecords S H sap nr2 q s, c.profile = P}

instance factorProfiles_finite {C D : (Lang).Sorts}
    (q : (Hidden).Carrier C) (s : (Hidden).Carrier D) :
    Finite (FactorProfiles S H sap nr2 q s) := by
  letI : Fintype (S.Atom C.down.1 D.down.1) := S.finiteAtom _ _
  unfold FactorProfiles
  infer_instance

/-- Concrete finite presentation of ALL source comparisons. The chosen
words present exactly spectra of actual factor records, and their number
is bounded by the fixed old endpoint palette, independently of term syntax.
A fine atom and its actual pair are supplied by the earlier source witness,
never manufactured using this exact-domain recognition. -/
theorem factorRecords_finite_presentation
    (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))
    {C D : (Lang).Sorts} (q : (Hidden).Carrier C) (s : (Hidden).Carrier D)
    {a : S.Atom C.down.1 D.down.1}
    (ha : a ∈ pairMenu S H sap nr2 (factorRecords S H sap nr2 q s))
    {x : X C.down.1} {y : X D.down.1} (hxy : S.atomRel a x y) :
    ∃ words : List (PositiveWord S C.down.1 D.down.1),
      present S words = pairMenu S H sap nr2 (factorRecords S H sap nr2 q s) ∧
      words.length ≤ 2 ^ (S.finiteAtom C.down.1 D.down.1).card ∧
      ∀ word ∈ words, ∃ c ∈ factorRecords S H sap nr2 q s,
        PositiveWord.profile S word = c.profile := by
  classical
  letI : Fintype (S.Atom C.down.1 D.down.1) := S.finiteAtom _ _
  letI : Fintype (FactorProfiles S H sap nr2 q s) := Fintype.ofFinite _
  have hPositive (P : FactorProfiles S H sap nr2 q s) :
      ∃ word : PositiveWord S C.down.1 D.down.1, PositiveWord.profile S word = P.val := by
    obtain ⟨c,hc,hP⟩ := P.property
    obtain ⟨word,hword⟩ := c.profile_positive hCover hxy
      (all_atoms_read_all_comparisons S H sap nr2 _ ha hxy c hc)
    exact ⟨word,hword.trans hP⟩
  let chosen (P : FactorProfiles S H sap nr2 q s) : PositiveWord S C.down.1 D.down.1 :=
    (hPositive P).choose
  have hChosen (P : FactorProfiles S H sap nr2 q s) :
      PositiveWord.profile S (chosen P) = P.val := (hPositive P).choose_spec
  let candidates := (Finset.univ : Finset (FactorProfiles S H sap nr2 q s)).toList
  let words := candidates.map chosen
  refine ⟨words,?_,?_,?_⟩
  · ext b
    constructor
    · intro h c hc
      let P : FactorProfiles S H sap nr2 q s := ⟨c.profile,⟨c,hc,rfl⟩⟩
      have hP : P ∈ candidates := by simp [candidates]
      have hb := h (chosen P) (List.mem_map.mpr ⟨P,hP,rfl⟩)
      rwa [hChosen] at hb
    · intro h word hword
      obtain ⟨P,_,rfl⟩ := List.mem_map.mp hword
      rw [hChosen]
      obtain ⟨c,hc,hP⟩ := P.property
      exact hP ▸ h c hc
  · calc
      words.length = Fintype.card (FactorProfiles S H sap nr2 q s) := by
        simp only [words,candidates,List.length_map,Finset.length_toList,Finset.card_univ]
      _ ≤ Fintype.card (S.Menu C.down.1 D.down.1) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      _ = 2 ^ (S.finiteAtom C.down.1 D.down.1).card := Fintype.card_set
  · intro word hword
    obtain ⟨P,_,rfl⟩ := List.mem_map.mp hword
    obtain ⟨c,hc,hP⟩ := P.property
    exact ⟨c,hc,(hChosen P).trans hP.symm⟩

/-- The actual one-factor source instance: the common fine witness is
constructed first, then its FULL menu is placed in the original exact
family by a finite positive-word presentation. -/
theorem one_factor_exact_record_menu
    (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))
    {P : Type z} [Finite P]
    (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (e : CCO.UnarySupport.Structure.Embedding F (originalPartialTarget S H sap nr2))
    (b c : P) (hbc : b ≠ c) :
    let q : (Hidden).Carrier (F.sort b) := ⟨e.point b,e.sort_eq b⟩
    let s : (Hidden).Carrier (F.sort c) := ⟨e.point c,e.sort_eq c⟩
    Exact S (pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)) := by
  dsimp only
  obtain ⟨x,y,a,hxy,ha⟩ := one_factor_all_comparisons S H sap nr2 F e b c hbc
  obtain ⟨words,hWords,_,_⟩ := factorRecords_finite_presentation S H sap nr2 hCover
    ⟨e.point b,e.sort_eq b⟩ ⟨e.point c,e.sort_eq c⟩ ha hxy
  exact ⟨⟨a,ha⟩,words,hWords.symm⟩

/-- Canonical private theta for the actual factor menu. Its formal size
and every positive branch length depend only on the original language.
The remaining old root-signature anchors are a separate obligation. -/
theorem one_factor_canonical_theta
    (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))
    {P : Type z} [Finite P]
    (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (e : CCO.UnarySupport.Structure.Embedding F (originalPartialTarget S H sap nr2))
    (b c : P) (hbc : b ≠ c) :
    let q : (Hidden).Carrier (F.sort b) := ⟨e.point b,e.sort_eq b⟩
    let s : (Hidden).Carrier (F.sort c) := ⟨e.point c,e.sort_eq c⟩
    ∃ words : List (PositiveWord S (F.sort b).down.1 (F.sort c).down.1),
      present S words = pairMenu S H sap nr2 (factorRecords S H sap nr2 q s) ∧
      Nat.card (thetaVertices S words) ≤ canonicalThetaBudget S H sap ∧
      (∀ word ∈ words, TypedPrefix.length S word ≤ Nat.card (TypedPrefix.State S)) := by
  dsimp only
  let q : (Hidden).Carrier (F.sort b) := ⟨e.point b,e.sort_eq b⟩
  let s : (Hidden).Carrier (F.sort c) := ⟨e.point c,e.sort_eq c⟩
  let D : ExactMenu S := ⟨(F.sort b).down.1,(F.sort c).down.1,
    pairMenu S H sap nr2 (factorRecords S H sap nr2 q s),
    one_factor_exact_record_menu S H sap nr2 hCover F e b c hbc⟩
  exact ⟨fixedTheta S H sap D,fixedTheta_menu S H sap D,
    fixedTheta_vertices_le S H sap D,fixedTheta_word_length S H sap D⟩

end
end CCO.GuardedTwoRoot
