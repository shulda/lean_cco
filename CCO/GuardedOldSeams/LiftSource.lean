import CCO.GuardedOldSeams.LiftFinite
import CCO.GuardedOldSeams.LiftGraphSemantics

/-! The actual source guarded visible graph. Its branches are the
original positive words of the fixed same-support B056 presentations.
Both completion directions have all source providers discharged. -/

universe u v w r z
namespace CCO.GuardedOldSeams
open CCO.UnarySupport CCO.UnarySupport.Structure
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
open CCO.GuardedTwoRoot CCO.StrongExact
noncomputable section

/-- The visible target is a finite complete induced part of the actual
old source, with every formal vertex realized injectively inside it. -/
def FiniteVisibleCompletion {ι : Type u} {X : ι → Type v}
    (S : AtomicSource.{u,v,w} ι X) {V : Type z} (D : PartialDiagram S V) : Prop :=
  ∃ A : FiniteInduced (X := X), ∃ f : DiagramHom D,
    f.IsInjective ∧ ∀ p, f.image p ∈ A.vertices

theorem finite_visible_completion_iff {ι : Type u} {X : ι → Type v}
    (S : AtomicSource.{u,v,w} ι X) {V : Type z} (D : PartialDiagram S V) :
    FiniteVisibleCompletion S D ↔ ∃ f : DiagramHom D, f.IsInjective := by
  constructor
  · rintro ⟨_,f,hf,_⟩
    exact ⟨f,hf⟩
  · rintro ⟨f,hf⟩
    letI : Finite V := D.finite_type
    exact ⟨⟨Set.range f.image,Set.finite_range _⟩,f,hf,fun p => Set.mem_range_self p⟩

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
variable (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
variable (tests : BoundedJoinedPairTests S H sap nr2 F)
variable (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))

/-- One designated real root per old source vertex and one private
theta for each actual joined unordered pair. Length-one branches are
retained and their compatible direct letters are merged literally. -/
def typedRootWordSystem : RootWordSystem S P (OrderedGuardedPair S H sap nr2 F) where
  sort p := (F.sort p).down.1
  left k := k.val.val.1
  right k := k.val.val.2
  left_ne_right k := k.val.property.1
  unordered_unique := orderedGuardedPair_unique S H sap nr2 F
  words k := (guardedPairPackage S H sap nr2 F hUnary tests hCover k.val).words

theorem typedRootWordSystem_present (k : OrderedGuardedPair S H sap nr2 F) :
    present S ((typedRootWordSystem S H sap nr2 F hUnary tests hCover).words k) =
      guardedPairMenu S H sap nr2 F hUnary tests k.val :=
  (guardedPairPackage S H sap nr2 F hUnary tests hCover k.val).menu

def typedRootWordSeeds :
    RootWordSeeds S (typedRootWordSystem S H sap nr2 F hUnary tests hCover) :=
  (typedRootWordSystem S H sap nr2 F hUnary tests hCover).seedsOfNonemptyPresent H sap
    (fun k => (typedRootWordSystem_present S H sap nr2 F hUnary tests hCover k).symm ▸
      guardedPairMenu_nonempty S H sap nr2 F hUnary tests k.val)

/-- Concrete finite typed visible lift G_typ(C), as an ordinary simple
partial diagram with every original private word edge present. -/
def G_typ : PartialDiagram S
    (typedRootWordSystem S H sap nr2 F hUnary tests hCover).Vertex :=
  (typedRootWordSystem S H sap nr2 F hUnary tests hCover).diagram
    (typedRootWordSeeds S H sap nr2 F hUnary tests hCover)

def OrderedRootRealization.wordRoots
    (R : OrderedRootRealization S H sap nr2 F hUnary tests) :
    (typedRootWordSystem S H sap nr2 F hUnary tests hCover).RootRealization where
  point := R.point
  injective := R.injective
  profile k := (typedRootWordSystem_present S H sap nr2 F hUnary tests hCover k).symm ▸
    R.guarded k

def orderedRootsOfWordRoots
    (R : (typedRootWordSystem S H sap nr2 F hUnary tests hCover).RootRealization) :
    OrderedRootRealization S H sap nr2 F hUnary tests where
  point := R.point
  injective := R.injective
  guarded k := (typedRootWordSystem_present S H sap nr2 F hUnary tests hCover k) ▸
    R.profile k

/-- The source15 binary guarded lift equivalence. The hidden completion
is finite, induced and unary closed in the actual named MI-only target.
There is no global source-completion premise, CCO premise or stronger
test over all arbitrary irreducible source substructures. -/
theorem typed_guarded_lift_equivalence :
    (∃ f : DiagramHom (G_typ S H sap nr2 F hUnary tests hCover), f.IsInjective) ↔
      FiniteHiddenCompletion S H sap nr2 F := by
  refine ((typedRootWordSystem S H sap nr2 F hUnary tests hCover).strong_completion_iff_root_realization
    H sap (typedRootWordSeeds S H sap nr2 F hUnary tests hCover)).trans ?_
  constructor
  · rintro ⟨R⟩
    exact (orderedRootsOfWordRoots S H sap nr2 F hUnary tests hCover R).finiteHiddenCompletion
  · intro h
    obtain ⟨R⟩ := (ordered_roots_iff_finite_hidden_completion S H sap nr2 F hUnary tests).mpr h
    exact ⟨R.wordRoots S H sap nr2 F hUnary tests hCover⟩

/-- Every visible completion defines the literal canonical hidden map,
and that same map is induced on every source irreducible. -/
theorem typed_guarded_lift_canonical_HE
    (f : DiagramHom (G_typ S H sap nr2 F hUnary tests hCover))
    (hf : f.IsInjective) :
    ∃ g : Hom F (originalPartialTarget S H sap nr2), g.HomEmbedding ∧
      ∀ p, g.point p = rootMap S H sap nr2 (F.sort p) (f.point (.inl p)) := by
  let wr := (typedRootWordSystem S H sap nr2 F hUnary tests hCover).rootsOfInjectiveHom
    H sap (typedRootWordSeeds S H sap nr2 F hUnary tests hCover) f hf
  let R := orderedRootsOfWordRoots S H sap nr2 F hUnary tests hCover wr
  exact ⟨R.hiddenHom,R.hiddenHom_HE,fun _ => rfl⟩

theorem typed_hidden_noncompletion_lifts
    (h : ¬ FiniteHiddenCompletion S H sap nr2 F) :
    ¬ ∃ f : DiagramHom (G_typ S H sap nr2 F hUnary tests hCover), f.IsInjective :=
  fun hf => h ((typed_guarded_lift_equivalence S H sap nr2 F hUnary tests hCover).mp hf)

/-- The same equivalence with both finite actual completed targets
displayed explicitly. No hypothetical ambient completion class occurs. -/
theorem typed_guarded_finite_lift_equivalence :
    FiniteVisibleCompletion S (G_typ S H sap nr2 F hUnary tests hCover) ↔
      FiniteHiddenCompletion S H sap nr2 F :=
  (finite_visible_completion_iff S _).trans
    (typed_guarded_lift_equivalence S H sap nr2 F hUnary tests hCover)

/-- Exact original-word forcing by every completion of the concrete
visible lift, without deleting singleton branches or changing letters. -/
theorem G_typ_word_readback
    (f : DiagramHom (G_typ S H sap nr2 F hUnary tests hCover))
    (k : OrderedGuardedPair S H sap nr2 F)
    (word : PositiveWord S (F.sort k.val.val.1).down.1 (F.sort k.val.val.2).down.1)
    (hword : word ∈ (guardedPairPackage S H sap nr2 F hUnary tests hCover k.val).words) :
    PositiveWord.represented S word (f.point (.inl k.val.val.1))
      (f.point (.inl k.val.val.2)) :=
  (typedRootWordSystem S H sap nr2 F hUnary tests hCover).hom_represented_word
    (typedRootWordSeeds S H sap nr2 F hUnary tests hCover) f k word hword

/-- Retain exactly the same fixed source words/menu, and read their
actual root data at another real pair of a surviving fine atom. -/
def rootPackageAtRealPair
    {C D : (originalCompletedLanguage S H sap nr2).Sorts}
    {q : (originalCompletedStructure S H sap nr2).Carrier C}
    {s : (originalCompletedStructure S H sap nr2).Carrier D}
    (T : SourceThetaRootPackage S H sap nr2 q s)
    (x : X C.down.1) (y : X D.down.1)
    (h : S.menuRel (pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)) x y) :
    SourceThetaRootPackage S H sap nr2 q s where
  x := x
  y := y
  atom := h.choose
  fine := h.choose_spec.2
  survives := h.choose_spec.1
  words := T.words
  nonempty := T.nonempty
  menu := T.menu
  data := thetaRootDataOfPresentation S H sap _ T.words T.nonempty T.menu
    x y h.choose h.choose_spec.1 h.choose_spec.2
  direct_eq := rfl
  branch_eq _ := rfl
  word_length := T.word_length
  size_bound := T.size_bound

/-- A package at the literal roots of this visible completion, still
using the one previously fixed complete old support and its same words. -/
def visibleRootPackage
    (f : DiagramHom (G_typ S H sap nr2 F hUnary tests hCover))
    (hf : f.IsInjective) (k : OrderedGuardedPair S H sap nr2 F) :=
  let wr := (typedRootWordSystem S H sap nr2 F hUnary tests hCover).rootsOfInjectiveHom
    H sap (typedRootWordSeeds S H sap nr2 F hUnary tests hCover) f hf
  rootPackageAtRealPair S H sap nr2
    (guardedPairPackage S H sap nr2 F hUnary tests hCover k.val)
    (f.point (.inl k.val.val.1)) (f.point (.inl k.val.val.2))
    (by
      change S.menuRel (guardedPairMenu S H sap nr2 F hUnary tests k.val)
        (f.point (.inl k.val.val.1)) (f.point (.inl k.val.val.2))
      rw [← typedRootWordSystem_present S H sap nr2 F hUnary tests hCover k]
      exact wr.profile k)

/-- Every represented FULL root-signature equation is forced at the
actual completed root pair, not only at the package's initial seed. -/
theorem G_typ_all_root_equations
    (f : DiagramHom (G_typ S H sap nr2 F hUnary tests hCover))
    (hf : f.IsInjective) (k : OrderedGuardedPair S H sap nr2 F) :
    let T := visibleRootPackage S H sap nr2 F hUnary tests hCover f hf k
    ∀ d ∈ originalActualThetaRootSignature S H T.x T.y T.data,
      OriginalActualRootEquation S H sap nr2 d :=
  (visibleRootPackage S H sap nr2 F hUnary tests hCover f hf k).all_equations

/-- Every finite continuation uses those same actual named root term
values; no later chart, quotient section or additional source test is chosen. -/
theorem G_typ_all_named_continuations
    (f : DiagramHom (G_typ S H sap nr2 F hUnary tests hCover))
    (hf : f.IsInjective) (k : OrderedGuardedPair S H sap nr2 F) :
    let T := visibleRootPackage S H sap nr2 F hUnary tests hCover f hf k
    ∀ d ∈ originalActualThetaRootSignature S H T.x T.y T.data,
      ∀ {j : ι} (J : OriginalNamedHiddenCoordinate S H j)
        (word : OriginalNamedRawUnaryTerm S H sap nr2
          (originalRootNamedTarget S H sap nr2 d.J d.T) J),
        OriginalNamedRawUnaryTerm.eval S H sap nr2 word
          (d.T.quotientEquiv (Quotient.mk d.J.val.val T.x)) =
        OriginalNamedRawUnaryTerm.eval S H sap nr2 word
          (Quotient.mk (originalRootNamedTarget S H sap nr2 d.J d.T).val.val T.y) :=
  (visibleRootPackage S H sap nr2 F hUnary tests hCover f hf k).all_named_continuations

end
end CCO.GuardedOldSeams
