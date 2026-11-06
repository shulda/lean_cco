import CCO.GuardedTwoRoot.RepresentativeTerms

/-! Source14 C09--C14. Each record is an ACTUAL named binary orbital,
literal equality, or named unary graph, pulled back by actual named
real-source terms. One joint pair of distinct real witnesses supplies
one fine atom in ALL records. This proof uses neither exact-domain
recognition, Helly, positive profile multiplication, nor a cylinder
partition or pairwise-overlap substitute. -/

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

/-- A record retains its two typed actual terms and the literal allowed
comparison. A union of different orbital labels is not a record. -/
structure PairComparison (i j : ι) where
  leftSort : (Lang).Sorts
  rightSort : (Lang).Sorts
  left : Term Lang ⟨⟨i,.inl ()⟩⟩ leftSort
  right : Term Lang ⟨⟨j,.inl ()⟩⟩ rightSort
  predicate : (Hidden).Carrier leftSort → (Hidden).Carrier rightSort → Prop
  named : NamedComparison S H sap nr2 leftSort rightSort predicate

namespace PairComparison
variable {S H sap nr2} {i j : ι} (c : PairComparison S H sap nr2 i j)

def Holds (x : X i) (y : X j) : Prop :=
  c.predicate (namedRealTermMap S H sap nr2 c.left x)
    (namedRealTermMap S H sap nr2 c.right y)

/-- Exact old pullback with the source's universal `whenever` quantifier. -/
def profile : S.Menu i j := comparisonSpectrum S
  (namedRealTermMap S H sap nr2 c.left) (namedRealTermMap S H sap nr2 c.right) c.predicate

theorem atom_mem_of_holds {a : S.Atom i j} {x : X i} {y : X j}
    (hxy : S.atomRel a x y) (h : c.Holds x y) : a ∈ c.profile := by
  letI (C : (Lang).Sorts) : MulAction G ((Hidden).Carrier C) := completedSortAction S H sap nr2 C
  have hOrb := named_comparison_is_one_orbital S H sap nr2 c.named
    (namedRealTermMap S H sap nr2 c.left x) (namedRealTermMap S H sap nr2 c.right y) h
  intro x' y' hxy'
  obtain ⟨g,hgx,hgy⟩ := S.pair_homogeneous_of_homogeneous H x x' y y' (hxy.trans hxy'.symm)
  rw [hOrb]
  refine ⟨g,?_,?_⟩
  · exact (namedRealTermMap_equivariant S H sap nr2 c.left g x).symm.trans (congrArg _ hgx)
  · exact (namedRealTermMap_equivariant S H sap nr2 c.right g y).symm.trans (congrArg _ hgy)

theorem holds_iff_atom_mem {a : S.Atom i j} {x : X i} {y : X j}
    (hxy : S.atomRel a x y) : c.Holds x y ↔ a ∈ c.profile :=
  ⟨c.atom_mem_of_holds hxy,fun h => h x y hxy⟩

/-- Positivity is proved only after an ACTUAL fine witness. Literal
real identity with no distinct witnesses is never sent through TOP. -/
theorem profile_positive
    (hCover : ∀ k, OriginalAllFullCoversInfinite S (i := k))
    {a : S.Atom i j} {x : X i} {y : X j}
    (hxy : S.atomRel a x y) (h : c.Holds x y) :
    ∃ word : PositiveWord S i j, PositiveWord.profile S word = c.profile := by
  exact (named_term_pair_TOP S H sap nr2 hCover c.left c.right c.predicate c.named
    a x y hxy h).2.2

end PairComparison

/-- All records belong to the same old guarded pair. Membership keeps
the entire simultaneous family, including comparisons on descendants. -/
def pairMenu {i j : ι} (records : Set (PairComparison S H sap nr2 i j)) : S.Menu i j :=
  {a | ∀ c ∈ records, a ∈ c.profile}

/-- The source common-survivor argument: an already jointly realized
factor gives one atom satisfying every exact pulled-back record. -/
theorem one_source_support_per_guarded_pair
    {i j : ι} (records : Set (PairComparison S H sap nr2 i j))
    (x : X i) (y : X j) (hne : (⟨i,x⟩ : Sigma X) ≠ ⟨j,y⟩)
    (h : ∀ c ∈ records, c.Holds x y) :
    (pairMenu S H sap nr2 records).Nonempty := by
  obtain ⟨a,ha⟩ := S.some_colour_of_ne x y hne
  exact ⟨a,fun c hc => c.atom_mem_of_holds ha (h c hc)⟩

/-- Conversely EVERY surviving atom reads ALL recorded comparisons at
EVERY original endpoint pair of that colour, not just one chosen pair. -/
theorem all_atoms_read_all_comparisons
    {i j : ι} (records : Set (PairComparison S H sap nr2 i j))
    {a : S.Atom i j} (ha : a ∈ pairMenu S H sap nr2 records)
    {x : X i} {y : X j} (hxy : S.atomRel a x y) :
    ∀ c ∈ records, c.Holds x y := fun c hc => ha c hc x y hxy

end
end CCO.GuardedTwoRoot
