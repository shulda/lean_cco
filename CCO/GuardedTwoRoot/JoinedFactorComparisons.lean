import CCO.GuardedTwoRoot.CommonSurvivor
import CCO.GuardedTwoRoot.LocalRepresentatives
import CCO.GuardedTwoRoot.UnarySource

/-! All comparisons below are selected in ONE actual old factor BEFORE
representative splitting. A single pair motion transports its entire
family of named term comparisons; the actual split representatives then
supply the simultaneous fine survivor. No exact-domain or Helly API is
used, and no embedding of a larger partial source is assumed. -/

universe u v w r z
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
local notation "Values" => OriginalCompletedNamedCarrier S H

/-- Real/proper representatives evaluate through the literal canonical
root projection. The output sort determines the representative's real sort. -/
theorem rootBaseTerm_of_represents {C : (Lang).Sorts} {a : Sigma X} {q : Values}
    (h : RealRepresents S H a q) (hq : (Hidden).sort q = C) :
    ∃ x : X C.down.1, (⟨C.down.1,x⟩ : Sigma X) = a ∧
      (Hidden).eval (rootBaseTerm S H sap nr2 C) (.inl ⟨C.down.1,x⟩) = q := by
  rcases C with ⟨⟨i,c⟩⟩
  rcases a with ⟨j,x⟩
  rcases h with h | ⟨D,h⟩
  · subst q
    change ULift.up (⟨j,Sum.inl ()⟩ : OriginalCompletedCoordinateCode S H) =
      ULift.up ⟨i,c⟩ at hq
    cases hq
    exact ⟨x,rfl,rfl⟩
  · subst q
    change ULift.up (⟨j,Sum.inr D⟩ : OriginalCompletedCoordinateCode S H) =
      ULift.up ⟨i,c⟩ at hq
    cases hq
    exact ⟨x,rfl,rootBaseTerm_proper S H sap nr2 D x⟩

/-- The source comparison starts at the ACTUAL hidden root sorts.
Its pullback is formed only by composing those terms with the actual
real identity/F_J projection, never with an arbitrary quotient section. -/
structure RootedComparison (C D : (Lang).Sorts) where
  leftSort : (Lang).Sorts
  rightSort : (Lang).Sorts
  left : Term Lang C leftSort
  right : Term Lang D rightSort
  predicate : (Hidden).Carrier leftSort → (Hidden).Carrier rightSort → Prop
  named : NamedComparison S H sap nr2 leftSort rightSort predicate

namespace RootedComparison
variable {S H sap nr2}
variable {C D : (originalCompletedLanguage S H sap nr2).Sorts}
variable (c : RootedComparison S H sap nr2 C D)

def Holds (q : (Hidden).Carrier C) (s : (Hidden).Carrier D) : Prop :=
  c.predicate ((Hidden).typedEval c.left q) ((Hidden).typedEval c.right s)

def pullback : PairComparison S H sap nr2 C.down.1 D.down.1 where
  leftSort := c.leftSort
  rightSort := c.rightSort
  left := representativeTerm S H sap nr2 c.left
  right := representativeTerm S H sap nr2 c.right
  predicate := c.predicate
  named := c.named

theorem pullback_holds_iff (q : (Hidden).Carrier C) (s : (Hidden).Carrier D)
    (x : X C.down.1) (y : X D.down.1)
    (hx : (Hidden).eval (rootBaseTerm S H sap nr2 C) (.inl ⟨C.down.1,x⟩) = q.val)
    (hy : (Hidden).eval (rootBaseTerm S H sap nr2 D) (.inl ⟨D.down.1,y⟩) = s.val) :
    c.pullback.Holds x y ↔ c.Holds q s := by
  have hLeft : namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 c.left) x =
      (Hidden).typedEval c.left q := by
    apply Subtype.ext
    exact (representativeTerm_eval S H sap nr2 c.left x).trans (congrArg _ hx)
  have hRight : namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 c.right) y =
      (Hidden).typedEval c.right s := by
    apply Subtype.ext
    exact (representativeTerm_eval S H sap nr2 c.right y).trans (congrArg _ hy)
  change c.predicate
    (namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 c.left) x)
    (namedRealTermMap S H sap nr2 (representativeTerm S H sap nr2 c.right) y) ↔ c.Holds q s
  rw [hLeft,hRight]
  rfl

/-- One original motion transports ALL descendants of the same two
roots. No separately selected model is used for a later comparison. -/
theorem motion_preserves {q q' : (Hidden).Carrier C} {s s' : (Hidden).Carrier D}
    (g : G) (hq : originalCompletedNamedAct S H g q.val = q'.val)
    (hs : originalCompletedNamedAct S H g s.val = s'.val) (h : c.Holds q s) :
    c.Holds q' s' := by
  letI (E : (Lang).Sorts) : MulAction G ((Hidden).Carrier E) :=
    completedSortAction S H sap nr2 E
  have hOrb := named_comparison_is_one_orbital S H sap nr2 c.named
    ((Hidden).typedEval c.left q) ((Hidden).typedEval c.right s) h
  change c.predicate _ _
  rw [hOrb]
  refine ⟨g,?_,?_⟩
  · apply Subtype.ext
    change originalCompletedNamedAct S H g ((Hidden).eval c.left q.val) =
      (Hidden).eval c.left q'.val
    exact ((Hidden).aut_eval (originalCompletedMotionHom S H sap nr2 g) c.left q.val).trans
      (congrArg _ hq)
  · apply Subtype.ext
    change originalCompletedNamedAct S H g ((Hidden).eval c.right s.val) =
      (Hidden).eval c.right s'.val
    exact ((Hidden).aut_eval (originalCompletedMotionHom S H sap nr2 g) c.right s.val).trans
      (congrArg _ hs)

end RootedComparison

/-- ALL named comparisons read from this one pair of actual OLD factor
roots, before the real representatives or their fine colour are chosen. -/
def factorRecords {C D : (Lang).Sorts}
    (q : (Hidden).Carrier C) (s : (Hidden).Carrier D) :
    Set (PairComparison S H sap nr2 C.down.1 D.down.1) :=
  {c | ∃ d : RootedComparison S H sap nr2 C D, d.Holds q s ∧ c = d.pullback}

/-- Concrete source-record assembly. The actual factor embedding is
used ONCE, splitting is used ONCE on that entire finite factor, and
one pair motion transfers EVERY comparison selected in its full named
diagram. No premise assumes their common survivor or joint satisfaction
at the chosen real representatives. -/
theorem one_factor_all_comparisons
    {P : Type z} [Finite P]
    (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (e : CCO.UnarySupport.Structure.Embedding F (originalPartialTarget S H sap nr2))
    (b c : P) (hbc : b ≠ c) :
    let q : (Hidden).Carrier (F.sort b) := ⟨e.point b,e.sort_eq b⟩
    let s : (Hidden).Carrier (F.sort c) := ⟨e.point c,e.sort_eq c⟩
    ∃ (x : X (F.sort b).down.1) (y : X (F.sort c).down.1)
      (a : S.Atom (F.sort b).down.1 (F.sort c).down.1),
      S.atomRel a x y ∧
      a ∈ pairMenu S H sap nr2 (factorRecords S H sap nr2 q s) := by
  dsimp only
  obtain ⟨r⟩ := split_finite_assignment S H e.point sap ∅ Set.finite_empty
  have hbSort : (Hidden).sort (r.point b) = F.sort b :=
    (congrArg ULift.up (r.sort_eq b)).trans (e.sort_eq b)
  have hcSort : (Hidden).sort (r.point c) = F.sort c :=
    (congrArg ULift.up (r.sort_eq c)).trans (e.sort_eq c)
  obtain ⟨x,hxRep,hx⟩ := rootBaseTerm_of_represents S H sap nr2
    ((SplitAssignment.allRepresentatives_reads r) sap nr2 b) hbSort
  obtain ⟨y,hyRep,hy⟩ := rootBaseTerm_of_represents S H sap nr2
    ((SplitAssignment.allRepresentatives_reads r) sap nr2 c) hcSort
  have hRealNe : (⟨(F.sort b).down.1,x⟩ : Sigma X) ≠ ⟨(F.sort c).down.1,y⟩ := by
    intro he
    exact hbc ((SplitAssignment.allRepresentatives_injective r) sap nr2
      (hxRep.symm.trans (he.trans hyRep)))
  obtain ⟨a,ha⟩ := S.some_colour_of_ne x y hRealNe
  obtain ⟨g,hgb,hgc⟩ := r.pair_motion b c (fun he => hbc (e.injective he))
  refine ⟨x,y,a,ha,?_⟩
  rintro record ⟨d,hSource,rfl⟩
  apply d.pullback.atom_mem_of_holds ha
  apply (d.pullback_holds_iff ⟨r.point b,hbSort⟩ ⟨r.point c,hcSort⟩ x y hx hy).mpr
  exact d.motion_preserves g hgb hgc hSource

/-- Apply the complete-pattern gate to precisely the ACTUALLY irreducible
closed old endpoint support. Its single embedding supplies the simultaneous
menu; no embedding or completion of the ambient partial source is required. -/
theorem joined_pair_records_nonempty
    {P : Type z} [Finite P]
    (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (hVet : JoinedAdmissible F (originalPartialTarget S H sap nr2))
    (b c : P) (hbc : b ≠ c) (hirr : (F.closureStructure {b,c}).Irreducible) :
    let b' : F.closure {b,c} := ⟨b,F.subset_closure _ (by simp)⟩
    let c' : F.closure {b,c} := ⟨c,F.subset_closure _ (by simp)⟩
    ∃ e : CCO.UnarySupport.Structure.Embedding (F.closureStructure {b,c})
        (originalPartialTarget S H sap nr2),
      let q : (Hidden).Carrier (F.sort b) := ⟨e.point b',e.sort_eq b'⟩
      let s : (Hidden).Carrier (F.sort c) := ⟨e.point c',e.sort_eq c'⟩
      (pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)).Nonempty := by
  dsimp only
  obtain ⟨e⟩ := joined_pair_witness hVet b c hirr
  let b' : F.closure {b,c} := ⟨b,F.subset_closure _ (by simp)⟩
  let c' : F.closure {b,c} := ⟨c,F.subset_closure _ (by simp)⟩
  have hRoots : b' ≠ c' := fun he => hbc (congrArg Subtype.val he)
  obtain ⟨x,y,a,_,ha⟩ := one_factor_all_comparisons S H sap nr2
    (F.closureStructure {b,c}) e b' c' hRoots
  exact ⟨e,a,ha⟩

/-- The menu assembled from the full factor has the source universal
readback quantifier: EVERY surviving old atom and EVERY real pair of
that atom preserve EVERY named source term comparison. -/
theorem factorRecords_readback
    {C D : (Lang).Sorts} (q : (Hidden).Carrier C) (s : (Hidden).Carrier D)
    {a : S.Atom C.down.1 D.down.1}
    (ha : a ∈ pairMenu S H sap nr2 (factorRecords S H sap nr2 q s))
    {x : X C.down.1} {y : X D.down.1} (hxy : S.atomRel a x y)
    (d : RootedComparison S H sap nr2 C D) (hd : d.Holds q s) :
    d.pullback.Holds x y :=
  all_atoms_read_all_comparisons S H sap nr2 _ ha hxy d.pullback ⟨d,hd,rfl⟩

/-- Only AFTER the concrete common atom exists does TOP certify each
individual source record as an actual positive old word profile. -/
theorem factorRecords_positive_of_atom
    (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))
    {C D : (Lang).Sorts} (q : (Hidden).Carrier C) (s : (Hidden).Carrier D)
    {a : S.Atom C.down.1 D.down.1}
    (ha : a ∈ pairMenu S H sap nr2 (factorRecords S H sap nr2 q s))
    {x : X C.down.1} {y : X D.down.1} (hxy : S.atomRel a x y)
    (d : RootedComparison S H sap nr2 C D) (hd : d.Holds q s) :
    ∃ word : PositiveWord S C.down.1 D.down.1,
      PositiveWord.profile S word = d.pullback.profile :=
  d.pullback.profile_positive hCover hxy
    (factorRecords_readback S H sap nr2 q s ha hxy d hd)

end
end CCO.GuardedTwoRoot
