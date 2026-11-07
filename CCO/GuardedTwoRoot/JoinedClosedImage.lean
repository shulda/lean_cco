import CCO.GuardedTwoRoot.CompletePairReadback

/-! ANY surviving fine atom gives a literal full old-factor embedding
onto a closed induced image. The same original motion maps BOTH roots,
so ALL descendant terms are transported together. This is stronger than
separately preserving primitive comparisons, and retains domains,
relations, equality and injectivity of the entire vetted source factor. -/

universe u v w r z
namespace CCO.GuardedTwoRoot
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
open CCO.GroupActions
noncomputable section

section PartialAut
variable {L : Language.{u}} [Finite L.Sorts] [Finite L.Func] [Finite L.Rel]
variable {V : Type v} {P : Type w} (A : CCO.UnaryFreshFrames.Structure L V)

/-- The total bookkeeping automorphism preserves and reflects the
GENUINE typed partial graph; off-sort identity values are not edges. -/
theorem partialTarget_aut_func_iff (g : A.Aut) (F : L.Func) (x y : V) :
    g • y ∈ (partialTarget A).func F (g • x) ↔ y ∈ (partialTarget A).func F x := by
  classical
  change (g • y ∈ if A.sort (g • x) = L.input F then {A.func F (g • x)} else ∅) ↔
    (y ∈ if A.sort x = L.input F then {A.func F x} else ∅)
  rw [A.aut_sort g x]
  by_cases hs : A.sort x = L.input F
  · simp only [if_pos hs,Set.mem_singleton_iff]
    rw [← A.aut_func g F x]
    exact g.val.injective.eq_iff
  · simp only [if_neg hs,Set.mem_empty_iff_false]

/-- Postcompose a full partial-source embedding with an ACTUAL total
signature automorphism, retaining genuine domain reflection. -/
def postcomposeAutEmbedding
    (C : CCO.UnarySupport.Structure (partialSignature L) P)
    (e : CCO.UnarySupport.Structure.Embedding C (partialTarget A)) (g : A.Aut) :
    CCO.UnarySupport.Structure.Embedding C (partialTarget A) where
  point p := g • e.point p
  sort_eq p := (A.aut_sort g (e.point p)).trans (e.sort_eq p)
  map_func F p q h := (partialTarget_aut_func_iff A g F _ _).mpr (e.map_func F p q h)
  map_rel R xs h := (A.aut_rel g R (e.point ∘ xs)).mpr (e.map_rel R xs h)
  injective p q h := e.injective (g.val.injective h)
  reflect_func F p y hy := by
    have hPre : g⁻¹ • y ∈ (partialTarget A).func F (e.point p) := by
      apply (partialTarget_aut_func_iff A g F (e.point p) (g⁻¹ • y)).mp
      simpa only [smul_inv_smul] using hy
    obtain ⟨q,hq,he⟩ := e.reflect_func F p (g⁻¹ • y) hPre
    exact ⟨q,hq,(congrArg (fun t : V => g • t) he).trans (smul_inv_smul g y)⟩
  reflect_rel R xs h := e.reflect_rel R xs ((A.aut_rel g R (e.point ∘ xs)).mp h)

/-- A literal two-generated source embedding has exactly the target
closure of its two root images; no extra target generator is inserted. -/
theorem embedding_two_generated_range
    (C : CCO.UnarySupport.Structure (partialSignature L) P)
    (e : CCO.UnarySupport.Structure.Embedding C (partialTarget A))
    (b c : P) (hGenerated : C.closure {b,c} = Set.univ) :
    Set.range e.point = (partialTarget A).closure {e.point b,e.point c} := by
  have h := embedding_closure_image e {b,c}
  simpa only [hGenerated,Set.image_univ,Set.image_pair] using h

end PartialAut

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
local notation "Lang" => originalCompletedLanguage S H sap nr2
local notation "Hidden" => originalCompletedStructure S H sap nr2

/-- The identity root terms yield ONE actual original motion on BOTH
old root values, for every original pair of ANY surviving atom. -/
theorem root_pair_motion_of_surviving_atom
    {C D : (Lang).Sorts} (q : (Hidden).Carrier C) (s : (Hidden).Carrier D)
    {a : S.Atom C.down.1 D.down.1}
    (ha : a ∈ pairMenu S H sap nr2 (factorRecords S H sap nr2 q s))
    {x : X C.down.1} {y : X D.down.1} (hxy : S.atomRel a x y) :
    ∃ g : G,
      originalCompletedNamedAct S H g q.val =
        (Hidden).eval (rootBaseTerm S H sap nr2 C) (.inl ⟨C.down.1,x⟩) ∧
      originalCompletedNamedAct S H g s.val =
        (Hidden).eval (rootBaseTerm S H sap nr2 D) (.inl ⟨D.down.1,y⟩) := by
  exact term_pair_motion_of_surviving_atom S H sap nr2 q s ha hxy (.id C) (.id D)

/-- The original pair motion gives the WHOLE source factor an induced
closed target image with the prescribed canonical root readings. This is
an actual full DiagramIso, not a conditional preservation provider. -/
theorem one_factor_complete_closed_image
    {P : Type z}
    (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (e : CCO.UnarySupport.Structure.Embedding F (originalPartialTarget S H sap nr2))
    (b c : P)
    {a : S.Atom (F.sort b).down.1 (F.sort c).down.1}
    (ha : a ∈ pairMenu S H sap nr2
      (factorRecords S H sap nr2 ⟨e.point b,e.sort_eq b⟩ ⟨e.point c,e.sort_eq c⟩))
    {x : X (F.sort b).down.1} {y : X (F.sort c).down.1} (hxy : S.atomRel a x y) :
    ∃ f : CCO.UnarySupport.Structure.Embedding F (originalPartialTarget S H sap nr2),
      f.point b = (Hidden).eval (rootBaseTerm S H sap nr2 (F.sort b))
        (.inl ⟨(F.sort b).down.1,x⟩) ∧
      f.point c = (Hidden).eval (rootBaseTerm S H sap nr2 (F.sort c))
        (.inl ⟨(F.sort c).down.1,y⟩) ∧
      (originalPartialTarget S H sap nr2).IsClosed (Set.range f.point) ∧
      Nonempty (CCO.UnarySupport.Structure.DiagramIso F
        ((originalPartialTarget S H sap nr2).induce (Set.range f.point)
          (SourceSupport.embedding_range_closed f))) := by
  obtain ⟨g,hgb,hgc⟩ := root_pair_motion_of_surviving_atom S H sap nr2
    ⟨e.point b,e.sort_eq b⟩ ⟨e.point c,e.sort_eq c⟩ ha hxy
  let f := postcomposeAutEmbedding (Hidden) F e (originalCompletedMotionHom S H sap nr2 g)
  exact ⟨f,hgb,hgc,SourceSupport.embedding_range_closed f,
    ⟨SourceSupport.embedding_image_iso f⟩⟩

/-- The induced closure of the actual endpoint pair is literally
TWO-generated in its own partial-source language. -/
theorem pair_support_generated
    {P : Type z}
    (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (b c : P) :
    let b' : F.closure {b,c} := ⟨b,F.subset_closure _ (by simp)⟩
    let c' : F.closure {b,c} := ⟨c,F.subset_closure _ (by simp)⟩
    (F.closureStructure {b,c}).closure {b',c'} = Set.univ := by
  dsimp only
  let b' : F.closure {b,c} := ⟨b,F.subset_closure _ (by simp)⟩
  let c' : F.closure {b,c} := ⟨c,F.subset_closure _ (by simp)⟩
  have h := F.closure_induce_image (F.isClosed_closure {b,c}) {b',c'}
  have hSeed : Subtype.val '' ({b',c'} : Set (F.closure {b,c})) = {b,c} := by
    simp only [Set.image_pair,b',c']
  rw [hSeed] at h
  apply Set.eq_univ_of_forall
  intro x
  have hx : x.val ∈ Subtype.val '' (F.closureStructure {b,c}).closure {b',c'} :=
    h.symm ▸ x.property
  obtain ⟨y,hy,he⟩ := hx
  exact (Subtype.ext he : y = x) ▸ hy

/-- Complete source-facing reflection for the actual irreducible OLD
pair support. The test chooses ONE local factor; EVERY atom in its menu
at EVERY actual real pair yields a full induced isomorphism onto EXACTLY
the closure of the canonical target roots. No ambient completion or
unjoined ancestor reflection is asserted. -/
theorem joined_pair_every_atom_complete_image
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
      (pairMenu S H sap nr2 (factorRecords S H sap nr2 q s)).Nonempty ∧
      ∀ a ∈ pairMenu S H sap nr2 (factorRecords S H sap nr2 q s),
        ∀ (x : X (F.sort b).down.1) (y : X (F.sort c).down.1), S.atomRel a x y →
        ∃ f : CCO.UnarySupport.Structure.Embedding (F.closureStructure {b,c})
            (originalPartialTarget S H sap nr2),
          f.point b' = (Hidden).eval (rootBaseTerm S H sap nr2 (F.sort b))
            (.inl ⟨(F.sort b).down.1,x⟩) ∧
          f.point c' = (Hidden).eval (rootBaseTerm S H sap nr2 (F.sort c))
            (.inl ⟨(F.sort c).down.1,y⟩) ∧
          Set.range f.point = (originalPartialTarget S H sap nr2).closure
            {(Hidden).eval (rootBaseTerm S H sap nr2 (F.sort b)) (.inl ⟨(F.sort b).down.1,x⟩),
             (Hidden).eval (rootBaseTerm S H sap nr2 (F.sort c)) (.inl ⟨(F.sort c).down.1,y⟩)} ∧
          Nonempty (CCO.UnarySupport.Structure.DiagramIso (F.closureStructure {b,c})
            ((originalPartialTarget S H sap nr2).induce (Set.range f.point)
              (SourceSupport.embedding_range_closed f))) := by
  dsimp only
  obtain ⟨e,hMenu⟩ := joined_pair_records_nonempty S H sap nr2 F hVet b c hbc hirr
  refine ⟨e,hMenu,?_⟩
  intro a ha x y hxy
  let b' : F.closure {b,c} := ⟨b,F.subset_closure _ (by simp)⟩
  let c' : F.closure {b,c} := ⟨c,F.subset_closure _ (by simp)⟩
  obtain ⟨f,hb,hc,_,hIso⟩ := one_factor_complete_closed_image S H sap nr2
    (F.closureStructure {b,c}) e b' c' ha hxy
  have hRange := embedding_two_generated_range (Hidden) (F.closureStructure {b,c})
    f b' c' (pair_support_generated S H sap nr2 F b c)
  rw [hb,hc] at hRange
  exact ⟨f,hb,hc,hRange,hIso⟩

end
end CCO.GuardedTwoRoot
