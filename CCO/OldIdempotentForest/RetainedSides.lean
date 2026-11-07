import CCO.OldIdempotentForest.GapPath

/-! A retained original side keeps its SAME old pair menu under ANY
homomorphism of a closed retained source. This applies equally to retained
macro letters and the fixed original anchor; no profile provider is assumed. -/

universe u v w r z
namespace CCO.OldIdempotentForest
open CCO.GuardedOldSeams CCO.GuardedTwoRoot
open CCO.UnaryTermsReturn CCO.TransitionClosure CCO.ParityHasse.Original
open CCO.HiddenSAPReadings CCO.TypedOrbitFrames CCO.UnaryFreshFrames
open CCO.UnarySupport CCO.UnarySupport.Structure
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
local notation "Hidden" => originalCompletedStructure S H sap nr2
variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)

/-- Restrict the retained-source homomorphism to the original complete
pair support, then move the SAME previously chosen local model. Every
original comparison holds at the arbitrary actual representative pair. -/
theorem retained_side_atom_mem {b c : P}
    (side : SupportedMacroSide S H sap nr2 F b c)
    {A : Set P} (hA : F.IsClosed A) (hb : b ∈ A) (hc : c ∈ A)
    (f : Hom (F.induce A hA) (originalPartialTarget S H sap nr2))
    (x : X (gapSort S H sap nr2 F b)) (y : X (gapSort S H sap nr2 F c))
    (hx : rootMap S H sap nr2 (F.sort b) x = f.point ⟨b,hb⟩)
    (hy : rootMap S H sap nr2 (F.sort c) y = f.point ⟨c,hc⟩)
    {a : S.Atom (gapSort S H sap nr2 F b) (gapSort S H sap nr2 F c)}
    (hxy : S.atomRel a x y) : a ∈ side.menu := by
  have hClosure : F.closure {b,c} ⊆ A := F.closure_minimal hA (by
    intro p hp
    rcases hp with rfl | hp
    · exact hb
    · exact hp ▸ hc)
  let localHom : Hom (F.closureStructure {b,c}) (originalPartialTarget S H sap nr2) := {
    point p := f.point ⟨p.val,hClosure p.property⟩
    sort_eq p := f.sort_eq ⟨p.val,hClosure p.property⟩
    map_func U p q h := f.map_func U
      ⟨p.val,hClosure p.property⟩ ⟨q.val,hClosure q.property⟩ h
    map_rel R xs h := f.map_rel R
      (fun i => ⟨(xs i).val,hClosure (xs i).property⟩) h }
  let b0 : F.closure {b,c} := ⟨b,F.subset_closure _ (by simp)⟩
  let c0 : F.closure {b,c} := ⟨c,F.subset_closure _ (by simp)⟩
  obtain ⟨g,hgb,hgc⟩ := local_embedding_to_hom_pair_motion S H sap nr2
    (F.closureStructure {b,c}) side.model localHom b0 c0
    (fun he => side.distinct (congrArg Subtype.val he))
  rintro record ⟨d,hd,rfl⟩
  apply d.pullback.atom_mem_of_holds hxy
  apply (d.pullback_holds_iff
    ⟨f.point ⟨b,hb⟩,f.sort_eq ⟨b,hb⟩⟩
    ⟨f.point ⟨c,hc⟩,f.sort_eq ⟨c,hc⟩⟩ x y hx hy).mpr
  exact d.motion_preserves g hgb hgc hd

/-- Actual representative distinctness supplies a fine atom, and the
original menu containment places it in this EXACT original branch word.
No embedding or reflection hypothesis on the retained-source Hom is used. -/
theorem retained_side_profile_of_hom {b c : P}
    (side : SupportedMacroSide S H sap nr2 F b c)
    {A : Set P} (hA : F.IsClosed A) (hb : b ∈ A) (hc : c ∈ A)
    (f : Hom (F.induce A hA) (originalPartialTarget S H sap nr2))
    (x : X (gapSort S H sap nr2 F b)) (y : X (gapSort S H sap nr2 F c))
    (hx : rootMap S H sap nr2 (F.sort b) x = f.point ⟨b,hb⟩)
    (hy : rootMap S H sap nr2 (F.sort c) y = f.point ⟨c,hc⟩)
    (hne : (Sigma.mk (gapSort S H sap nr2 F b) x : Sigma X) ≠
      Sigma.mk (gapSort S H sap nr2 F c) y) :
    S.menuRel (PositiveWord.profile S side.word) x y := by
  obtain ⟨a,ha⟩ := S.some_colour_of_ne x y hne
  exact ⟨a,side.contains (retained_side_atom_mem S H sap nr2 F side hA hb hc f x y hx hy ha),ha⟩

end
end CCO.OldIdempotentForest
