import CCO.TypedOrbitFrames.CompletedStructureAction
import CCO.PointGeneratedSAP.Original
import CCO.TerminalPowers.FullSource

/-! The genuine original real reduct of the actual completed structure.
Its selected old relations are exactly the existing fine original atoms,
read as real/real full semantic cylinders. Real equality is logical equality.
No hidden relation or hidden automorphism is used as an original premise. -/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.UnaryFreshFrames CCO.PointGeneratedSAP

universe u v w r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

def originalCompletedOldAtomName (H : HomogeneousSource S G)
    {i j : ι} (a : S.Atom i j) : OriginalCompletedCylinderBinaryName S H :=
  ⟨⟨i,.inl ()⟩,⟨j,.inl ()⟩,
    ⟨originalTypedCylinderName S (⊥ : ColourEq S i) (⊥ : ColourEq S j) a,⟨a,rfl⟩⟩⟩

theorem original_completed_old_atom_name_semantics
    (H : HomogeneousSource S G) {i j : ι} (a : S.Atom i j) (x : X i) (y : X j) :
    originalCompletedCylinderBinaryPredicate S H (originalCompletedOldAtomName S H a)
      (.inl ⟨i,x⟩) (.inl ⟨j,y⟩) ↔ S.colour x y = some a := by
  constructor
  · rintro ⟨hne,q,r,hq,hr,hRelation⟩
    cases hq
    cases hr
    change originalTypedCylinderName S (⊥ : ColourEq S i) (⊥ : ColourEq S j) a =
      originalTypedQuotientPairSpectrum S (⊥ : ColourEq S i) (⊥ : ColourEq S j)
        (Quotient.mk (⊥ : ColourEq S i).val x)
        (Quotient.mk (⊥ : ColourEq S j).val y) at hRelation
    have ha : a ∈ originalTypedQuotientPairSpectrum S (⊥ : ColourEq S i)
        (⊥ : ColourEq S j) (Quotient.mk (⊥ : ColourEq S i).val x)
          (Quotient.mk (⊥ : ColourEq S j).val y) := by
      rw [← hRelation]
      exact originalTypedCylinderName_contains_atom S _ _ a
    obtain ⟨x',y',hx,hy,hxy⟩ := ha
    have hxx : x' = x := Quotient.exact hx
    have hyy : y' = y := Quotient.exact hy
    change S.colour x' y' = some a at hxy
    simpa only [hxx,hyy] using hxy
  · intro hxy
    refine ⟨fun he => S.atomRel_ne hxy (Sum.inl.inj he),
      Quotient.mk (⊥ : ColourEq S i).val x,Quotient.mk (⊥ : ColourEq S j).val y,
      .real x,.real y,?_⟩
    exact (originalTypedQuotientPairSpectrum_eq_raw S H _ _ a x y hxy).symm

noncomputable def originalCompletedOriginal
    (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S) :
    Original (originalCompletedLanguage S H sap nr2) (OriginalCompletedNamedCarrier S H)
      (originalCompletedStructure S H sap nr2) where
  realSort C := ∃ i : ι, C.down = ⟨i,.inl ()⟩
  originalRel := Set.range (fun a : Σ i : ι, Σ j : ι, S.Atom i j =>
    originalCompletedOldAtomName S H a.2.2)

def originalCompletedRealNode (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S) (x : Sigma X) :
    (originalCompletedOriginal S H sap nr2).Real :=
  ⟨.inl x,⟨x.1,rfl⟩⟩

theorem original_completed_real_node_injective (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S) :
    Function.Injective (originalCompletedRealNode S H sap nr2) := by
  intro x y h
  exact Sum.inl.inj (congrArg Subtype.val h)

theorem original_completed_real_node_surjective (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S) :
    Function.Surjective (originalCompletedRealNode S H sap nr2) := by
  rintro ⟨x,hx⟩
  cases x with
  | inl x => exact ⟨x,rfl⟩
  | inr x =>
      rcases x with ⟨⟨i,⟨J,q⟩⟩,hNamed⟩
      obtain ⟨j,hj⟩ := hx
      cases hj

/-- Exactly the actual original real universe, not a new hidden-real
sort, and not a family of chosen quotient representatives. -/
noncomputable def originalCompletedRealEquiv (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S) :
    Sigma X ≃ (originalCompletedOriginal S H sap nr2).Real :=
  Equiv.ofBijective (originalCompletedRealNode S H sap nr2)
    ⟨original_completed_real_node_injective S H sap nr2,
      original_completed_real_node_surjective S H sap nr2⟩

end CCO.TypedOrbitFrames
