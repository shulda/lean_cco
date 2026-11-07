import CCO.HiddenSAPReadings.SourceSupport
import CCO.TerminalPowers.FullSource
import CCO.TypedOrbitFrames.FullCoverNR2

/-! The ONE actual terminal hidden signature, target and entire finite
closed age used by the structural, HN and FullCode branches. Membership
is a full embedding into the actual target on an arbitrary carrier; no
point-generation, completion or representative choice is part of it. -/

universe u v w r z
namespace CCO.TerminalHiddenHN
open CCO.TerminalPowers CCO.TypedOrbitFrames CCO.UnaryFreshFrames
open CCO.UnaryTermsReturn
open CCO.HiddenSAPReadings CCO.UnarySupport CCO.UnarySupport.Structure
noncomputable section

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]

abbrev HF (H : HomogeneousSource S G) : HomogeneousSource S (FullAut S) :=
  full_homogeneous S H

abbrev NR2 (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i)) : Selectors.OriginalNR2 S :=
  original_nr2_of_all_full_covers_infinite S hCover

variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))

abbrev Lang := originalCompletedLanguage S (HF S H) sap (NR2 S hCover)
abbrev Values := OriginalCompletedNamedCarrier S (HF S H)
abbrev Hidden := originalCompletedStructure S (HF S H) sap (NR2 S hCover)
abbrev Sig := originalPartialSignature S (HF S H) sap (NR2 S hCover)
abbrev Target : CCO.UnarySupport.Structure (Sig S H sap hCover) (Values S H) :=
  originalPartialTarget S (HF S H) sap (NR2 S hCover)

/-- All actual relations are the original named binary cylinders. -/
@[simp] theorem sig_binary (R : (Sig S H sap hCover).Rel) :
    (Sig S H sap hCover).arity R = 2 := rfl

/-- The entire finite induced unary-closed actual age, on ANY carrier
presentation, including empty and orphan-only members. -/
def ActualAge {V : Type z} (C : CCO.UnarySupport.Structure (Sig S H sap hCover) V) : Prop :=
  Finite V ∧ Nonempty (C.Embedding (Target S H sap hCover))

theorem actualAge_finite {V : Type z}
    {C : CCO.UnarySupport.Structure (Sig S H sap hCover) V}
    (hC : ActualAge S H sap hCover C) : Finite V := hC.1

theorem actualAge_embedding {V : Type z}
    {C : CCO.UnarySupport.Structure (Sig S H sap hCover) V}
    (hC : ActualAge S H sap hCover C) :
    Nonempty (C.Embedding (Target S H sap hCover)) := hC.2

end
end CCO.TerminalHiddenHN
