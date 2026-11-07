import CCO.HiddenSAPReadings.SourceSupport
import CCO.TerminalPowers.FullSource
import CCO.TypedOrbitFrames.FullCoverNR2
import CCO.TerminalHiddenHN.HEBridge

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

/-- The partial encoding is total exactly on each prescribed source
sort. Canonical off-sort bookkeeping contributes no displayed graph. -/
theorem target_total : (Target S H sap hCover).Total := by
  classical
  intro F x hx
  change (Lang S H sap hCover).Func at F
  change (Hidden S H sap hCover).sort x = (Lang S H sap hCover).input F at hx
  refine ⟨(Hidden S H sap hCover).func F x,?_⟩
  change (Hidden S H sap hCover).func F x ∈
    (if (Hidden S H sap hCover).sort x = (Lang S H sap hCover).input F then
      {(Hidden S H sap hCover).func F x} else ∅)
  rw [if_pos hx]
  rfl

theorem actualAge_total {V : Type z}
    {C : CCO.UnarySupport.Structure (Sig S H sap hCover) V}
    (hC : ActualAge S H sap hCover C) : C.Total := by
  obtain ⟨e⟩ := hC.2
  intro F x hx
  have ht := target_total S H sap hCover F (e.point x) ((e.sort_eq x).trans hx)
  obtain ⟨y,hy⟩ := ht
  obtain ⟨z,hz,_⟩ := e.reflect_func F x y hy
  exact ⟨z,hz⟩

/-- Full embeddings pull back actual-age membership across arbitrary
carrier universes, preserving every relation and partial unary domain. -/
theorem actualAge_hereditary_mixed {V : Type z} {W : Type*}
    {C : CCO.UnarySupport.Structure (Sig S H sap hCover) V}
    {D : CCO.UnarySupport.Structure (Sig S H sap hCover) W}
    (hD : ActualAge S H sap hCover D) (e : C.Embedding D) :
    ActualAge S H sap hCover C := by
  letI : Finite W := hD.1
  obtain ⟨f⟩ := hD.2
  exact ⟨Finite.of_injective e.point e.injective,⟨embedding_comp e f⟩⟩

theorem actualAge_hereditary :
    CCO.UnaryHN.Raw.Hereditary (ActualAge.{u,v,w,r,z} S H sap hCover) := by
  intro V W C D hD e
  exact actualAge_hereditary_mixed S H sap hCover hD e

theorem actualAge_completed :
    CCO.UnaryHN.Raw.CompletedClass (ActualAge.{u,v,w,r,z} S H sap hCover) := by
  intro V _ C hC
  exact actualAge_total S H sap hCover hC

theorem actualAge_induce {V : Type z}
    {C : CCO.UnarySupport.Structure (Sig S H sap hCover) V}
    (hC : ActualAge S H sap hCover C) (D : Set V) (hD : C.IsClosed D) :
    ActualAge S H sap hCover (C.induce D hD) :=
  actualAge_hereditary_mixed S H sap hCover hC (C.inclusion D hD)

/-- Membership supplies the full induced diagram of a finite CLOSED
subset of the actual target, including empty and orphan-only images. -/
theorem actualAge_closedImage {V : Type z}
    {C : CCO.UnarySupport.Structure (Sig S H sap hCover) V}
    (hC : ActualAge S H sap hCover C) :
    ∃ (D : Set (Values S H)) (_ : D.Finite)
      (hD : (Target S H sap hCover).IsClosed D),
      Nonempty (DiagramIso C ((Target S H sap hCover).induce D hD)) := by
  letI : Finite V := hC.1
  obtain ⟨e⟩ := hC.2
  exact ⟨Set.range e.point,Set.finite_range _,
    SourceSupport.embedding_range_closed e,⟨SourceSupport.embedding_image_iso e⟩⟩

theorem actualAge_of_closed (D : Set (Values S H)) (hFinite : D.Finite)
    (hD : (Target S H sap hCover).IsClosed D) :
    ActualAge S H sap hCover ((Target S H sap hCover).induce D hD) :=
  ⟨hFinite.to_subtype,⟨(Target S H sap hCover).inclusion D hD⟩⟩

end
end CCO.TerminalHiddenHN
