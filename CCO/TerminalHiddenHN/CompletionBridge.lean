import CCO.TerminalHiddenHN.ActualAge
import CCO.TerminalHiddenHN.Admissibility
import CCO.TerminalHiddenHN.HEBridge
import CCO.GuardedOldSeams.LiftFinite
import Mathlib.Data.Fintype.EquivFin

/-! Finite completion in the actual closed hidden target is equivalent
to completion in the carrier-polymorphic actual age. A finite actual
image is explicitly copied into the HN carrier universe; no ambient
completion, global injectivity, or unary-admissibility premise is added. -/

universe u v w r z
namespace CCO.TerminalHiddenHN
open CCO.UnarySupport CCO.UnarySupport.Structure
open CCO.GuardedTwoRoot CCO.GuardedOldSeams
open CCO.HiddenSAPReadings CCO.TypedOrbitFrames CCO.UnaryTermsReturn
noncomputable section

/-- Reindex the ENTIRE typed partial diagram along an equivalence,
including its complete partial function domains and all relation tuples. -/
def pullbackStructure {L : Signature.{u}} {V : Type v} {W : Type w}
    (C : Structure L V) (e : W ≃ V) : Structure L W where
  sort x := C.sort (e x)
  func F x := {y | e y ∈ C.func F (e x)}
  functional F x y z hy hz := e.injective (C.functional F (e x) (e y) (e z) hy hz)
  func_sorted F x y hy := C.func_sorted F (e x) (e y) hy
  rel R xs := C.rel R (e ∘ xs)
  rel_sorted R xs hx := C.rel_sorted R (e ∘ xs) hx

def pullbackStructureIso {L : Signature.{u}} {V : Type v} {W : Type w}
    (C : Structure L V) (e : W ≃ V) : DiagramIso (pullbackStructure C e) C where
  equiv := e
  sort_eq _ := rfl
  func_iff _ _ _ := Iff.rfl
  rel_iff _ _ := Iff.rfl

def diagramIso_symm {L : Signature.{u}} {V : Type v} {W : Type w}
    {C : Structure L V} {D : Structure L W} (e : DiagramIso C D) : DiagramIso D C where
  equiv := e.equiv.symm
  sort_eq x := by
    simpa only [Equiv.apply_symm_apply] using (e.sort_eq (e.equiv.symm x)).symm
  func_iff F x y := by
    simpa only [Equiv.apply_symm_apply] using
      (e.func_iff F (e.equiv.symm x) (e.equiv.symm y)).symm
  rel_iff R xs := by
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using
      (e.rel_iff R (e.equiv.symm ∘ xs)).symm

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))
variable {P : Type z} [Finite P]
variable (C : Structure (Sig S H sap hCover) P)

/-- This equivalence applies to ANY finite partial source. A genuine HE
into the fixed actual target itself supplies the unary-admissibility
needed to prove source totality and take its actual finite closed image. -/
theorem finiteHiddenCompletion_iff_rawHasCompletion :
    FiniteHiddenCompletion S (HF S H) sap (NR2 S hCover) C ↔
      CCO.UnaryHN.Raw.HasCompletion (ActualAge S H sap hCover) C := by
  classical
  constructor
  · rintro ⟨D,hDfinite,hD,f,hf⟩
    letI : Finite D := hDfinite.to_subtype
    letI : Fintype D := Fintype.ofFinite D
    let Q := ULift.{z} (Fin (Fintype.card D))
    let e : Q ≃ D := Equiv.ulift.trans (Fintype.equivFin D).symm
    let A : Structure (Sig S H sap hCover) Q :=
      pullbackStructure ((Target S H sap hCover).induce D hD) e
    let iso : DiagramIso A ((Target S H sap hCover).induce D hD) :=
      pullbackStructureIso _ e
    let back : Embedding ((Target S H sap hCover).induce D hD) A :=
      (diagramIso_symm iso).toEmbedding
    let g : Hom C A := hom_postcompose_embedding f back
    have hg : g.HomEmbedding := homEmbedding_postcompose_embedding f hf back
    have hAge : ActualAge S H sap hCover A :=
      ⟨inferInstance,⟨embedding_comp iso.toEmbedding ((Target S H sap hCover).inclusion D hD)⟩⟩
    exact ⟨Q,inferInstance,A,hAge,g.point,homEmbedding_to_rawHE g hg⟩
  · rintro ⟨W,_hW,A,hA,f,hf⟩
    obtain ⟨e⟩ := actualAge_embedding S H sap hCover hA
    let g : Hom C (Target S H sap hCover) := hom_postcompose_embedding hf.toHom e
    have hg : g.HomEmbedding := homEmbedding_postcompose_embedding hf.toHom
      (rawHE_to_homEmbedding hf.toHom hf) e
    have hUnary := unaryAdmissible_of_homEmbedding g hg
    have hTotal : C.Total := total_of_unary_admissible hUnary
      (originalPartialTarget_total S (HF S H) sap (NR2 S hCover))
    exact finite_closed_HE_image g hTotal hg

theorem rawHasCompletion_iff_finiteHiddenCompletion :
    CCO.UnaryHN.Raw.HasCompletion (ActualAge S H sap hCover) C ↔
      FiniteHiddenCompletion S (HF S H) sap (NR2 S hCover) C :=
  (finiteHiddenCompletion_iff_rawHasCompletion S H sap hCover C).symm

end
end CCO.TerminalHiddenHN
