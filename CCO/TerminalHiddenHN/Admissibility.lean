import CCO.GuardedTwoRoot.UnarySource
import CCO.TerminalHiddenHN.ActualAge
import CCO.UnaryHN.RawEncoding.Obstruction

/-! Actual closed singleton embeddings discharge unary admissibility.
A genuine HE into a fixed actual member embeds each WHOLE singleton
closure; the HN projection to an arbitrary ambient is not such a member. -/

universe u v w r z
namespace CCO.TerminalHiddenHN
open CCO.UnarySupport CCO.UnarySupport.Structure CCO.GuardedTwoRoot

/-- This restriction works for mixed source/target universes and for
genuinely partial unary domains. No totality or finite-size premise is used. -/
theorem unaryAdmissible_of_homEmbedding {L : Signature.{u}}
    {V : Type v} {W : Type w} {C : Structure L V} {A : Structure L W}
    (f : Hom C A) (hf : f.HomEmbedding) : UnaryAdmissible C A := by
  intro x
  exact ⟨f.restrictionEmbedding (C.isClosed_closure {x})
    (hf _ (C.isClosed_closure {x}) (C.singleton_irreducible x))⟩

open CCO.TypedOrbitFrames CCO.HiddenSAPReadings
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))
variable {V : Type z} (C : Structure (Sig S H sap hCover) V)

/-- HN actual membership of EACH literal one-generated diagram supplies
its genuine embedding into this fixed actual target. No global source
completion or projection to the arbitrary HN ambient is used. -/
theorem unaryAdmissible_of_oneGeneratedDomain
    (h : CCO.UnaryHN.Raw.OneGeneratedDomain (ActualAge S H sap hCover) C) :
    UnaryAdmissible C (Target S H sap hCover) :=
  fun x => (h x).2

theorem oneGeneratedDomain_iff_unaryAdmissible [Finite V] :
    CCO.UnaryHN.Raw.OneGeneratedDomain (ActualAge S H sap hCover) C ↔
      UnaryAdmissible C (Target S H sap hCover) := by
  refine ⟨unaryAdmissible_of_oneGeneratedDomain S H sap hCover C,?_⟩
  intro h x
  exact ⟨inferInstance,h x⟩

/-- The accepted irreducible-membership test includes the WHOLE actual
closed singleton diagram, even when displayed unary maps were partial. -/
theorem unaryAdmissible_of_irreducibles
    (h : CCO.UnaryHN.Raw.IrreduciblesIn (ActualAge S H sap hCover) C) :
    UnaryAdmissible C (Target S H sap hCover) := by
  apply unaryAdmissible_of_oneGeneratedDomain S H sap hCover C
  intro x
  exact C.singleton_mem_class (CCO.UnaryHN.Raw.irreduciblesIn_subsets h) x

theorem total_of_oneGeneratedDomain
    (h : CCO.UnaryHN.Raw.OneGeneratedDomain (ActualAge S H sap hCover) C) : C.Total :=
  total_of_unary_admissible (unaryAdmissible_of_oneGeneratedDomain S H sap hCover C h)
    (originalPartialTarget_total S (HF S H) sap (NR2 S hCover))

end CCO.TerminalHiddenHN
