import CCO.TerminalHiddenHN.ActualAge
import CCO.UnaryTermsReturn.CompletedNamedBinaryCoverage
import CCO.UnaryHN.TypedTransferBasis
import CCO.UnaryHN.RawEncoding.PairCoverage

/-! Source17 C24--C28: EVERY completed member of the actual full hidden
age is irreducible in its original signature. The positive cylinder for
each distinct pair is the actual exhaustive named cylinder supplied by
the original real source and visible SAP. Orphan-only members and arbitrary
isomorphic presentations are included; no universal joining edge is added.
The standalone exports use an explicit NR2 construction parameter, with
no FULL-cover or CCO hypothesis. Canonical terminal-age wrappers follow.

The final boundary is the explicitly weaker sort-only two-point reduct.
It does not assert reducibility of any member in the actual full signature.
-/

universe u v w r z
namespace CCO.TerminalHiddenHN
open CCO.TypedOrbitFrames CCO.UnaryTermsReturn CCO.HiddenSAPReadings
open CCO.UnarySupport CCO.UnarySupport.Structure
noncomputable section

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)

/-- The actual partial-domain target is total precisely on each named
input sort. This construction fact has no FULL-cover or CCO premise. -/
theorem original_target_total (nr2 : Selectors.OriginalNR2 S) :
    (originalPartialTarget S H sap nr2).Total := by
  classical
  intro F x hx
  change (originalCompletedLanguage S H sap nr2).Func at F
  change (originalCompletedStructure S H sap nr2).sort x =
    (originalCompletedLanguage S H sap nr2).input F at hx
  refine ⟨(originalCompletedStructure S H sap nr2).func F x,?_⟩
  change (originalCompletedStructure S H sap nr2).func F x ∈
    (if (originalCompletedStructure S H sap nr2).sort x =
        (originalCompletedLanguage S H sap nr2).input F then
      {(originalCompletedStructure S H sap nr2).func F x} else ∅)
  rw [ite_eq_left hx]
  rfl

/-- Genuine full embeddings reflect every actual unary domain. Neither
finiteness nor a completion of a larger source is needed. -/
theorem original_member_total (nr2 : Selectors.OriginalNR2 S) {V : Type z}
    {C : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) V}
    (e : C.Embedding (originalPartialTarget S H sap nr2)) : C.Total := by
  intro F x hx
  obtain ⟨y,hy⟩ := original_target_total S H sap nr2 F (e.point x)
    ((e.sort_eq x).trans hx)
  obtain ⟨q,hq,_⟩ := e.reflect_func F x y hy
  exact ⟨q,hq⟩

/-- Actual exhaustive cylinders join every distinct pair, including
mixed real/proper and orphan proper/proper pairs. The proof uses only
original homogeneity and visible SAP. NR2 fixes the named target. -/
theorem original_target_binary_coverage (nr2 : Selectors.OriginalNR2 S)
    (x y : OriginalCompletedNamedCarrier S H) (hne : x ≠ y) :
    CCO.UnaryHN.Raw.BinaryEdge (originalPartialTarget S H sap nr2) x y := by
  obtain ⟨R,hR⟩ := original_completed_distinct_pair_binary_exists S H sap x y hne
  refine ⟨R,rfl,?_⟩
  change originalCompletedCylinderBinaryPredicate S H R
    (if (0 : Fin 2).val = 0 then x else y)
    (if (1 : Fin 2).val = 0 then x else y)
  simpa [originalCompletedActualBinary] using hR

/-- The SAME full induced embedding reflects the actual named joining
cylinder on every distinct source pair, without a coverage or HN provider. -/
theorem original_hidden_binary_coverage_of_embedding
    (nr2 : Selectors.OriginalNR2 S) {V : Type z}
    {C : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) V}
    (e : C.Embedding (originalPartialTarget S H sap nr2)) :
    ∀ x y, x ≠ y → CCO.UnaryHN.Raw.BinaryEdge C x y := by
  intro x y hne
  obtain ⟨R,hR,hRel⟩ := original_target_binary_coverage S H sap nr2
    (e.point x) (e.point y) (fun h => hne (e.injective h))
  refine ⟨R,hR,e.reflect_rel R (fun i => if i.val = 0 then x else y) ?_⟩
  have hfun :
      e.point ∘ (fun i : Fin ((originalPartialSignature S H sap nr2).arity R) =>
        if i.val = 0 then x else y) =
        (fun i => if i.val = 0 then e.point x else e.point y) := by
    funext i
    by_cases hi : i.val = 0 <;> simp only [Function.comp_apply,hi,ite_true,ite_false]
  rw [hfun]
  exact hRel

/-- Standalone source C28 in the ACTUAL original full hidden signature:
every induced closed copy is irreducible, with NO FULL-cover, CCO, hidden
SAP, HN or obstruction hypothesis. It applies in particular to every
finite completed member, including empty and orphan-only members. -/
theorem original_hidden_irreducible_of_embedding
    (nr2 : Selectors.OriginalNR2 S) {V : Type z}
    {C : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) V}
    (e : C.Embedding (originalPartialTarget S H sap nr2)) : C.Irreducible :=
  CCO.UnaryHN.Raw.binary_coverage_irreducible C
    (original_member_total S H sap nr2 e)
    (original_hidden_binary_coverage_of_embedding S H sap nr2 e)

/-- Literal closed induced subsets of the actual interpreted target
have the same standalone C28 irreducibility, before any terminal HN use. -/
theorem original_hidden_closed_irreducible
    (nr2 : Selectors.OriginalNR2 S) (D : Set (OriginalCompletedNamedCarrier S H))
    (hD : (originalPartialTarget S H sap nr2).IsClosed D) :
    ((originalPartialTarget S H sap nr2).induce D hD).Irreducible :=
  original_hidden_irreducible_of_embedding S H sap nr2
    ((originalPartialTarget S H sap nr2).inclusion D hD)

variable (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))

/-- The actual full named signature joins every distinct ordered pair,
including mixed real/proper and proper/proper pairs, by a positive binary
tuple. The FULL-cover proof only fixes the shared target construction. -/
theorem target_binary_coverage (x y : Values S H) (hne : x ≠ y) :
    CCO.UnaryHN.Raw.BinaryEdge (Target S H sap hCover) x y :=
  original_target_binary_coverage S (HF S H) sap (NR2 S hCover) x y hne

/-- Full induced member embeddings reflect the SAME actual positive
cylinder. This is entire-age coverage, not selected tuple coverage or
mere membership in a finite completion. -/
theorem actualAge_binary_coverage {V : Type z}
    {C : CCO.UnarySupport.Structure (Sig S H sap hCover) V}
    (hC : ActualAge S H sap hCover C) :
    ∀ x y, x ≠ y → CCO.UnaryHN.Raw.BinaryEdge C x y := by
  obtain ⟨e⟩ := actualAge_embedding S H sap hCover hC
  exact original_hidden_binary_coverage_of_embedding S (HF S H) sap (NR2 S hCover) e

/-- Source `lem:typed-terminal-hidden-irreducible`, for EVERY finite
induced closed member in the original complete hidden signature. -/
theorem actual_hidden_irreducible {V : Type z}
    {C : CCO.UnarySupport.Structure (Sig S H sap hCover) V}
    (hC : ActualAge S H sap hCover C) : C.Irreducible := by
  obtain ⟨e⟩ := actualAge_embedding S H sap hCover hC
  exact original_hidden_irreducible_of_embedding S (HF S H) sap (NR2 S hCover) e

/-- The concrete completed-class premise consumed by the existing direct
HN theorem. No CCO, hidden SAP or obstruction assumption is used here. -/
theorem actualAge_allIrreducible :
    CCO.UnaryHN.Raw.AllIrreducible
      (ActualAge S H sap hCover : CCO.UnaryHN.Raw.Class.{max u v w,z} (Sig S H sap hCover)) := by
  intro V C hC
  exact actual_hidden_irreducible S H sap hCover hC

end

namespace SortOnlyBoundary

/-- A two-sort reduct retaining just the real/proper sort tags. In
particular this deliberately forgets the actual joining cylinders and
unary maps; it is not the full original hidden signature. -/
def signature : Signature where
  Sorts := Bool
  Func := Empty
  Rel := Empty
  input := Empty.elim
  output := Empty.elim
  arity := Empty.elim
  argument R := Empty.elim R
  finiteSort := inferInstance
  finiteFunc := inferInstance
  finiteRel := inferInstance

def pair : CCO.UnarySupport.Structure signature Bool where
  sort := id
  func F := Empty.elim F
  functional F := Empty.elim F
  func_sorted F := Empty.elim F
  rel R := Empty.elim R
  rel_sorted R := Empty.elim R

def split : pair.FreeDecomposition where
  left := {false}
  right := {true}
  left_closed F := Empty.elim F
  right_closed F := Empty.elim F
  cover := by ext x; cases x <;> simp
  left_proper := by
    intro h
    have ht : true ∈ ({false} : Set Bool) := h ▸ Set.mem_univ true
    simpa using ht
  right_proper := by
    intro h
    have hf : false ∈ ({true} : Set Bool) := h ▸ Set.mem_univ false
    simpa using hf
  rel_local R := Empty.elim R

/-- C48: sort tags alone allow the two points to split into closed
singleton factors. Actual full-cylinder coverage is substantive. -/
theorem reducible : ¬ pair.Irreducible := fun h => h.false split

theorem total : pair.Total := fun F => Empty.elim F

end SortOnlyBoundary
end CCO.TerminalHiddenHN
