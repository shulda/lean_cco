import CCO.ExactEPGeometry.OriginalRetainedQuotientToSuccessorAge
import CCO.ExactEPGeometry.OriginalRetainedSuccessorToQuotientAge
import CCO.ExactEPGeometry.OriginalRetainedComparisonMotions
import CCO.ExactEPGeometry.NamedSourceIso

/-!
# B062 C96/C103: actual retained selected source isomorphism

BOTH whole finite-age inclusions and actual finite homogeneous motions
produce the genuine countable source isomorphism. The old and selected
canonical markings are independent: the old global-E point bijection is
only a comparison-code device, and is NOT asserted to preserve the new
canonical marking. The resulting true point equivalence has the proved
actual occupancy-child sort equivalence, and transports the entire new
optional-atom palette, including every child label and logical equality.
-/

universe u v w t z
namespace CCO.ExactEPGeometry
open APCharacter APCharacter.SourceAge APCharacter.Towers
open RigidGroupoid.Geometry FullPhaseLift.BinarySource.MarkedComparison
open CCO.SimultaneousQuotients.Towers
noncomputable section

variable (A B : CurrentSource.{u,v,w,t})
variable (P : UnaryReduct A.source B.source)
variable (transport : ExactTraceTransport A.source B.source P)
variable (tp : ExactTraceProduct A.source B.source P)
variable (hOne : ∀ i j : A.Sorts, i = j)
variable {r : B.Sorts} (Kroot : Kernel B.source r)
variable (phase : SourcePhase B.source B.homogeneous
  (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
variable (E : ExactEq A.source (P.parent r))
variable (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
  (current_kernel_exact_eq B Kroot))

/-- Actual countable back-and-forth, with both whole finite ages and
both true homogeneous source groups discharged inside the construction. -/
theorem originalRetainedSelectedPointEquiv_exists :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
    let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
    let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
    let M := SingleStep.successor QB φ
    let T := originalRetainedQuotientComparisonTable A B P transport tp hOne Kroot phase E hE
    let U := originalRetainedSuccessorComparisonTable A B P transport tp hOne Kroot phase E hE
    ∃ F : Sigma QN.Point ≃ Sigma M.Point,
      (∀ q, U.owner (F q) = T.owner q) ∧
      ∀ q s, U.colour (F q) (F s) = T.colour q s := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
  let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
  let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
  let M := SingleStep.successor QB φ
  letI := QN.source.finiteSort
  letI := M.source.finiteSort
  letI : ∀ i : QN.Sorts, Countable (QN.Point i) := QN.countable
  letI : ∀ i : M.Sorts, Countable (M.Point i) := M.countable
  exact actual_equiv_of_same_age
    (originalRetainedQuotientComparisonTable A B P transport tp hOne Kroot phase E hE)
    (originalRetainedSuccessorComparisonTable A B P transport tp hOne Kroot phase E hE)
    (originalRetainedQuotientToSuccessorAge A B P transport tp hOne Kroot phase E hE)
    (originalRetainedSuccessorToQuotientAge A B P transport tp hOne Kroot phase E hE)
    (originalRetainedQuotientComparisonTable_motions A B P transport tp hOne Kroot phase E hE)
    (originalRetainedSuccessorComparisonTable_motions A B P transport tp hOne Kroot phase E hE)

/-- Choose the actual source point equivalence from the proved full
age/motion theorem, rather than identifying independent canonical marks. -/
def originalRetainedSelectedPointEquiv :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
    let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
    let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
    Sigma QN.Point ≃ Sigma (SingleStep.successor QB φ).Point :=
  Classical.choose (originalRetainedSelectedPointEquiv_exists A B P transport tp hOne Kroot phase E hE)

/-- Its literal owner is the actual retained occupancy-child equivalence. -/
theorem originalRetainedSelectedPointEquiv_owner :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
    let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
    let F := originalRetainedSelectedPointEquiv A B P transport tp hOne Kroot phase E hE
    let e := originalRetainedOccupancyChildEquiv A B P transport tp hOne Kroot phase E hE
    ∀ q : Sigma QN.Point, (F q).1 = e q.1 :=
  (Classical.choose_spec (originalRetainedSelectedPointEquiv_exists
    A B P transport tp hOne Kroot phase E hE)).1

/-- Every actual complete new pair colour is preserved and reflected.
BOTH endpoint child names occur in the two full palette comparisons. -/
theorem originalRetainedSelectedPointEquiv_palette :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
    let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
    let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
    let M := SingleStep.successor QB φ
    let F := originalRetainedSelectedPointEquiv A B P transport tp hOne Kroot phase E hE
    ∀ q s q' s' : Sigma QN.Point,
      taggedColour QN.source q s = taggedColour QN.source q' s' ↔
      taggedColour M.source (F q) (F s) = taggedColour M.source (F q') (F s') := by
  dsimp only
  intro q s q' s'
  let F := originalRetainedSelectedPointEquiv A B P transport tp hOne Kroot phase E hE
  have hSpec := Classical.choose_spec (originalRetainedSelectedPointEquiv_exists
    A B P transport tp hOne Kroot phase E hE)
  have hT := originalRetainedQuotientComparisonTable_palette_iff
    A B P transport tp hOne Kroot phase E hE q' s' q s
  have hU := originalRetainedSuccessorComparisonTable_palette_iff
    A B P transport tp hOne Kroot phase E hE (F q') (F s') (F q) (F s)
  constructor
  · intro h
    obtain ⟨ho,hs,hc⟩ := hT.mp h
    exact hU.mpr ⟨(hSpec.1 q).trans (ho.trans (hSpec.1 q').symm),
      (hSpec.1 s).trans (hs.trans (hSpec.1 s').symm),
      (hSpec.2 q s).trans (hc.trans (hSpec.2 q' s').symm)⟩
  · intro h
    obtain ⟨ho,hs,hc⟩ := hU.mp h
    exact hT.mpr ⟨(hSpec.1 q).symm.trans (ho.trans (hSpec.1 q')),
      (hSpec.1 s).symm.trans (hs.trans (hSpec.1 s')),
      (hSpec.2 q s).symm.trans (hc.trans (hSpec.2 q' s'))⟩

/-- The genuine C103 retained selected quotient source isomorphism,
after precisely its proved actual occupancy-child sort reindexing. -/
def originalRetainedSelectedAtomicIso :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
    let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
    let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
    let M := SingleStep.successor QB φ
    let e := originalRetainedOccupancyChildEquiv A B P transport tp hOne Kroot phase E hE
    letI : Fintype (OriginalOccupancy A N (P.compose R) base hBase E) := QN.source.finiteSort
    AtomicIso QN.source (selectedSortAtomicSource M.source e.toEmbedding) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
  let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
  let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
  let M := SingleStep.successor QB φ
  let e := originalRetainedOccupancyChildEquiv A B P transport tp hOne Kroot phase E hE
  let F := originalRetainedSelectedPointEquiv A B P transport tp hOne Kroot phase E hE
  exact namedAtomicIso e F
    (originalRetainedSelectedPointEquiv_owner A B P transport tp hOne Kroot phase E hE)
    QN.source M.source
    (originalRetainedSelectedPointEquiv_palette A B P transport tp hOne Kroot phase E hE)

/-- BOTH full-age directions on arbitrary complete induced diagrams.
The successor diagram uses its true actual child names e(owner a), and its
tagged point injection is into the actual selected SourcePhase successor. This
applies to EVERY finite formal vertex set, including the empty diagram. -/
theorem originalRetainedSelectedFullAge_iff
    {V : Type z}
    (owner : V → OriginalOccupancy A (SingleStep.successor B phase)
      (P.compose (SingleStep.projection B phase)) (P.parent r)
      (fun i => hOne (P.parent r) i) E)
    (colour : ∀ a b,
      Option ((originalExactSelectedQuotientCurrentSource
        A (SingleStep.successor B phase) (P.compose (SingleStep.projection B phase))
        (ExactTraceTransport.compose P (SingleStep.projection B phase) transport
          (canonical_step_exact_transport B phase)) (P.parent r)
        (fun i => hOne (P.parent r) i) E).source.Atom (owner a) (owner b))) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
    let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
    let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
    let M := SingleStep.successor QB φ
    let e := originalRetainedOccupancyChildEquiv A B P transport tp hOne Kroot phase E hE
    let I := originalRetainedSelectedAtomicIso A B P transport tp hOne Kroot phase E hE
    (∃ point : ∀ a, QN.Point (owner a),
      Function.Injective (fun a => (⟨owner a,point a⟩ : Sigma QN.Point)) ∧
      ∀ a b, QN.source.colour (point a) (point b) = colour a b) ↔
    (∃ point : ∀ a, M.Point (e (owner a)),
      Function.Injective (fun a => (⟨e (owner a),point a⟩ : Sigma M.Point)) ∧
      ∀ a b, M.source.colour (point a) (point b) = (colour a b).map (I.atom _ _)) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
  let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
  let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
  let M := SingleStep.successor QB φ
  let e := originalRetainedOccupancyChildEquiv A B P transport tp hOne Kroot phase E hE
  letI : Fintype (OriginalOccupancy A N (P.compose R) base hBase E) := QN.source.finiteSort
  let I := originalRetainedSelectedAtomicIso A B P transport tp hOne Kroot phase E hE
  have h := atomicIso_inducedDiagram_iff I owner colour
  constructor
  · intro hNew
    obtain ⟨p,hp,hColour⟩ := h.mp hNew
    exact ⟨p,(selectedSortPoint_injective (X := M.Point) e.toEmbedding).comp hp,hColour⟩
  · rintro ⟨p,hp,hColour⟩
    apply h.mpr
    refine ⟨p,?_,hColour⟩
    intro a b hab
    exact hp (congrArg (selectedSortPoint (X := M.Point) e.toEmbedding) hab)


end
end CCO.ExactEPGeometry
