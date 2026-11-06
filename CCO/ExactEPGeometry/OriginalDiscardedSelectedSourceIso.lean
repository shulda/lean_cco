import CCO.ExactEPGeometry.OriginalDiscardedSelectedPalette
import CCO.ExactEPGeometry.NamedSourceIso

/-!
# B062 C103: discarded step is a genuine selected quotient source isomorphism

The sort equivalence is the proved actual occupancy equivalence. Its fibre
point equivalences are the literal global original-E class bijection. ALL
diversity names, including every cross-sort palette, are then transported
from their realized atomic relations. This is instantiated on the TRUE
selected old and SingleStep-successor quotient CurrentSources, with all
successor exact transport discharged internally. Every whole finite induced
diagram transports in both directions through the same source isomorphism.
-/

universe u v w t z
namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open RigidGroupoid.Geometry
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
variable (hNot : ¬ E ≤ PrefixExactLargestLift.largest
  A B P transport tp r (current_kernel_exact_eq B Kroot))

/-- The actual discarded selected quotient source isomorphism, after
the SPECIFIED equivalent occupancy names are reindexed. No CCO, orbit,
finite-age, exactness or automorphism-lifting provider is hypothesized. -/
def originalDiscardedSelectedAtomicIso :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
    let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
    let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let e := originalDiscardedOccupancySortClassEquiv A B P transport tp hOne Kroot phase E hNot
    letI : Fintype (OriginalOccupancy A N (P.compose R) base hBase E) := QN.source.finiteSort
    AtomicIso QN.source (selectedSortAtomicSource QB.source e.toEmbedding) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
  let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
  let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let e := originalDiscardedOccupancySortClassEquiv A B P transport tp hOne Kroot phase E hNot
  let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hBase E
  exact namedAtomicIso e f
    (originalDiscardedSelectedPointEquiv_owner A B P transport tp hOne Kroot phase E hNot)
    QN.source QB.source
    (fun q s q' s' => originalDiscardedSelectedTaggedColour_iff
      A B P transport tp hOne Kroot phase E hNot q' s' q s)

/-- BOTH full-age directions on arbitrary complete induced diagrams.
The old diagram uses its true occupancy names e(owner a), and its tagged
point injection is into the actual old selected quotient carrier. This
applies to EVERY finite formal vertex set, including the empty diagram. -/
theorem originalDiscardedSelectedFullAge_iff
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
    let e := originalDiscardedOccupancySortClassEquiv A B P transport tp hOne Kroot phase E hNot
    let I := originalDiscardedSelectedAtomicIso A B P transport tp hOne Kroot phase E hNot
    (∃ point : ∀ a, QN.Point (owner a),
      Function.Injective (fun a => (⟨owner a,point a⟩ : Sigma QN.Point)) ∧
      ∀ a b, QN.source.colour (point a) (point b) = colour a b) ↔
    (∃ point : ∀ a, QB.Point (e (owner a)),
      Function.Injective (fun a => (⟨e (owner a),point a⟩ : Sigma QB.Point)) ∧
      ∀ a b, QB.source.colour (point a) (point b) = (colour a b).map (I.atom _ _)) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
  let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
  let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let e := originalDiscardedOccupancySortClassEquiv A B P transport tp hOne Kroot phase E hNot
  letI : Fintype (OriginalOccupancy A N (P.compose R) base hBase E) := QN.source.finiteSort
  let I := originalDiscardedSelectedAtomicIso A B P transport tp hOne Kroot phase E hNot
  have h := atomicIso_inducedDiagram_iff I owner colour
  constructor
  · intro hNew
    obtain ⟨p,hp,hColour⟩ := h.mp hNew
    exact ⟨p,(selectedSortPoint_injective (X := QB.Point) e.toEmbedding).comp hp,hColour⟩
  · rintro ⟨p,hp,hColour⟩
    apply h.mpr
    refine ⟨p,?_,hColour⟩
    intro a b hab
    exact hp (congrArg (selectedSortPoint (X := QB.Point) e.toEmbedding) hab)

end
end CCO.ExactEPGeometry
