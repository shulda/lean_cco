import CCO.ExactEPGeometry.OriginalRetainedSelectedOccupancyCharacter
import CCO.RigidGroupoid.Phase.AbstractSeeds
import CCO.RigidGroupoid.Geometry.PointAction

/-!
# B062 C85-C89: the REAL full selected occupancy groupoid acts on K/E classes

The actual quotient-source groupoid has an object for each original
E-occupancy component of true reached types, with its entire exact
Arrow Hom set and a complete C84 corrected character. Every selected
object's carrier is the literal quotient by the FULL projected gate
K/E, not the logical E-quotient point itself.

The actual Arrow quotientMap builds a functor to the complete
selected K/E class carriers. Its identity and composition equations
are the proven exact Arrow equations; it is FREE because two whole
Arrows agreeing on any one actual gate class coincide.

The existing finite seed-extension theorem is instantiated on THIS
fully constructed free action and its real C84 character. This
is a finite-marking provider for the actual quotient source, not
a statement that all locally allowed quotient finite diagrams have
already been realized by the old marked age (C89-C96 still OPEN).
No quotient SAP, new action section, independent character or
invented intermediate orbit is assumed.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RigidGroupoid.Phase
open CategoryTheory

noncomputable section

/-- The ACTUAL C85 selected point action: the complete occupancy
groupoid acts on its genuine projected K/E class carriers. The
source homogeneous AP+HOM-CCO CurrentSource supplies real quotient
maps and Arrow laws. -/
noncomputable def originalRetainedSelectedPointFunctor
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot)) :
    letI := originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
    OriginalReachedOccupancy A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E Kroot ⥤ Type v := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
  let Q : CurrentSource.{u,v,v,t} :=
    originalExactSelectedQuotientCurrentSource
      A B P transport base hBase E
  let C : ExactCalculus Q.source :=
    exactCalculus_of_homogeneous_CCO Q.source Q.homogeneous Q.cco
  letI : ∀ i : Q.Sorts, MulAction Q.G (Q.Point i) := Q.action
  letI : Groupoid Occ :=
    originalRetainedOccupancyGroupoid A B P transport tp
      hOne Kroot E hE
  let anchor : Occ → Reached B.source Kroot :=
    originalReachedOccupancyAnchor A B P base hBase E Kroot
  let K := fun z : Occ => originalRetainedSelectedKernel
    A B P transport tp hOne Kroot E hE (anchor z)
  exact {
    obj := fun z => (K z).Class
    map := fun R => TypeCat.ofHom (R.quotientMap Q.homogeneous)
    map_id := by
      intro z
      ext q
      exact Arrow.quotientMap_id Q.homogeneous q
    map_comp := by
      intro a b c R T
      ext q
      exact Arrow.quotientMap_comp Q.homogeneous C R T q
  }

/-- The true selected occupancy groupoid's action is FREE: two
complete exact Arrow relations with equal image of one actual
K/E class are the same whole Arrow. -/
theorem originalRetainedSelectedPointFunctor_free
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot)) :
    letI := originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
    Abstract.Free (originalRetainedSelectedPointFunctor
      A B P transport tp hOne Kroot E hE) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
  let Q : CurrentSource.{u,v,v,t} :=
    originalExactSelectedQuotientCurrentSource
      A B P transport base hBase E
  letI : ∀ i : Q.Sorts, MulAction Q.G (Q.Point i) := Q.action
  letI : Groupoid Occ :=
    originalRetainedOccupancyGroupoid A B P transport tp
      hOne Kroot E hE
  intro a b R T q he
  change R.quotientMap Q.homogeneous q =
    T.quotientMap Q.homogeneous q at he
  exact R.eq_of_agree_at Q.homogeneous T q he

/-- Genuine finite full-character seed extension for the selected
quotient group's ACTUAL point action, with every equality duplicate
and every complete Hom arrow included in the condition. It proves
an abstract global quotient marking on ALL K/E classes, not yet
the equivalence of the old/new finite marked ages. -/
theorem originalRetainedSelectedFiniteSeedExtension
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (s : Finset (Abstract.Point
      (originalRetainedSelectedPointFunctor A B P transport tp
        hOne Kroot E hE)))
    (ε : s → ZMod 2) :
    letI := originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
    let F := originalRetainedSelectedPointFunctor
      A B P transport tp hOne Kroot E hE
    let chi := originalRetainedSelectedOccupancyCharacter
      A B P transport tp hOne Kroot phase E hE
    (∃ mark, Abstract.IsMarking F chi mark ∧
      ∀ p : s, mark p.val = ε p) ↔
    ∀ (p q : s) (R : p.val.1 ⟶ q.val.1),
      F.map R p.val.2 = q.val.2 →
        ε q = ε p + chi.value R := by
  let Occ := OriginalReachedOccupancy A B P (P.parent r)
    (fun i => hOne (P.parent r) i) E Kroot
  letI : Groupoid Occ :=
    originalRetainedOccupancyGroupoid A B P transport tp
      hOne Kroot E hE
  let F := originalRetainedSelectedPointFunctor
    A B P transport tp hOne Kroot E hE
  let chi := originalRetainedSelectedOccupancyCharacter
    A B P transport tp hOne Kroot phase E hE
  exact Abstract.finite_seed_extension_iff F
    (originalRetainedSelectedPointFunctor_free A B P transport tp
      hOne Kroot E hE) chi s ε

end
end CCO.ExactEPGeometry
