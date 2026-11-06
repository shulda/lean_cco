import CCO.ExactEPGeometry.OriginalExactOccupancy
import CCO.ExactEPGeometry.PrefixExactRestriction

/-!
# B062 C66: actual E-class carriers on occupancy-representative sorts

One original FULL RAW-exact equivalence E induces a global setoid on
the REAL tagged current prefix carrier and a separate equivalence on
the ACTUAL current unary sort NAMES (its type support, N06).

An occupancy class is literally a quotient of those current names.
Choose one parent sort of that class, and use the already PROVED
source exact-restriction rho to obtain a FULL exact current E-kernel
on that parent. Its quotient injects into the real GLOBAL E-class
quotient. Every individual global E-class meeting ANY type in the
occupancy class has a representative at this chosen parent, by the
proved actual N06 class-occupancy theorem.

Thus the selected local quotient points are exactly the actual old
E-classes of their occupancy component. These are not new independent
copies of quotient points; no quotient action, SAP or global section
is introduced. The next C67 will apply the fully NAMED-SORTED actual
joint exact quotient source provider to these genuine local kernels.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Actual original E supports form a REAL setoid on the finite
CURRENT unary names, with no fictitious unoccupied sorts. -/
def originalExactOccupancySetoid
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) : Setoid B.Sorts := by
  let hEq := originalExactTypeSupport_equiv A B P base hOne E
  exact {
    r := prefixSupport P (originalExactGlobalRelation A base hOne E)
    iseqv := ⟨
      (by intro i; exact hEq.refl i),
      (by intro i j h; exact hEq.symm i j h),
      (by intro i j k hij hjk; exact hEq.trans i j k hij hjk)⟩
  }

/-- An occupancy object is an ACTUAL class of current unary sorts. -/
abbrev OriginalOccupancy
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) : Type _ :=
  Quotient (originalExactOccupancySetoid A B P base hOne E)

/-- Fix a genuine parent representative in a given actual occupancy
class; each class is inhabited by quotient surjectivity. -/
def originalOccupancyRepresentative
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (c : OriginalOccupancy A B P base hOne E) : B.Sorts :=
  Classical.choose (Quotient.mk''_surjective c)

theorem originalOccupancyRepresentative_class
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (c : OriginalOccupancy A B P base hOne E) :
    (Quotient.mk'' (originalOccupancyRepresentative A B P base hOne E c) :
      OriginalOccupancy A B P base hOne E) = c :=
  Classical.choose_spec (Quotient.mk''_surjective c)

/-- Genuine E|p², which is an ACTUAL current FULL RAW-exact
equivalence from the proved old/current exact transport, not
a merely invariant nonexact equivalence. -/
def originalExactOnCurrentSort
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) (p : B.Sorts) :
    ExactEq B.source p :=
  PrefixExactRestriction.rho A B P transport p
    (oldExactEqCast A.source (hOne (P.parent p)).symm E)

/-- The actual source E-restriction agrees with the REAL E-class
setoid on tagged current points, including original equality. -/
theorem originalExactOnCurrentSort_iff
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (p : B.Sorts) (x y : B.Point p) :
    originalExactOnCurrentSort A B P transport base hOne E p x y ↔
      (currentOriginalExactSetoid A B P base hOne E).r
        (⟨p,x⟩ : Sigma B.Point) (⟨p,y⟩ : Sigma B.Point) := by
  exact (PrefixExactRestriction.rho_iff A B P transport p
      (oldExactEqCast A.source (hOne (P.parent p)).symm E) x y).trans
    (oldExactEqCast_iff A.source
      (hOne (P.parent p)).symm E (P.point p x) (P.point p y))

/-- The REAL E-classes in any selected current sort are genuine
quotient objects with the current FULL RAW-exact kernel, not an
independently postulated setoid. -/
abbrev OriginalSelectedClass
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) (p : B.Sorts) : Type _ :=
  Quotient (originalExactOnCurrentSort A B P transport base hOne E p).val.val

/-- The actual quotient map from one selected local current parent
to the WHOLE tagged E-class quotient. It is defined on true
`Quotient` classes and respects exactly the previously proved
same-sort E relation. -/
def selectedOriginalClassToGlobal
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) (p : B.Sorts) :
    OriginalSelectedClass A B P transport base hOne E p →
      Quotient (currentOriginalExactSetoid A B P base hOne E) :=
  Quotient.map
    (fun x : B.Point p => (⟨p,x⟩ : Sigma B.Point))
    (fun {x y} h =>
      (originalExactOnCurrentSort_iff A B P transport base hOne E p x y).mp h)

/-- No two different E-classes of a chosen parent are identified
when viewed as global ORIGINAL E-classes. -/
theorem selectedOriginalClassToGlobal_injective
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) (p : B.Sorts) :
    Function.Injective
      (selectedOriginalClassToGlobal A B P transport base hOne E p) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      have hGlobal :
          (currentOriginalExactSetoid A B P base hOne E).r
            (⟨p,x⟩ : Sigma B.Point) (⟨p,y⟩ : Sigma B.Point) := by
        exact Quotient.exact hab
      exact (originalExactOnCurrentSort_iff
        A B P transport base hOne E p x y).mpr hGlobal

/-- C66, individual-real-class strength. If an ACTUAL current type i
belongs to the occupancy class represented by p, then EVERY E-class
meeting i occurs among the quotient points of p/E|p². No unrelated
global E-class is assumed present at p. -/
theorem originalClass_occurs_at_representative
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (i p : B.Sorts) (x : B.Point i)
    (hSupport : (originalExactOccupancySetoid A B P base hOne E).r i p) :
    ∃ q : OriginalSelectedClass A B P transport base hOne E p,
      selectedOriginalClassToGlobal A B P transport base hOne E p q =
        (Quotient.mk'' (⟨i,x⟩ : Sigma B.Point) :
          Quotient (currentOriginalExactSetoid A B P base hOne E)) := by
  obtain ⟨y,hxy⟩ :=
    (originalExactClass_occupies_supported_type A B P base hOne E i p x).mp hSupport
  refine ⟨Quotient.mk'' y,?_⟩
  apply Quotient.sound
  exact (currentOriginalExactSetoid A B P base hOne E).symm hxy

/-- C66 for the CANONICALLY selected parent of a concrete occupancy
class. One original E-class meeting any parent in that occupancy
has a real, unique quotient representative at that selected parent. -/
theorem originalClass_at_canonical_occupancy_parent
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (c : OriginalOccupancy A B P base hOne E)
    (i : B.Sorts) (x : B.Point i)
    (hi : (Quotient.mk'' i : OriginalOccupancy A B P base hOne E) = c) :
    ∃ q : OriginalSelectedClass A B P transport base hOne E
        (originalOccupancyRepresentative A B P base hOne E c),
      selectedOriginalClassToGlobal A B P transport base hOne E
        (originalOccupancyRepresentative A B P base hOne E c) q =
          (Quotient.mk'' (⟨i,x⟩ : Sigma B.Point) :
            Quotient (currentOriginalExactSetoid A B P base hOne E)) := by
  apply originalClass_occurs_at_representative
    A B P transport base hOne E i
      (originalOccupancyRepresentative A B P base hOne E c) x
  exact Quotient.exact (hi.trans
    (originalOccupancyRepresentative_class A B P base hOne E c).symm)

end
end CCO.ExactEPGeometry
