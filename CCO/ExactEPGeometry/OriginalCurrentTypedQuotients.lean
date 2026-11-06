import CCO.ExactEPGeometry.OriginalOccupancyRepresentatives
import CCO.SimultaneousQuotients.Exports

/-!
# B062 C67: actual FULL typed simultaneous E-kernel quotient source

At a real homogeneous AP+HOM CCO current prefix B, the OLD original
full RAW-exact equivalence E has a genuinely exact restriction on
EVERY current named parent sort. Its true local setoid is the actual
restriction of the global old E-class relation, not an arbitrarily
specified invariant kernel or a nonexact old equivalence.

This module packages those real kernels with their witnessed nonempty
RAW exact word presentations and applies the ALREADY ACCEPTED,
fully NAMED-SORTED source provider `SimultaneousQuotients.simultaneous_exact_quotients`
to the ACTUAL many-parent current source B (not the one-original-sort
specialization). The resulting actual literal quotient family has
finite orbital languages, joint homogeneity, AP/JEP, triangle fullness,
and HOM simple-cycle CCO; no SAP, global quotient group section,
or strengthened old CCO assumption is introduced.

At this stage all current parent sorts are retained as named quotient
sorts. The C66 occupancy representatives have already been shown to
parametrize exactly the distinct GLOBAL E-classes. Identifying/restricting
these duplicate named carriers to one actual parent per occupancy class
is the next C67 interface; these declarations DO NOT claim that
coalescence has already happened.
-/

universe u v w t z

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RawExact
open CCO.SimultaneousQuotients

noncomputable section

/-- Actual current E|p² kernel for every REAL current named sort p;
each kernel is a full RAW-exact current equivalence via the proven
two-way canonical exact transport, not merely an invariant setoid. -/
def originalExactCurrentKernelFamily
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    ∀ p : B.Sorts, Setoid (B.Point p) :=
  fun p => (originalExactOnCurrentSort
    A B P transport base hOne E p).val.val

/-- A REAL nonempty equality-inclusive RAW exact presentation of
every selected current source E-kernel, chosen from its PROVED
FullExact property; no new word provider is supplied. -/
def originalExactCurrentKernelWords
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    ∀ p : B.Sorts, RawExact.NonemptyExact B.source p p :=
  fun p => Classical.choose
    (originalExactOnCurrentSort A B P transport base hOne E p).property

theorem originalExactCurrentKernelWords_relation
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    ∀ p : B.Sorts,
      RawExact.evaluate B.source
        (originalExactCurrentKernelWords
          A B P transport base hOne E p).words =
      (originalExactCurrentKernelFamily
        A B P transport base hOne E p).r := by
  intro p
  exact Classical.choose_spec
    (originalExactOnCurrentSort A B P transport base hOne E p).property

/-- Source C67, ALREADY at actual many-parent quotient source strength:
the fully typed simultaneous exact-quotient theorem is applied to
the NEW CURRENT prefix B, independently on every current sort p,
with kernels E|p² that are all genuine current full RAW exact.
No assumed quotient homogeneity/CCO, arbitrary mixed word descent,
one-original-sort provider swap, SAP or group-section hypothesis. -/
theorem originalExactAllCurrentQuotientSourceProperties
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    CCO.SimultaneousQuotients.SourceProperties.{u,v,w,t,z}
      B.source B.homogeneous
      (originalExactCurrentKernelFamily A B P transport base hOne E)
      (originalExactCurrentKernelWords A B P transport base hOne E)
      (originalExactCurrentKernelWords_relation
        A B P transport base hOne E) := by
  letI : ∀ p : B.Sorts, Countable (B.Point p) := B.countable
  exact CCO.SimultaneousQuotients.simultaneous_exact_quotients
    B.source B.homogeneous
    (originalExactCurrentKernelFamily A B P transport base hOne E)
    (originalExactCurrentKernelWords A B P transport base hOne E)
    (originalExactCurrentKernelWords_relation
      A B P transport base hOne E) B.cco

end
end CCO.ExactEPGeometry
