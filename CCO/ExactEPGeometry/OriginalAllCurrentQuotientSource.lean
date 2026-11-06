import CCO.ExactEPGeometry.OriginalCurrentTypedQuotients
import CCO.APCharacter.Towers.CurrentSource

/-!
# B062 C67: the GENUINE all-parent typed E-quotient CurrentSource

The previously proved actual FULL RAW exact current kernel family
E|p² and I13 typed simultaneous quotient provider now construct a
real CurrentSource, not merely a collection of abstract source
properties. Its points are the LITERAL Quotient classes of the
actual local E restrictions; every pair atom is the real occurring
finite orbital. The inherited action is the actual quotient action
constructed from the current source's real B.G and invariant exact
kernels, never a section of the new full automorphism group.

The real source has countability, homogeneity, ordinary AP/JEP,
triangle fullness and HOM simple-cycle CCO by accepted I13. Logical
equality on local Quotient points is the true quotient identity;
it pulls back to the whole E|p² kernel, not to old logical identity.

This interface presently retains ALL current parent sort names.
C66 identifies repeated global E-classes across occupancy-related
parents; making exactly ONE parent sort per occupancy class by
restricting the actual full typed quotient source is a separate
C67 compatibility obligation, not silently asserted here.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open CCO.SimultaneousQuotients

noncomputable section

/-- The actual full orbital-language homogeneous AP+HOM CCO quotient
of the CURRENT many-sorted source by the chosen ORIGINAL full RAW
exact E|p² on EACH real parent. All standing properties are PROVED
by the accepted fully typed simultaneous quotient source theorem,
not assumed as a new provider. The index has all current parents;
occupancy-type merging follows separately. -/
noncomputable def originalExactAllCurrentQuotientCurrentSource
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) :
    CurrentSource.{u,v,v,t} := by
  let J : ∀ p : B.Sorts, Setoid (B.Point p) :=
    originalExactCurrentKernelFamily A B P transport base hOne E
  let W : ∀ p : B.Sorts, RawExact.NonemptyExact B.source p p :=
    originalExactCurrentKernelWords A B P transport base hOne E
  have hRep : ∀ p : B.Sorts,
      RawExact.evaluate B.source (W p).words = (J p).r :=
    originalExactCurrentKernelWords_relation A B P transport base hOne E
  letI : ∀ p : B.Sorts, Countable (B.Point p) := B.countable
  let properties : CCO.SimultaneousQuotients.SourceProperties.{u,v,w,t,max u v}
      B.source B.homogeneous J W hRep :=
    originalExactAllCurrentQuotientSourceProperties
      A B P transport base hOne E
  exact {
    Sorts := B.Sorts
    Point := fun p => Quotient (J p)
    source := CCO.SimultaneousQuotients.source
      B.source B.homogeneous J W hRep
    G := B.G
    group := inferInstance
    action := CCO.SimultaneousQuotients.action
      B.source B.homogeneous J W hRep
    homogeneous := properties.homogeneous
    countable := fun p =>
      CCO.SimultaneousQuotients.countable_carrier J p
    cco := properties.cycles
  }

end
end CCO.ExactEPGeometry
