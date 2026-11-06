import CCO.ExactEPGeometry.OriginalReachedGlobalGauge
import CCO.RigidGroupoid.Phase.AbstractMarkings

/-!
# B062 C84/C93: exact objectwise gauge transfer of full groupoid markings

The phase correction on a genuine source gate tower is not an extra
marking choice. The REAL old reached character is changed by the
already constructed original E-occupancy offsets. The same offsets
give a bijection between full compatible groupoid markings for the
old character and those for its corrected character. Because bits
live in ZMod 2, this bijection is its own inverse.

The elementary lemma works for ALL arrows of an arbitrary full
groupoid action; the instance below uses the actual C79/C84 global
offsets of the original homogeneous source. The missing bridge
between selected E-quotient gate classes and original K-classes is
NOT replaced with a hypothesis here.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RigidGroupoid.Phase
open CategoryTheory

noncomputable section

/-- Correct every literal groupoid point by the true phase offset at
its source object, not a quotient of the bit function alone. -/
def gaugeMarking {J : Type u} [Groupoid.{v} J]
    (F : J ⥤ Type w) (gamma : J → ZMod 2)
    (mark : Abstract.Point F → ZMod 2) :
    Abstract.Point F → ZMod 2 :=
  fun p => mark p + gamma p.1

/-- A full marking for the genuine original character becomes a
full marking for its objectwise corrected character, for ALL Arrows. -/
theorem gaugeMarking_forward {J : Type u} [Groupoid.{v} J]
    (F : J ⥤ Type w) (chi : Abstract.Character J)
    (gamma : J → ZMod 2) (mark : Abstract.Point F → ZMod 2)
    (hmark : Abstract.IsMarking F chi mark) :
    Abstract.IsMarking F (gaugeCharacter chi gamma)
      (gaugeMarking F gamma mark) := by
  intro a b R q
  change mark ⟨b,F.map R q⟩ + gamma b =
    (mark ⟨a,q⟩ + gamma a) +
      (gamma a + chi.value R + gamma b)
  rw [hmark R q]
  have hDouble : gamma a + gamma a = 0 := by
    have h : ∀ z : ZMod 2, z + z = 0 := by decide
    exact h _
  calc
    (mark ⟨a,q⟩ + chi.value R) + gamma b =
        ((mark ⟨a,q⟩ + chi.value R) + gamma b) + 0 :=
      (add_zero _).symm
    _ = ((mark ⟨a,q⟩ + chi.value R) + gamma b) +
          (gamma a + gamma a) := by rw [hDouble]
    _ = (mark ⟨a,q⟩ + gamma a) +
          (gamma a + chi.value R + gamma b) := by abel

/-- Conversely any full corrected-character marking gives a full
marking of the ORIGINAL true character by the SAME objectwise offset.
No selected generator or independently defined quotient character. -/
theorem gaugeMarking_reverse {J : Type u} [Groupoid.{v} J]
    (F : J ⥤ Type w) (chi : Abstract.Character J)
    (gamma : J → ZMod 2) (mark : Abstract.Point F → ZMod 2)
    (hmark : Abstract.IsMarking F (gaugeCharacter chi gamma) mark) :
    Abstract.IsMarking F chi (gaugeMarking F gamma mark) := by
  intro a b R q
  change mark ⟨b,F.map R q⟩ + gamma b =
    (mark ⟨a,q⟩ + gamma a) + chi.value R
  have h := hmark R q
  change mark ⟨b,F.map R q⟩ =
    mark ⟨a,q⟩ + (gamma a + chi.value R + gamma b) at h
  rw [h]
  have hDouble : gamma b + gamma b = 0 := by
    have h : ∀ z : ZMod 2, z + z = 0 := by decide
    exact h _
  calc
    (mark ⟨a,q⟩ + (gamma a + chi.value R + gamma b)) + gamma b =
        ((mark ⟨a,q⟩ + gamma a) + chi.value R) +
          (gamma b + gamma b) := by abel
    _ = (mark ⟨a,q⟩ + gamma a) + chi.value R := by
      rw [hDouble,add_zero]

/-- At the level of ALL literal points the ZMod 2 gauge is a true
involution; one does not need a noncanonical section of any group. -/
theorem gaugeMarking_twice {J : Type u} [Groupoid.{v} J]
    (F : J ⥤ Type w) (gamma : J → ZMod 2)
    (mark : Abstract.Point F → ZMod 2) :
    gaugeMarking F gamma (gaugeMarking F gamma mark) = mark := by
  funext p
  change (mark p + gamma p.1) + gamma p.1 = mark p
  have h : gamma p.1 + gamma p.1 = 0 := by
    have hh : ∀ z : ZMod 2, z + z = 0 := by decide
    exact hh _
  calc
    (mark p + gamma p.1) + gamma p.1 =
        mark p + (gamma p.1 + gamma p.1) := add_assoc _ _ _
    _ = mark p := by rw [h,add_zero]

/-- ACTUAL B062 C84/C93 source: each marking for the real globally
corrected reached character yields a marking of the genuine original
full Reached groupoid. All old E-gate canonical offsets are supplied
by C79, not postulated as new parameters. -/
theorem originalReachedCorrectedMarking_toOriginal
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
      (current_kernel_exact_eq B Kroot)) :
    let C := exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco
    letI := Reached.groupoid B.homogeneous C (A := Kroot)
    let F := Reached.pointFunctor B.homogeneous C Kroot
    let gamma := originalReachedGlobalOffset A B P transport tp
      hOne Kroot phase E hE
    ∀ (mark : Abstract.Point F → ZMod 2),
      Abstract.IsMarking F
        (originalReachedGlobalCharacter A B P transport tp
          hOne Kroot phase E hE) mark →
      Abstract.IsMarking F phase.character
        (gaugeMarking F gamma mark) := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI : Groupoid (Reached B.source Kroot) :=
    Reached.groupoid B.homogeneous C (A := Kroot)
  let F := Reached.pointFunctor B.homogeneous C Kroot
  let gamma := originalReachedGlobalOffset A B P transport tp
    hOne Kroot phase E hE
  change ∀ (mark : Abstract.Point F → ZMod 2),
    Abstract.IsMarking F (gaugeCharacter phase.character gamma) mark →
      Abstract.IsMarking F phase.character
        (gaugeMarking F gamma mark)
  intro mark hmark
  exact gaugeMarking_reverse F phase.character gamma mark hmark

end
end CCO.ExactEPGeometry
