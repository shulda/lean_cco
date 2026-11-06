import CCO.ExactEPGeometry.OriginalCoherentAllparentGroupoid
import CCO.ExactEPGeometry.OriginalOccupancyRepresentatives

/-!
# B062 C82–C83: real E-class transport between duplicate quotient sorts

The simultaneous all-parent quotient has one local E-class quotient
for EVERY true current unary name. The selected occupancy quotient
retains only one such name per supported original E-component.

For every two actual E-supported current types i,j, C49 proves that
EVERY individual global old E-class represented in i is represented
in j. C66 proves injectivity of each selected local-to-global map.
Together these create a canonical, coherent equivalence between the
ACTUAL local E-quotient carriers i/E_i and j/E_j.

This is genuine exact E-class identification and works for every
supported type pair, including equal types and the real old diagonal.
There is no arbitrary group section, independent quotient action, SAP,
or assumption about projected exactness under sort deletion. The latter
is the separate remaining C82 provider obligation.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers

noncomputable section

/-- Every REAL E-class on i has a quotient representative on
the specified E-supported type j. This is actual C49 occupancy,
not merely a nonempty relation between some two classes. -/
theorem originalSupportedClass_exists_at
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (i j : B.Sorts)
    (hSup : (originalExactOccupancySetoid
      A B P base hOne E).r i j)
    (q : OriginalSelectedClass A B P transport base hOne E i) :
    ∃ r : OriginalSelectedClass A B P transport base hOne E j,
      selectedOriginalClassToGlobal A B P transport base hOne E j r =
        selectedOriginalClassToGlobal A B P transport base hOne E i q := by
  induction q using Quotient.inductionOn with
  | _ x =>
    exact originalClass_occurs_at_representative
      A B P transport base hOne E i j x hSup

/-- The ACTUAL local quotient-class transport is determined
uniquely by its global original E-class. No point in the E-class
is chosen as a distinguished representative. -/
noncomputable def originalSupportedClassMap
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (i j : B.Sorts)
    (hSup : (originalExactOccupancySetoid
      A B P base hOne E).r i j) :
    OriginalSelectedClass A B P transport base hOne E i →
      OriginalSelectedClass A B P transport base hOne E j :=
  fun q => Classical.choose
    (originalSupportedClass_exists_at
      A B P transport base hOne E i j hSup q)

theorem originalSupportedClassMap_global
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (i j : B.Sorts)
    (hSup : (originalExactOccupancySetoid
      A B P base hOne E).r i j)
    (q : OriginalSelectedClass A B P transport base hOne E i) :
    selectedOriginalClassToGlobal A B P transport base hOne E j
      (originalSupportedClassMap
        A B P transport base hOne E i j hSup q) =
    selectedOriginalClassToGlobal A B P transport base hOne E i q :=
  Classical.choose_spec
    (originalSupportedClass_exists_at
      A B P transport base hOne E i j hSup q)

/-- Canonical E-class transport is injective: the global
E-class quotient distinguishes every local point. -/
theorem originalSupportedClassMap_injective
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (i j : B.Sorts)
    (hSup : (originalExactOccupancySetoid
      A B P base hOne E).r i j) :
    Function.Injective
      (originalSupportedClassMap
        A B P transport base hOne E i j hSup) := by
  intro x y hxy
  apply selectedOriginalClassToGlobal_injective
    A B P transport base hOne E i
  calc
    selectedOriginalClassToGlobal A B P transport base hOne E i x =
        selectedOriginalClassToGlobal A B P transport base hOne E j
          (originalSupportedClassMap
            A B P transport base hOne E i j hSup x) :=
      (originalSupportedClassMap_global
        A B P transport base hOne E i j hSup x).symm
    _ = selectedOriginalClassToGlobal A B P transport base hOne E j
          (originalSupportedClassMap
            A B P transport base hOne E i j hSup y) :=
      congrArg _ hxy
    _ = selectedOriginalClassToGlobal A B P transport base hOne E i y :=
      originalSupportedClassMap_global
        A B P transport base hOne E i j hSup y

/-- Every actual j/E_j class is reached by canonical transport
from i/E_i, since its own class also occupies the supported type i. -/
theorem originalSupportedClassMap_surjective
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (i j : B.Sorts)
    (hSup : (originalExactOccupancySetoid
      A B P base hOne E).r i j) :
    Function.Surjective
      (originalSupportedClassMap
        A B P transport base hOne E i j hSup) := by
  intro z
  let J := originalExactOccupancySetoid A B P base hOne E
  obtain ⟨x,hx⟩ := originalSupportedClass_exists_at
    A B P transport base hOne E j i (J.symm hSup) z
  refine ⟨x,?_⟩
  apply selectedOriginalClassToGlobal_injective
    A B P transport base hOne E j
  calc
    selectedOriginalClassToGlobal A B P transport base hOne E j
        (originalSupportedClassMap
          A B P transport base hOne E i j hSup x) =
      selectedOriginalClassToGlobal A B P transport base hOne E i x :=
        originalSupportedClassMap_global
          A B P transport base hOne E i j hSup x
    _ = selectedOriginalClassToGlobal A B P transport base hOne E j z := hx

/-- A genuine E-class carrier equivalence, canonically induced by
the SAME global E relation rather than independent choices of maps. -/
noncomputable def originalSupportedClassEquiv
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (i j : B.Sorts)
    (hSup : (originalExactOccupancySetoid
      A B P base hOne E).r i j) :
    OriginalSelectedClass A B P transport base hOne E i ≃
      OriginalSelectedClass A B P transport base hOne E j :=
  Equiv.ofBijective
    (originalSupportedClassMap A B P transport base hOne E i j hSup)
    ⟨originalSupportedClassMap_injective
      A B P transport base hOne E i j hSup,
     originalSupportedClassMap_surjective
      A B P transport base hOne E i j hSup⟩

/-- Actual source C83 coherence: the E-class map p→q followed
by q→r equals the direct p→r map. The proof is equality on
the real global E-class quotient, not merely a choice of paths. -/
theorem originalSupportedClassMap_comp
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (i j k : B.Sorts)
    (hij : (originalExactOccupancySetoid
      A B P base hOne E).r i j)
    (hjk : (originalExactOccupancySetoid
      A B P base hOne E).r j k)
    (x : OriginalSelectedClass A B P transport base hOne E i) :
    originalSupportedClassMap A B P transport base hOne E j k hjk
      (originalSupportedClassMap A B P transport base hOne E i j hij x) =
    originalSupportedClassMap A B P transport base hOne E i k
      ((originalExactOccupancySetoid A B P base hOne E).trans hij hjk) x := by
  apply selectedOriginalClassToGlobal_injective
    A B P transport base hOne E k
  calc
    selectedOriginalClassToGlobal A B P transport base hOne E k
        (originalSupportedClassMap A B P transport base hOne E j k hjk
          (originalSupportedClassMap A B P transport base hOne E i j hij x)) =
      selectedOriginalClassToGlobal A B P transport base hOne E j
        (originalSupportedClassMap A B P transport base hOne E i j hij x) :=
      originalSupportedClassMap_global A B P transport base hOne E j k hjk _
    _ = selectedOriginalClassToGlobal A B P transport base hOne E i x :=
      originalSupportedClassMap_global A B P transport base hOne E i j hij x
    _ = selectedOriginalClassToGlobal A B P transport base hOne E k
        (originalSupportedClassMap A B P transport base hOne E i k
          ((originalExactOccupancySetoid A B P base hOne E).trans hij hjk) x) :=
      (originalSupportedClassMap_global A B P transport base hOne E i k _ x).symm

end
end CCO.ExactEPGeometry
