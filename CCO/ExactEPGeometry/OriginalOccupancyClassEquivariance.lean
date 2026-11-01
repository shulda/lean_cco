import CCO.ExactEPGeometry.OriginalOccupancyClassTransport
import CCO.ExactEPGeometry.OriginalCurrentTypedQuotients

/-!
# B062 C83: exact global-class readout and equivariance of merged sorts

The coherent local E-class bijections constructed from C49/C66 are
actual maps of the existing simultaneous quotient carriers.
For a specific pair x:i, y:j their graph holds exactly when the
original tagged points are E-related.

The maps are equivariant for the REAL current group B.G and the
already constructed simultaneous E-quotient actions. This is a
proved property of local canonical E-class maps, not a section of
the automorphism group of an independent quotient.

It is a source prerequisite for transporting quotient orbital
colours/RAW words when choosing one parent per occupancy class.
It does NOT yet claim arbitrary selected-sort RAW exact descent.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers

noncomputable section

/-- The canonical local E-class transport has exactly the REAL
global E relation as its graph on genuine current points. -/
theorem originalSupportedClassMap_mk_iff
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (i j : B.Sorts)
    (hSup : (originalExactOccupancySetoid
      A B P base hOne E).r i j)
    (x : B.Point i) (y : B.Point j) :
    originalSupportedClassMap A B P transport base hOne E
        i j hSup (Quotient.mk'' x) = Quotient.mk'' y ↔
      (currentOriginalExactSetoid A B P base hOne E).r
        (⟨i,x⟩ : Sigma B.Point) (⟨j,y⟩ : Sigma B.Point) := by
  constructor
  · intro h
    have hh := congrArg
      (selectedOriginalClassToGlobal A B P transport base hOne E j) h
    rw [originalSupportedClassMap_global] at hh
    change (Quotient.mk'' (⟨i,x⟩ : Sigma B.Point) :
      Quotient (currentOriginalExactSetoid A B P base hOne E)) =
      Quotient.mk'' (⟨j,y⟩ : Sigma B.Point) at hh
    exact Quotient.exact hh
  · intro h
    apply selectedOriginalClassToGlobal_injective
      A B P transport base hOne E j
    calc
      selectedOriginalClassToGlobal A B P transport base hOne E j
          (originalSupportedClassMap A B P transport
            base hOne E i j hSup (Quotient.mk'' x)) =
        selectedOriginalClassToGlobal A B P transport
          base hOne E i (Quotient.mk'' x) :=
        originalSupportedClassMap_global
          A B P transport base hOne E i j hSup _
      _ = selectedOriginalClassToGlobal A B P transport
          base hOne E j (Quotient.mk'' y) := by
        change (Quotient.mk'' (⟨i,x⟩ : Sigma B.Point) :
          Quotient (currentOriginalExactSetoid A B P base hOne E)) =
          Quotient.mk'' (⟨j,y⟩ : Sigma B.Point)
        exact Quotient.sound h

/-- For any legal E-support proof on one actual type, its
canonical class map is precisely the identity, including old
equality and nontrivial local E-classes. -/
theorem originalSupportedClassMap_self
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (i : B.Sorts)
    (hii : (originalExactOccupancySetoid
      A B P base hOne E).r i i)
    (x : OriginalSelectedClass A B P transport base hOne E i) :
    originalSupportedClassMap
      A B P transport base hOne E i i hii x = x := by
  apply selectedOriginalClassToGlobal_injective
    A B P transport base hOne E i
  exact originalSupportedClassMap_global
    A B P transport base hOne E i i hii x

/-- The SAME actual quotient B.G action commutes with canonical
E-class maps on any two E-supported current names. -/
theorem originalSupportedClassMap_equivariant
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (i j : B.Sorts)
    (hSup : (originalExactOccupancySetoid
      A B P base hOne E).r i j)
    (g : B.G)
    (q : OriginalSelectedClass A B P transport base hOne E i) :
    letI : ∀ k : B.Sorts, MulAction B.G
        (OriginalSelectedClass A B P transport base hOne E k) :=
      CCO.SimultaneousQuotients.action B.source B.homogeneous
        (originalExactCurrentKernelFamily A B P transport base hOne E)
        (originalExactCurrentKernelWords A B P transport base hOne E)
        (originalExactCurrentKernelWords_relation
          A B P transport base hOne E)
    originalSupportedClassMap A B P transport base hOne E i j hSup
        (g • q) =
      g • originalSupportedClassMap
        A B P transport base hOne E i j hSup q := by
  dsimp only
  letI : ∀ k : B.Sorts, MulAction B.G
      (OriginalSelectedClass A B P transport base hOne E k) :=
    CCO.SimultaneousQuotients.action B.source B.homogeneous
      (originalExactCurrentKernelFamily A B P transport base hOne E)
      (originalExactCurrentKernelWords A B P transport base hOne E)
      (originalExactCurrentKernelWords_relation A B P transport base hOne E)
  induction q using Quotient.inductionOn with
  | _ x =>
    obtain ⟨y,hxy⟩ :=
      (originalExactClass_occupies_supported_type
        A B P base hOne E i j x).mp hSup
    have hMap :
        originalSupportedClassMap A B P transport
          base hOne E i j hSup (Quotient.mk'' x) =
          (Quotient.mk'' y :
            OriginalSelectedClass A B P transport base hOne E j) :=
      (originalSupportedClassMap_mk_iff
        A B P transport base hOne E i j hSup x y).mpr hxy
    have hMoved : (currentOriginalExactSetoid A B P base hOne E).r
        (⟨i,g • x⟩ : Sigma B.Point)
        (⟨j,g • y⟩ : Sigma B.Point) :=
      (originalExactGlobalRelation_prefix_invariant
        A B P base hOne E) g x y hxy
    have hMapMoved :
        originalSupportedClassMap A B P transport
          base hOne E i j hSup (Quotient.mk'' (g • x)) =
          (Quotient.mk'' (g • y) :
            OriginalSelectedClass A B P transport base hOne E j) :=
      (originalSupportedClassMap_mk_iff
        A B P transport base hOne E i j hSup (g • x) (g • y)).mpr hMoved
    calc
      originalSupportedClassMap A B P transport
          base hOne E i j hSup
            (g • (Quotient.mk'' x :
              OriginalSelectedClass A B P transport base hOne E i)) =
        originalSupportedClassMap A B P transport
          base hOne E i j hSup (Quotient.mk'' (g • x)) := rfl
      _ = (Quotient.mk'' (g • y) :
          OriginalSelectedClass A B P transport base hOne E j) := hMapMoved
      _ = g • (Quotient.mk'' y :
          OriginalSelectedClass A B P transport base hOne E j) := rfl
      _ = g • originalSupportedClassMap
          A B P transport base hOne E i j hSup (Quotient.mk'' x) :=
        congrArg (fun z => g • z) hMap.symm

end
end CCO.ExactEPGeometry
