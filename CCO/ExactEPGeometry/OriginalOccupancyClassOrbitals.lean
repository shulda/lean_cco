import CCO.ExactEPGeometry.OriginalOccupancyClassEquivariance

/-!
# B062 C83: coherent quotient-copy maps preserve ALL actual orbitals

The original single-E quotient-class maps between occupied unary names
are bijective and equivariant for the SAME genuine B.G action on the
all-parent simultaneous exact quotient. Hence they preserve and reflect
the FULL relational orbitals of every real point pair, including the
actual quotient diagonal. This is the precise pair-colour compatibility
needed to retype RAW words when selecting one parent per occupancy.

The statement is an equivalence of genuine B.G orbital relations,
not an unproved claim that full RAW exactness is inherited by arbitrary
sort deletion, not an automorphism-group section, and not quotient SAP.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers

noncomputable section

/-- ACTUAL B.G orbitals are invariant under the canonical
E-class identifications at both displayed endpoint sorts, in BOTH
directions. The reverse uses the already proved real injectivity
of these equivalences rather than postulating a quotient section. -/
theorem originalSupportedClassMap_orbital_iff
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (i j k l : B.Sorts)
    (hik : (originalExactOccupancySetoid A B P base hOne E).r i k)
    (hjl : (originalExactOccupancySetoid A B P base hOne E).r j l)
    (x x' : OriginalSelectedClass A B P transport base hOne E i)
    (y y' : OriginalSelectedClass A B P transport base hOne E j) :
    letI : ∀ s : B.Sorts, MulAction B.G
        (OriginalSelectedClass A B P transport base hOne E s) :=
      CCO.SimultaneousQuotients.action B.source B.homogeneous
        (originalExactCurrentKernelFamily A B P transport base hOne E)
        (originalExactCurrentKernelWords A B P transport base hOne E)
        (originalExactCurrentKernelWords_relation
          A B P transport base hOne E)
    GroupActions.orbital (G := B.G) x y x' y' ↔
      GroupActions.orbital (G := B.G)
        (originalSupportedClassMap A B P transport base hOne E i k hik x)
        (originalSupportedClassMap A B P transport base hOne E j l hjl y)
        (originalSupportedClassMap A B P transport base hOne E i k hik x')
        (originalSupportedClassMap A B P transport base hOne E j l hjl y') := by
  letI : ∀ s : B.Sorts, MulAction B.G
      (OriginalSelectedClass A B P transport base hOne E s) :=
    CCO.SimultaneousQuotients.action B.source B.homogeneous
      (originalExactCurrentKernelFamily A B P transport base hOne E)
      (originalExactCurrentKernelWords A B P transport base hOne E)
      (originalExactCurrentKernelWords_relation A B P transport base hOne E)
  let Fi := originalSupportedClassMap A B P transport base hOne E i k hik
  let Fj := originalSupportedClassMap A B P transport base hOne E j l hjl
  have hFi : ∀ (g : B.G) (z : OriginalSelectedClass
      A B P transport base hOne E i), Fi (g • z) = g • Fi z :=
    fun g z => originalSupportedClassMap_equivariant
      A B P transport base hOne E i k hik g z
  have hFj : ∀ (g : B.G) (z : OriginalSelectedClass
      A B P transport base hOne E j), Fj (g • z) = g • Fj z :=
    fun g z => originalSupportedClassMap_equivariant
      A B P transport base hOne E j l hjl g z
  have hIi := originalSupportedClassMap_injective
    A B P transport base hOne E i k hik
  have hIj := originalSupportedClassMap_injective
    A B P transport base hOne E j l hjl
  constructor
  · rintro ⟨g,hgx,hgy⟩
    refine ⟨g,?_,?_⟩
    · calc
        g • Fi x = Fi (g • x) := (hFi g x).symm
        _ = Fi x' := congrArg Fi hgx
    · calc
        g • Fj y = Fj (g • y) := (hFj g y).symm
        _ = Fj y' := congrArg Fj hgy
  · rintro ⟨g,hgx,hgy⟩
    refine ⟨g,?_,?_⟩
    · apply hIi
      calc
        Fi (g • x) = g • Fi x := hFi g x
        _ = Fi x' := hgx
    · apply hIj
      calc
        Fj (g • y) = g • Fj y := hFj g y
        _ = Fj y' := hgy

end
end CCO.ExactEPGeometry
