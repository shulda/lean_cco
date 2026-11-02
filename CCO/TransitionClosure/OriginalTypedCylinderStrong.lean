import CCO.TransitionClosure.OriginalTypedCylinderSpectrum

/-!
# B049 source07 C41-C42: all FOUR actual STRONG typed cylinder cases

For any real old typed fine atom a and original quotients J,K,
the full class-pair representative spectrum was proved to be
the diversity guard of the literal original RAW J;{a};K.

When a real ORIGINAL exterior equivalence is Id, its RAW step
is actual equality. The corresponding STRONG diversity factor
must be OMITTED, NEVER interpreted as the empty palette or as
a fabricated equality-labelled STRONG edge.

Together with the original old AgeSAP typed saturation theorems,
this produces the exact genuine STRONG spectrum in all four
nonzero/identity cases, including different source/target sorts.
No quotient SAP/CCO, NR2, unknown identity atom or mixed-sort
commutation is used.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.TerminalLattice

/-- Literally OMIT the right exterior when K is original
equality on its true old target sort. This is RAW setoid
equality, not an empty STRONG diversity palette. -/
theorem originalRawTypedSandwich_bot_right
    {i j : ι} (J : ColourEq S i) (a : S.Atom i j) :
    originalRawTypedSandwich S J (⊥ : ColourEq S j) a =
      originalRawTypedLeftExterior S J a := by
  funext x y
  apply propext
  constructor
  · rintro ⟨u,v,hJ,hA,hZero⟩
    change v = y at hZero
    subst v
    exact ⟨u,hJ,hA⟩
  · rintro ⟨u,hJ,hA⟩
    exact ⟨u,y,hJ,hA,rfl⟩

/-- Literally OMIT the left exterior when J is original
equality on its true old source sort. -/
theorem originalRawTypedSandwich_bot_left
    {i j : ι} (K : ColourEq S j) (a : S.Atom i j) :
    originalRawTypedSandwich S (⊥ : ColourEq S i) K a =
      originalRawTypedRightExterior S K a := by
  funext x y
  apply propext
  constructor
  · rintro ⟨u,v,hZero,hA,hK⟩
    change x = u at hZero
    subst u
    exact ⟨v,hA,hK⟩
  · rintro ⟨v,hA,hK⟩
    exact ⟨x,v,rfl,hA,hK⟩

/-- When BOTH exteriors are actual original equality,
the RAW sandwich is the old atomic relation itself.
In particular it never creates a diversity identity atom. -/
theorem originalRawTypedSandwich_bot_both
    {i j : ι} (a : S.Atom i j) :
    originalRawTypedSandwich S
      (⊥ : ColourEq S i) (⊥ : ColourEq S j) a =
        S.atomRel a := by
  rw [originalRawTypedSandwich_bot_left S (⊥ : ColourEq S j) a]
  funext x y
  apply propext
  constructor
  · rintro ⟨v,hA,hZero⟩
    change v = y at hZero
    subst v
    exact hA
  · intro hA
    exact ⟨y,hA,rfl⟩

/-- SOURCE07 C42 both nonzero original exteriors:
the ACTUAL full original quotient pair spectrum is the
genuine J°*{a}*K° typed STRONG product. -/
theorem originalTypedCylinder_both_nonzero
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (J : ColourEq S i) (K : ColourEq S j)
    (hJ : (⊥ : ColourEq S i) < J)
    (hK : (⊥ : ColourEq S j) < K)
    (a : S.Atom i j) (x : X i) (y : X j)
    (hxy : S.atomRel a x y) :
    originalTypedQuotientPairSpectrum S J K
      (Quotient.mk J.val x) (Quotient.mk K.val y) =
        S.product (originalEquivDiversityPalette S J)
          (S.product ({a} : S.Menu i j)
            (originalEquivDiversityPalette S K)) := by
  rw [originalTypedQuotientPairSpectrum_eq_raw S H J K a x y hxy]
  exact original_raw_typed_J_atom_K_guard_eq_strong
    S H sap J K hJ hK a

/-- SOURCE07 C42 nonzero LEFT but IDENTITY RIGHT:
only the original left STRONG exterior is present. -/
theorem originalTypedCylinder_left_nonzero
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (J : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    (a : S.Atom i j) (x : X i) (y : X j)
    (hxy : S.atomRel a x y) :
    originalTypedQuotientPairSpectrum S J (⊥ : ColourEq S j)
      (Quotient.mk J.val x) (Quotient.mk (⊥ : ColourEq S j).val y) =
        S.product (originalEquivDiversityPalette S J)
          ({a} : S.Menu i j) := by
  rw [originalTypedQuotientPairSpectrum_eq_raw
    S H J (⊥ : ColourEq S j) a x y hxy,
    originalRawTypedSandwich_bot_right]
  exact original_raw_typed_left_exterior_guard_eq_strong S H sap J hJ a

/-- SOURCE07 C42 IDENTITY LEFT but nonzero RIGHT:
only the original right STRONG exterior is present. -/
theorem originalTypedCylinder_right_nonzero
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (K : ColourEq S j)
    (hK : (⊥ : ColourEq S j) < K)
    (a : S.Atom i j) (x : X i) (y : X j)
    (hxy : S.atomRel a x y) :
    originalTypedQuotientPairSpectrum S (⊥ : ColourEq S i) K
      (Quotient.mk (⊥ : ColourEq S i).val x) (Quotient.mk K.val y) =
        S.product ({a} : S.Menu i j)
          (originalEquivDiversityPalette S K) := by
  rw [originalTypedQuotientPairSpectrum_eq_raw
    S H (⊥ : ColourEq S i) K a x y hxy,
    originalRawTypedSandwich_bot_left]
  exact original_raw_typed_right_exterior_guard_eq_strong S H sap K hK a

/-- SOURCE07 C42 IDENTITY on both original coordinates:
the old fine spectrum is exactly the old atom singleton.
No old/hiddden equality is ever a STRONG diversity factor. -/
theorem originalTypedCylinder_both_identity
    (H : HomogeneousSource S G)
    {i j : ι} (a : S.Atom i j)
    (x : X i) (y : X j) (hxy : S.atomRel a x y) :
    originalTypedQuotientPairSpectrum S
      (⊥ : ColourEq S i) (⊥ : ColourEq S j)
      (Quotient.mk (⊥ : ColourEq S i).val x)
      (Quotient.mk (⊥ : ColourEq S j).val y) =
        ({a} : S.Menu i j) := by
  rw [originalTypedQuotientPairSpectrum_eq_raw
    S H (⊥ : ColourEq S i) (⊥ : ColourEq S j) a x y hxy,
    originalRawTypedSandwich_bot_both]
  exact original_raw_typed_no_exterior_guard_eq_atom S a

end CCO.TransitionClosure
