import CCO.TerminalLattice.StrongPaletteBridge
import CCO.TerminalLattice.FullCoverAperiodicity

/-!
# B050 C36/C38: ALL complete OLD external orbitals already square onto J-diversity

This is a stronger CCO-free reuse of the source C12 semigroup than the
source's explicit SAP duplicate-triangle construction at C38. For one
COMPLETE quotient orbital of the SAME old automorphism group, its
quotient graph is symmetric and serial. Its quotient RAW square
therefore contains the true quotient diagonal at every quotient
vertex. Since C12 proves full actual STRONG old lifting with arbitrarily
fresh representatives, the square of its FULL original fine-atom
diversity palette contains ALL nonempty OLD J-diversity, not old Id.

The proof also derives literal J-bisaturation of the OLD square:
membership of distinct old endpoints is determined solely by their
actual J-classes. There is NO reset square assumed, no use of original
CCO, FULL-cover hypothesis, NR2, synthetic STRONG identity, extra
quotient action or B049 import. Original AgeSAP is used solely via the
already proved fresh-fibre C12 provider.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- C36 exact OLD square semantics: one COMPLETE old-G quotient
orbital's literal old fine-atom STRONG square is precisely the full
diversity preimage of its ACTUAL quotient relational square. -/
theorem original_complete_quotient_orbital_square_semantics
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (J : ColourEq S i) (hJ : (⊥ : ColourEq S i) < J)
    (p q : X i) :
    S.menuRel
      (S.product
        (originalQuotientOrbitalPalette S (G := G) J p q)
        (originalQuotientOrbitalPalette S (G := G) J p q)) =
      quotientDiversity J.val
        (RawSymmetric.compose
          (originalQuotientOrbital S (G := G) J p q)
          (originalQuotientOrbital S (G := G) J p q)) := by
  let T := originalQuotientOrbitalPalette S (G := G) J p q
  let R := originalQuotientOrbital S (G := G) J p q
  calc
    S.menuRel (S.product T T) =
        strongCompose (S.menuRel T) (S.menuRel T) :=
      menuRel_product_eq_strongCompose S H T T
    _ = strongCompose (quotientDiversity J.val R)
          (quotientDiversity J.val R) := by
      rw [originalQuotientOrbitalPalette_semantics S H J p q]
    _ = quotientDiversity J.val (RawSymmetric.compose R R) :=
      quotientDiversity_strong_comp J.val
        (freshFibre_of_original_SAP S H sap J hJ) R R

/-- SOURCE C38: ALL old J-diversity fine atoms occur in the OLD
STRONG square of ANY complete original quotient orbital, even before
a global CCO reset has chosen a special orbital. The quotient
diagonal here is the genuine return q-R-r-R-q; the old endpoints are
distinct J-real points, not a fabricated old identity atom. -/
theorem original_complete_quotient_orbital_square_contains_Jdiv
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (J : ColourEq S i) (hJ : (⊥ : ColourEq S i) < J)
    (p q : X i) :
    originalEquivDiversityPalette S J ⊆
      S.product
        (originalQuotientOrbitalPalette S (G := G) J p q)
        (originalQuotientOrbitalPalette S (G := G) J p q) := by
  let R := originalQuotientOrbital S (G := G) J p q
  let T := originalQuotientOrbitalPalette S (G := G) J p q
  intro c hc
  obtain ⟨x,y,hJxy,hColour⟩ := hc
  have hXY : x ≠ y := by
    intro heq
    exact S.atomRel_ne hColour (congrArg (Sigma.mk i) heq)
  obtain ⟨v,hXV⟩ :=
    originalQuotientOrbital_serial S H J p q (Quotient.mk J.val x)
  have hVX : R v (Quotient.mk J.val x) :=
    originalQuotientOrbital_symmetric S H J p q _ _ hXV
  have hLoop : RawSymmetric.compose R R
      (Quotient.mk J.val x) (Quotient.mk J.val x) :=
    ⟨v,hXV,hVX⟩
  have hQ : Quotient.mk J.val x = Quotient.mk J.val y :=
    Quotient.sound hJxy
  have hXYwalk : RawSymmetric.compose R R
      (Quotient.mk J.val x) (Quotient.mk J.val y) := by
    rw [← hQ]
    exact hLoop
  have hMenu : S.menuRel (S.product T T) x y := by
    rw [original_complete_quotient_orbital_square_semantics
      S H sap J hJ p q]
    exact ⟨hXY,hXYwalk⟩
  obtain ⟨d,hd,hColD⟩ := hMenu
  have hDC : d = c := Option.some.inj (hColD.symm.trans hColour)
  simpa only [hDC] using hd

/-- C36 original J-bisaturation of a COMPLETE quotient orbital's
OLD square: any two genuine distinct real endpoint pairs with the
same old J-quotient endpoints have the same literal original
STRONG-square membership. This is conditional only on original SAP
and J>Id, NOT on the future reset square. -/
theorem original_complete_quotient_orbital_square_J_bisaturated
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (J : ColourEq S i) (hJ : (⊥ : ColourEq S i) < J)
    (p q : X i)
    (x y x' y' : X i)
    (hX'Y' : x' ≠ y')
    (hJXX' : J x x') (hJYY' : J y y')
    (hXY :
      S.menuRel
        (S.product
          (originalQuotientOrbitalPalette S (G := G) J p q)
          (originalQuotientOrbitalPalette S (G := G) J p q)) x y) :
    S.menuRel
      (S.product
        (originalQuotientOrbitalPalette S (G := G) J p q)
        (originalQuotientOrbitalPalette S (G := G) J p q)) x' y' := by
  rw [original_complete_quotient_orbital_square_semantics
    S H sap J hJ p q] at hXY ⊢
  refine ⟨hX'Y', ?_⟩
  have hXQ : Quotient.mk J.val x = Quotient.mk J.val x' :=
    Quotient.sound hJXX'
  have hYQ : Quotient.mk J.val y = Quotient.mk J.val y' :=
    Quotient.sound hJYY'
  rw [← hXQ, ← hYQ]
  exact hXY.2

end CCO.TerminalLattice
