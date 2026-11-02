import CCO.TransitionClosure.OriginalFiniteCylinderPartition
import CCO.TerminalLattice.FibreSAP

/-!
# B049 source07 C43/C49: all actual admissible hidden cylinder pairs

The finite original typed cylinder names from C41-C43 already separate
distinct full old representative spectra. To obtain the WHOLE hidden
pair partition rather than merely the conditional nonempty-spectrum
case, every actual coordinate pair must have two distinct OLD
representatives whenever at least one endpoint is a nonzero original
equivalence. This follows from actual ORIGINAL SAP infinite fibres,
not quotient SAP or a quotient homogeneity assumption.

For two old identity coordinates the only missing case is their
same-sort diagonal; genuine OLD diversity atoms partition exactly
the distinct original real pairs. The diagonal is ordinary equality.

For actual named hidden coordinates D,E the finite cylinder
semantic relations therefore form a total and disjoint pair
partition for all quotient class pairs. On the same hidden sort we
remove q=r from the BINARY diversity colours and check it by
actual hidden equality. This is NOT an equality-labelled STRONG
atom. Theorems for real-hidden and hidden-real endpoints also
retain the genuine omitted identity exterior.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.TerminalLattice

/-- For any actual pair q:a/J, r:b/K of original quotient
classes, J>Id guarantees an OLD distinct representative pair.
Even if the two current original sorts coincide and the given
representatives coincide, old SAP supplies a second real
representative inside the SAME J-class avoiding the fixed
target representative. No hidden/quotient SAP is used. -/
theorem originalTypedQuotientPairSpectrum_nonempty_of_left_nonzero
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (J : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    (K : ColourEq S j)
    (q : Quotient J.val) (r : Quotient K.val) :
    (originalTypedQuotientPairSpectrum S J K q r).Nonempty := by
  classical
  obtain ⟨y,hy⟩ := Quotient.exists_rep r
  by_cases hij : i = j
  · cases hij
    obtain ⟨x,hNot,hq⟩ :=
      (freshFibre_of_original_SAP S H sap J hJ)
        q ({y} : Finset (X i))
    have hxy : x ≠ y := by
      intro heq
      exact hNot (by simp [heq])
    have hTag : (⟨i,x⟩ : Sigma X) ≠ ⟨i,y⟩ := by
      intro heq
      exact hxy (by
        simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using heq)
    obtain ⟨a,ha⟩ := S.some_colour_of_ne x y hTag
    exact ⟨a,x,y,hq,hy,ha⟩
  · obtain ⟨x,hq⟩ := Quotient.exists_rep q
    have hTag : (⟨i,x⟩ : Sigma X) ≠ ⟨j,y⟩ := by
      intro heq
      exact hij (congrArg Sigma.fst heq)
    obtain ⟨a,ha⟩ := S.some_colour_of_ne x y hTag
    exact ⟨a,x,y,hq,hy,ha⟩

/-- Symmetric-to-left analogue with a genuine nonidentity RIGHT
original exterior. The K-fibre avoids the fixed old source
representative, maintaining the original sort and quotient class. -/
theorem originalTypedQuotientPairSpectrum_nonempty_of_right_nonzero
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι} (J : ColourEq S i)
    (K : ColourEq S j)
    (hK : (⊥ : ColourEq S j) < K)
    (q : Quotient J.val) (r : Quotient K.val) :
    (originalTypedQuotientPairSpectrum S J K q r).Nonempty := by
  classical
  obtain ⟨x,hq⟩ := Quotient.exists_rep q
  by_cases hij : i = j
  · cases hij
    obtain ⟨y,hNot,hr⟩ :=
      (freshFibre_of_original_SAP S H sap K hK)
        r ({x} : Finset (X i))
    have hxy : x ≠ y := by
      intro heq
      exact hNot (by simp [heq])
    have hTag : (⟨i,x⟩ : Sigma X) ≠ ⟨i,y⟩ := by
      intro heq
      exact hxy (by
        simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using heq)
    obtain ⟨a,ha⟩ := S.some_colour_of_ne x y hTag
    exact ⟨a,x,y,hq,hr,ha⟩
  · obtain ⟨y,hr⟩ := Quotient.exists_rep r
    have hTag : (⟨i,x⟩ : Sigma X) ≠ ⟨j,y⟩ := by
      intro heq
      exact hij (congrArg Sigma.fst heq)
    obtain ⟨a,ha⟩ := S.some_colour_of_ne x y hTag
    exact ⟨a,x,y,hq,hr,ha⟩

/-- Two actual original IDENTITY coordinates on the same sort
have a fine old diversity atom precisely whenever their real
quotient vertices are DISTINCT. No artificial equality atom. -/
theorem originalTypedQuotientPairSpectrum_nonempty_of_real_distinct
    {i : ι}
    (q r : Quotient (⊥ : ColourEq S i).val)
    (hne : q ≠ r) :
    (originalTypedQuotientPairSpectrum S
      (⊥ : ColourEq S i) (⊥ : ColourEq S i) q r).Nonempty := by
  classical
  obtain ⟨x,hqx⟩ := Quotient.exists_rep q
  obtain ⟨y,hry⟩ := Quotient.exists_rep r
  have hxy : x ≠ y := by
    intro heq
    apply hne
    calc
      q = Quotient.mk (⊥ : ColourEq S i).val x := hqx.symm
      _ = Quotient.mk (⊥ : ColourEq S i).val y := by rw [heq]
      _ = r := hry
  have hTag : (⟨i,x⟩ : Sigma X) ≠ ⟨i,y⟩ := by
    intro h
    exact hxy (by
      simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using h)
  obtain ⟨a,ha⟩ := S.some_colour_of_ne x y hTag
  exact ⟨a,x,y,hqx,hry,ha⟩

/-- FULL SOURCE C43: every pair of ACTUAL represented nonzero
hidden quotient positions has exactly one of the finite old
complete semantic-cylinder names. Existence uses visible SAP
nonzero classes; uniqueness uses old TWO-POINT homogeneity,
not hidden quotient SAP or an invented quotient orbit. -/
theorem original_named_hidden_pair_cylinder_unique
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι}
    (D : OriginalNamedHiddenCoordinate S H i)
    (E : OriginalNamedHiddenCoordinate S H j)
    (q : Quotient D.val.val) (r : Quotient E.val.val) :
    ∃! P : S.Menu i j,
      P ∈ originalTypedCylinderNames S D.val E.val ∧
      originalTypedCylinderSemanticRelation S D.val E.val P q r := by
  apply originalTypedCylinderSemanticRelation_unique S H D.val E.val q r
  exact originalTypedQuotientPairSpectrum_nonempty_of_left_nonzero
    S H sap D.val D.property.1 E.val q r

/-- Full hidden-to-real typed cylinder partition. The original
right equality exterior is omitted in STRONG syntax, not set
to the empty positive palette. -/
theorem original_hidden_real_pair_cylinder_unique
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι}
    (D : OriginalNamedHiddenCoordinate S H i)
    (q : Quotient D.val.val)
    (r : Quotient (⊥ : ColourEq S j).val) :
    ∃! P : S.Menu i j,
      P ∈ originalTypedCylinderNames S D.val (⊥ : ColourEq S j) ∧
      originalTypedCylinderSemanticRelation S D.val (⊥ : ColourEq S j) P q r := by
  apply originalTypedCylinderSemanticRelation_unique S H D.val
    (⊥ : ColourEq S j) q r
  exact originalTypedQuotientPairSpectrum_nonempty_of_left_nonzero
    S H sap D.val D.property.1 (⊥ : ColourEq S j) q r

/-- Full real-to-hidden typed cylinder partition with no fake
left STRONG equality exterior. -/
theorem original_real_hidden_pair_cylinder_unique
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι}
    (E : OriginalNamedHiddenCoordinate S H j)
    (q : Quotient (⊥ : ColourEq S i).val)
    (r : Quotient E.val.val) :
    ∃! P : S.Menu i j,
      P ∈ originalTypedCylinderNames S (⊥ : ColourEq S i) E.val ∧
      originalTypedCylinderSemanticRelation S (⊥ : ColourEq S i) E.val P q r := by
  apply originalTypedCylinderSemanticRelation_unique S H
    (⊥ : ColourEq S i) E.val q r
  exact originalTypedQuotientPairSpectrum_nonempty_of_right_nonzero
    S H sap (⊥ : ColourEq S i) E.val E.property.1 q r

/-- Ordinary real-real old diversity is partitioned off the
actual real diagonal. Original and hidden equality remain
different tests, and no STRONG positive identity is created. -/
theorem original_real_real_distinct_cylinder_unique
    (H : HomogeneousSource S G)
    {i : ι}
    (q r : Quotient (⊥ : ColourEq S i).val)
    (hne : q ≠ r) :
    ∃! P : S.Menu i i,
      P ∈ originalTypedCylinderNames S
        (⊥ : ColourEq S i) (⊥ : ColourEq S i) ∧
      originalTypedCylinderSemanticRelation S
        (⊥ : ColourEq S i) (⊥ : ColourEq S i) P q r := by
  apply originalTypedCylinderSemanticRelation_unique S H
    (⊥ : ColourEq S i) (⊥ : ColourEq S i) q r
  exact originalTypedQuotientPairSpectrum_nonempty_of_real_distinct S q r hne

/-- Hidden same-sort diagonal is checked by logical quotient
equality, never by one of the distinct-vertex cylinder colours. -/
def originalNamedHiddenOffDiagonalCylinder
    (H : HomogeneousSource S G)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (P : S.Menu i i)
    (q r : Quotient D.val.val) : Prop :=
  q ≠ r ∧ originalTypedCylinderSemanticRelation S D.val D.val P q r

theorem originalNamedHiddenOffDiagonalCylinder_diagonal_empty
    (H : HomogeneousSource S G)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (P : S.Menu i i) (q : Quotient D.val.val) :
    ¬ originalNamedHiddenOffDiagonalCylinder S H D P q q := by
  rintro ⟨h,_⟩
  exact h rfl

end CCO.TransitionClosure
