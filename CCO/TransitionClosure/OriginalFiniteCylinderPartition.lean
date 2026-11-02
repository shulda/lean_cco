import CCO.TransitionClosure.OriginalNamedHiddenCoordinates

/-!
# B049 source07 C41-C48: finite ACTUAL old typed cylinder names and partition

For every actual pair of old quotient-equivalence kernels J,K on named
original sorts, an OLD fine atom a determines the real diversity
cylinder (J;{a};K)°. The literal old finite atomic palette gives only
finitely many DISTINCT cylinder names, even if the actual quotient
carriers are infinite.

Source two-point homogeneity proves that different such cylinder
palettes have DISJOINT fine old atoms. Every real old fine atom
belongs to exactly one name. The full representative spectrum of
every ACTUAL class pair having distinct representatives is ONE of
these names; the corresponding semantic-cylinder relations partition
such class pairs. In particular this applies to the actual named
hidden quotient coordinates of the previous module, and to the
original equality coordinate where a distinct old pair exists.

The omitted diagonal of the SAME hidden coordinate is still
handled by unary equality, not a fabricated STRONG binary atom.
There is no quotient SAP/CCO, guessed admissibility of arbitrary
hidden pair diagrams or new quotient-reduct automorphism action.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original

/-- One actual OLD typed representative-cylinder name. Its
exteriors are FULL original RAW equivalences; the diversity
guard removes only real equality, and an identity exterior
is omitted from the STRONG realization by the earlier TSC. -/
def originalTypedCylinderName
    {i j : ι} (J : ColourEq S i) (K : ColourEq S j)
    (a : S.Atom i j) : S.Menu i j :=
  S.diversityGuard (originalRawTypedSandwich S J K a)

/-- The FINITE family of all distinct actual old typed
representative-cylinder names; syntactically different fine
atoms may give the SAME name. -/
def originalTypedCylinderNames
    {i j : ι} (J : ColourEq S i) (K : ColourEq S j) :
    Set (S.Menu i j) :=
  Set.range (originalTypedCylinderName S J K)

theorem originalTypedCylinderNames_finite
    {i j : ι} (J : ColourEq S i) (K : ColourEq S j) :
    (originalTypedCylinderNames S J K).Finite := by
  letI : Finite (S.Atom i j) := S.finiteAtom i j
  exact Set.finite_range _

/-- Every realized fine old atom belongs to the cylinder it
generates. The true old RAW outside factors may be equality;
this is NOT a positive STRONG identity step. -/
theorem originalTypedCylinderName_contains_atom
    {i j : ι} (J : ColourEq S i) (K : ColourEq S j)
    (a : S.Atom i j) :
    a ∈ originalTypedCylinderName S J K a := by
  obtain ⟨x,y,hxy⟩ := S.realized a
  exact ⟨x,y,⟨x,y,J.val.refl x,hxy,K.val.refl y⟩,hxy⟩

/-- For every literal old J/K class pair with an old diversity
representative, its FULL representative spectrum has one of
the finite canonical old cylinder names. Original pair
homogeneity identifies the entire spectrum, not merely
its seed fine atom. -/
theorem originalTypedQuotientPairSpectrum_is_named
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i) (K : ColourEq S j)
    (q : Quotient J.val) (r : Quotient K.val)
    (h : (originalTypedQuotientPairSpectrum S J K q r).Nonempty) :
    originalTypedQuotientPairSpectrum S J K q r ∈
      originalTypedCylinderNames S J K := by
  obtain ⟨a,ha⟩ := h
  obtain ⟨x,y,hqx,hry,hxy⟩ := ha
  refine ⟨a, ?_⟩
  calc
    originalTypedCylinderName S J K a =
        originalTypedQuotientPairSpectrum S J K
          (Quotient.mk J.val x) (Quotient.mk K.val y) :=
      (originalTypedQuotientPairSpectrum_eq_raw S H J K a x y hxy).symm
    _ = originalTypedQuotientPairSpectrum S J K q r := by rw [hqx,hry]

/-- Distinct TRUE old typed cylinder names have disjoint
fine-atom menus. One common original diversity atom witnesses
two actual quotient class pairs; source two-point homogeneity
then forces equality of their WHOLE full representative spectra.
No quotient-age amalgamation is used. -/
theorem originalTypedCylinderNames_overlap_eq
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i) (K : ColourEq S j)
    (A B : S.Menu i j)
    (hA : A ∈ originalTypedCylinderNames S J K)
    (hB : B ∈ originalTypedCylinderNames S J K)
    (hOverlap : (A ∩ B).Nonempty) :
    A = B := by
  obtain ⟨a,rfl⟩ := hA
  obtain ⟨b,rfl⟩ := hB
  obtain ⟨c,hca,hcb⟩ := hOverlap
  obtain ⟨x,y,⟨u,v,hJu,hAuv,hKv⟩,hxy⟩ := hca
  obtain ⟨x',y',⟨u',v',hJu',hBuv',hKv'⟩,hxy'⟩ := hcb
  have hSpectraOverlap :
      (originalTypedQuotientPairSpectrum S J K
        (Quotient.mk J.val u) (Quotient.mk K.val v) ∩
       originalTypedQuotientPairSpectrum S J K
        (Quotient.mk J.val u') (Quotient.mk K.val v')).Nonempty := by
    refine ⟨c, ?_, ?_⟩
    · rw [originalTypedQuotientPairSpectrum_eq_raw S H J K a u v hAuv]
      exact ⟨x,y,⟨u,v,hJu,hAuv,hKv⟩,hxy⟩
    · rw [originalTypedQuotientPairSpectrum_eq_raw S H J K b u' v' hBuv']
      exact ⟨x',y',⟨u',v',hJu',hBuv',hKv'⟩,hxy'⟩
  have hFull :=
    originalTypedQuotientPairSpectrum_eq_of_overlap
      S H J K (Quotient.mk J.val u) (Quotient.mk J.val u')
        (Quotient.mk K.val v) (Quotient.mk K.val v')
          hSpectraOverlap
  calc
    originalTypedCylinderName S J K a =
        originalTypedQuotientPairSpectrum S J K
          (Quotient.mk J.val u) (Quotient.mk K.val v) :=
      (originalTypedQuotientPairSpectrum_eq_raw S H J K a u v hAuv).symm
    _ = originalTypedQuotientPairSpectrum S J K
          (Quotient.mk J.val u') (Quotient.mk K.val v') := hFull
    _ = originalTypedCylinderName S J K b :=
      originalTypedQuotientPairSpectrum_eq_raw S H J K b u' v' hBuv'

/-- Source-facing atom partition: each REAL old diversity
fine atom belongs to EXACTLY ONE of the finitely many
distinct cylinder names for the fixed J,K endpoint kernels.
The names are sets of fine atoms, not syntactic expression IDs. -/
theorem originalTypedCylinderNames_atom_unique
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i) (K : ColourEq S j)
    (c : S.Atom i j) :
    ∃! P : S.Menu i j,
      P ∈ originalTypedCylinderNames S J K ∧ c ∈ P := by
  refine ⟨originalTypedCylinderName S J K c,
    ⟨⟨c,rfl⟩, originalTypedCylinderName_contains_atom S J K c⟩, ?_⟩
  intro P hP
  exact originalTypedCylinderNames_overlap_eq S H J K P
    (originalTypedCylinderName S J K c)
      hP.1 ⟨c,rfl⟩
        ⟨c,hP.2,originalTypedCylinderName_contains_atom S J K c⟩

/-- Semantic interpretation of a true cylinder label on
ACTUAL old J/K quotient classes. The eventual binary hidden
language restricts these relations to DISTINCT coordinate
vertices, leaving same-hidden-sort diagonal to equality. -/
def originalTypedCylinderSemanticRelation
    {i j : ι} (J : ColourEq S i) (K : ColourEq S j)
    (P : S.Menu i j) :
    Quotient J.val → Quotient K.val → Prop :=
  fun q r => P = originalTypedQuotientPairSpectrum S J K q r

/-- Each ACTUAL class pair with an OLD distinct representative
has precisely one finite cylinder name. The proof covers
both proper-hidden and equality-coordinate endpoints and
does not assume that any absent diagonal has a diversity type. -/
theorem originalTypedCylinderSemanticRelation_unique
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i) (K : ColourEq S j)
    (q : Quotient J.val) (r : Quotient K.val)
    (h : (originalTypedQuotientPairSpectrum S J K q r).Nonempty) :
    ∃! P : S.Menu i j,
      P ∈ originalTypedCylinderNames S J K ∧
        originalTypedCylinderSemanticRelation S J K P q r := by
  refine ⟨originalTypedQuotientPairSpectrum S J K q r,
    ⟨originalTypedQuotientPairSpectrum_is_named S H J K q r h,rfl⟩, ?_⟩
  intro P hP
  exact hP.2

end CCO.TransitionClosure
