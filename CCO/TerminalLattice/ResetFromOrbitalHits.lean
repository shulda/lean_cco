import CCO.TerminalLattice.QuotientSquareOrbitalClosure
import CCO.TerminalLattice.ResetSquareRAW
import CCO.TerminalLattice.OldAbsorption

/-!
# B050 C37–C39: SOURCE reset assembled from real external-orbital hits

This is a precise receiving theorem for the still-open global old CCO
sparse-graph step C31–C35. If one COMPLETE external quotient orbital
has a literal OLD STRONG square meeting EVERY complete external OLD
quotient orbital inside a FULL original upper equivalence K, then the
square is exactly K^circ; both the J^circ diagonal slice and full
external layers are separately justified by already proved theorems.

The only conditional input is the honest mathematical OUTPUT of C35:
every external complete J-quotient orbital is met by the original
square. It is NOT an assumed reset, not an imported B049 conclusion,
not an arbitrary quotient groupoid, and not a CCO assumption. The
source C40 still requires constructing those hits with ONE original
homomorphic CCO completion and the sparse labelled private paths.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- A complete external old quotient orbital inside K is a subset
of the genuine OLD fine-atom K-diversity palette, not a fine subset
assumption. All original orbitals are those of the ambient G. -/
theorem original_full_external_orbital_inside_K
    (H : HomogeneousSource S G) {i : ι}
    (J K : ColourEq S i) (hJK : J ≤ K)
    (p q : X i) (hpq : K p q) :
    originalQuotientOrbitalPalette S (G := G) J p q ⊆
      originalEquivDiversityPalette S K := by
  intro c hc
  obtain ⟨x,y,⟨hxne,hOrb⟩,hCol⟩ := hc
  have hKclasses :=
    originalQuotientOrbital_le_upper S H J K hJK p q hpq
      (Quotient.mk J.val x) (Quotient.mk J.val y) hOrb
  have hKxy :=
    (originalUpperSetoid_mk S J K hJK x y).mp hKclasses
  exact ⟨x,y,hKxy,hCol⟩

/-- An old K-diversity fine atom either lies in OLD J^circ or, using
its ACTUAL represented pair x,y, belongs to the full original-G
external quotient orbital through that pair. The latter is exactly
the identity motion in the old G, not a new orbital existence axiom. -/
theorem original_Kdiv_in_J_or_external_orbital
    {i : ι} (J K : ColourEq S i)
    (c : S.Atom i i)
    (hc : c ∈ originalEquivDiversityPalette S K) :
    c ∈ originalEquivDiversityPalette S J ∨
      ∃ x y : X i, K x y ∧ ¬ J x y ∧
        c ∈ originalQuotientOrbitalPalette S (G := G) J x y := by
  obtain ⟨x,y,hKxy,hCol⟩ := hc
  by_cases hJxy : J x y
  · exact Or.inl ⟨x,y,hJxy,hCol⟩
  · have hxne : x ≠ y := by
      intro h
      exact S.atomRel_ne hCol (congrArg (Sigma.mk i) h)
    exact Or.inr ⟨x,y,hKxy,hJxy,
      x,y,⟨hxne,originalQuotientOrbital_root S (G := G) J x y⟩,hCol⟩

/-- C37/C38 source assembly, CONDITIONAL on C35's actual full list
of hits: if the OLD square W meets every COMPLETE external quotient
orbital in K, then W=K^circ. The proof uses proved J^circ containment
and old-G/J-bisaturated orbital closure; nothing about the desired
square equality is assumed. -/
theorem original_complete_reset_square_of_all_external_hits
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (J K : ColourEq S i) (hJK : J ≤ K)
    (hJ : (⊥ : ColourEq S i) < J)
    (p q : X i) (hpq : K p q)
    (hHits : ∀ x y : X i, K x y → ¬ J x y →
      (S.product
        (originalQuotientOrbitalPalette S (G := G) J p q)
        (originalQuotientOrbitalPalette S (G := G) J p q)
        ∩ originalQuotientOrbitalPalette S (G := G) J x y).Nonempty) :
    S.product
      (originalQuotientOrbitalPalette S (G := G) J p q)
      (originalQuotientOrbitalPalette S (G := G) J p q) =
        originalEquivDiversityPalette S K := by
  let T := originalQuotientOrbitalPalette S (G := G) J p q
  let W := S.product T T
  let KD := originalEquivDiversityPalette S K
  have hInside : T ⊆ KD :=
    original_full_external_orbital_inside_K S H J K hJK p q hpq
  have hWinside : W ⊆ KD := by
    intro c hc
    obtain ⟨a,ha,b,hb,x,y,z,hxy,hyz,hxz⟩ := hc
    obtain ⟨u,v,hKuv,hcolA⟩ := hInside ha
    obtain ⟨w₀,w₁,hKw,hcolB⟩ := hInside hb
    have hKxy : K x y :=
      (K.property u v x y (hcolA.trans hxy.symm)).mp hKuv
    have hKyz : K y z :=
      (K.property w₀ w₁ y z (hcolB.trans hyz.symm)).mp hKw
    exact ⟨x,z,K.val.trans hKxy hKyz,hxz⟩
  apply Set.Subset.antisymm hWinside
  intro c hc
  rcases original_Kdiv_in_J_or_external_orbital S (G := G) J K c hc with hCj | ⟨x,y,hKxy,hNotJ,hCtarget⟩
  · exact original_complete_quotient_orbital_square_contains_Jdiv
      S H sap J hJ p q hCj
  · exact (original_complete_square_meeting_orbital_contains_it
      S H sap J hJ p q x y (hHits x y hKxy hNotJ)) hCtarget

/-- C39 actual OLD RAW reset obtained without a hidden RAW premise.
The argument first constructs the literal STRONG square K^circ from
the C35 hit input, then uses proved seriality of the original-G
complete quotient orbital and original symmetric old-loop colours
to add the GENUINE old logical identity to its RAW square.

No CCO or global NR2 is used inside this final algebraic step. -/
theorem original_complete_reset_strong_and_RAW_of_all_hits
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (J K : ColourEq S i) (hJK : J ≤ K)
    (hJ : (⊥ : ColourEq S i) < J)
    (p q : X i) (hpq : K p q) (hExternal : ¬ J p q)
    (hHits : ∀ x y : X i, K x y → ¬ J x y →
      (S.product
        (originalQuotientOrbitalPalette S (G := G) J p q)
        (originalQuotientOrbitalPalette S (G := G) J p q)
        ∩ originalQuotientOrbitalPalette S (G := G) J x y).Nonempty) :
    (S.product
      (originalQuotientOrbitalPalette S (G := G) J p q)
      (originalQuotientOrbitalPalette S (G := G) J p q) =
        originalEquivDiversityPalette S K) ∧
    (RawSymmetric.compose
      (S.menuRel (originalQuotientOrbitalPalette S (G := G) J p q))
      (S.menuRel (originalQuotientOrbitalPalette S (G := G) J p q)) =
        K.val.r) := by
  have hSquare :=
    original_complete_reset_square_of_all_external_hits
      S H sap J K hJK hJ p q hpq hHits
  have hInside :=
    original_full_external_orbital_inside_K S H J K hJK p q hpq
  exact ⟨hSquare,
    original_complete_external_RAW_square_of_STRONG
      S H J K p q hExternal hInside hSquare⟩

end CCO.TerminalLattice
