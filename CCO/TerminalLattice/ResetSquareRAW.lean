import CCO.TerminalLattice.CompleteOrbitalWord
import CCO.TerminalLattice.StrongPaletteBridge

/-!
# B050 C39: genuine old RAW square recovered from an OLD STRONG reset square

This is the final algebraic firewall of the source's reset theorem.
A full old diversity menu T has a STRONG square K^circ, and if T has
a real neighbour at every endpoint, the equality-inclusive RAW square
is exactly the full original invariant equivalence K (including OLD
logical equality).

The helper makes the square and seriality assumptions EXPLICIT, not
automatically discharged; in the source consumer, T is one COMPLETE
external original-G quotient orbital, and its seriality is PROVED
here from ORIGINAL sort transitivity alone.
No CCO, NR2, exact-domain product oracle or synthetic STRONG unit.
-/

universe u v w t
namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- Original same-sort menu symmetry as a literal real-pair relation;
the witness old fine colour is preserved by the source's loop
converse law, without an axiom of quotient symmetry. -/
theorem original_menuRel_symmetric {i : ι}
    (T : S.Menu i i) :
    ∀ x y : X i, S.menuRel T x y → S.menuRel T y x := by
  intro x y
  rintro ⟨c, hc, hxy⟩
  refine ⟨c, hc, ?_⟩
  change S.colour y x = some c
  simpa only [S.symmetricLoop] using (S.colour_swap x y c).mp hxy

/-- C39 algebraic step: if the OLD STRONG square equals K^circ
and the input menu T lies inside K^circ and is serial, then its
equality-inclusive RAW square is the ENTIRE old equivalence K.
This proof does not assume that T is a complete orbital; that
source instance is provided by the following two theorems. -/
theorem original_RAW_square_of_STRONG_square
    (H : HomogeneousSource S G) {i : ι}
    (K : ColourEq S i) (T : S.Menu i i)
    (hInside : T ⊆ originalEquivDiversityPalette S K)
    (hSerial : ∀ x : X i, ∃ y, S.menuRel T x y)
    (hSquare : S.product T T = originalEquivDiversityPalette S K) :
    RawSymmetric.compose (S.menuRel T) (S.menuRel T) = K.val.r := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y,hxy,hyz⟩
    have hKxy : K x y := by
      obtain ⟨c,hc,hcol⟩ := hxy
      have h : S.menuRel (originalEquivDiversityPalette S K) x y :=
        ⟨c, hInside hc, hcol⟩
      rw [originalEquivDiversityPalette_semantics S K] at h
      exact h.2
    have hKyz : K y z := by
      obtain ⟨c,hc,hcol⟩ := hyz
      have h : S.menuRel (originalEquivDiversityPalette S K) y z :=
        ⟨c, hInside hc, hcol⟩
      rw [originalEquivDiversityPalette_semantics S K] at h
      exact h.2
    exact K.val.trans hKxy hKyz
  · intro hKxz
    by_cases hxz : x = z
    · subst z
      obtain ⟨y,hxy⟩ := hSerial x
      exact ⟨y, hxy, original_menuRel_symmetric S T x y hxy⟩
    · have hMenu : S.menuRel (S.product T T) x z := by
        rw [hSquare, originalEquivDiversityPalette_semantics S K]
        exact ⟨hxz, hKxz⟩
      rw [menuRel_product_eq_strongCompose S H T T] at hMenu
      obtain ⟨_,y,_,_,hxy,hyz⟩ := hMenu
      exact ⟨y,hxy,hyz⟩

/-- A COMPLETE external quotient orbital has a real old neighbour
at every old endpoint, without SAP or quotient homogeneity.
The same ORIGINAL group transitivity that acts on all named sorts
moves the pinned old root of its quotient orbital to x. -/
theorem original_complete_external_orbital_serial
    (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i) (p q : X i)
    (hExternal : ¬ J p q) :
    ∀ x : X i,
      ∃ y : X i,
        S.menuRel (originalQuotientOrbitalPalette S (G := G) J p q) x y := by
  intro x
  obtain ⟨g,hgx⟩ := S.original_sort_transitive_of_homogeneous H i p x
  let y : X i := g • q
  have hpqNe : p ≠ q := by
    intro h
    exact hExternal (h ▸ J.val.refl p)
  have hxy : x ≠ y := by
    intro h
    have hAct : g • p = g • q := by
      simpa only [hgx, y] using h
    exact hpqNe (MulAction.injective g hAct)
  have hOrbit : originalQuotientOrbital S (G := G) J p q
      (Quotient.mk J.val x) (Quotient.mk J.val y) := by
    refine ⟨g, ?_, rfl⟩
    simpa only [hgx]
  refine ⟨y, ?_⟩
  rw [originalQuotientOrbitalPalette_semantics S H J p q]
  exact ⟨hxy,hOrbit⟩

/-- The SOURCE C39 RAW consequence, with the genuine complete
old-group external orbital's seriality now discharged.
The only remaining conclusion premise is the ACTUAL STRONG reset
square, supplied by the later sparse global CCO construction.
No independent RAW reset premise is inserted. -/
theorem original_complete_external_RAW_square_of_STRONG
    (H : HomogeneousSource S G) {i : ι}
    (J K : ColourEq S i) (p q : X i)
    (hExternal : ¬ J p q)
    (hInside :
      originalQuotientOrbitalPalette S (G := G) J p q ⊆
        originalEquivDiversityPalette S K)
    (hStrongSquare :
      S.product
        (originalQuotientOrbitalPalette S (G := G) J p q)
        (originalQuotientOrbitalPalette S (G := G) J p q) =
          originalEquivDiversityPalette S K) :
    RawSymmetric.compose
      (S.menuRel (originalQuotientOrbitalPalette S (G := G) J p q))
      (S.menuRel (originalQuotientOrbitalPalette S (G := G) J p q)) =
        K.val.r :=
  original_RAW_square_of_STRONG_square S H K
    (originalQuotientOrbitalPalette S (G := G) J p q)
    hInside
    (original_complete_external_orbital_serial S H J p q hExternal)
    hStrongSquare

end CCO.TerminalLattice
