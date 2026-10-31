import CCO.TerminalLattice.FullCoverIndexTwo
import CCO.TerminalLattice.StrongPaletteBridge
import Mathlib.Algebra.Ring.Parity

/-!
# B050 C15: original relative index two gives alternating STRONG powers

There is no fabricated equality atom. On each actual original K/J
component the complete non-diagonal OLD G-orbital is the unique edge
between its two true quotient vertices. Its literal quotient square
is equality; this gives odd/original-orbital and positive-even/true
quotient-diagonal powers. The already-proved source SAP fresh-fibre
lemma lifts the latter to the nonempty OLD J-diversity palette.
-/

universe u v w t

namespace CCO.TerminalLattice

open ParityHasse.Original

/-- For a relation whose genuine square is equality, every further
two steps leave its RAW endpoint relation unchanged. -/
theorem relPow_two_periodic_of_square {A : Type u}
    (R : A → A → Prop) (hSquare : relPow R 2 = Eq) :
    ∀ n : Nat, relPow R (n+2) = relPow R n := by
  intro n
  rw [relPow_add R n 2, hSquare]
  funext x y
  apply propext
  constructor
  · rintro ⟨z, hxz, hzy⟩
    subst z
    exact hxz
  · intro hxy
    exact ⟨y, hxy, rfl⟩

/-- Odd and strictly positive even RAW quotient powers have exactly
the expected two alternating relations. Neither exponent 0 nor an
artificial positive equality edge appears. -/
theorem relPow_alternating_of_square {A : Type u}
    (R : A → A → Prop) (hSquare : relPow R 2 = Eq) :
    ∀ k : Nat, relPow R (2*k+1) = R ∧
      relPow R (2*k+2) = Eq := by
  intro k
  induction k with
  | zero =>
      constructor
      · funext x y
        exact propext (relPow_one R x y)
      · simpa using hSquare
  | succ k ih =>
      constructor
      · have hIndex : 2*(k+1)+1 = (2*k+1)+2 := by omega
        rw [hIndex, relPow_two_periodic_of_square R hSquare (2*k+1)]
        exact ih.1
      · have hIndex : 2*(k+1)+2 = (2*k+2)+2 := by omega
        rw [hIndex, relPow_two_periodic_of_square R hSquare (2*k+2)]
        exact ih.2

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- C15 (actual quotient graph). In a FULL original index-two cover
one complete external quotient orbital squares to the TRUE quotient
identity relation. Its two edges necessarily have the same endpoint
quotient class. This is not an old STRONG identity. -/
theorem originalQuotient_index_two_square
    (H : HomogeneousSource S G) {i : ι}
    (J K : ColourEq S i) (hJK : J ⋖ K)
    (a b : X i) (hab : K a b) (hne : ¬ J a b)
    (htwo : relativeIndex J.val K.val a = 2) :
    relPow (originalQuotientOrbital S (G := G) J a b) 2 = Eq := by
  let R := originalQuotientOrbital S (G := G) J a b
  have hExternal (q r : Quotient J.val) :
      R q r ↔ originalUpperSetoid S J K hJK.le q r ∧ q ≠ r := by
    change originalQuotientOrbital S (G := G) J a b q r ↔ _
    rw [originalQuotientOrbital_index_two_external S H J K hJK a b hab hne htwo]
  have hUnique (p q r : Quotient J.val)
      (hpq : R p q) (hpr : R p r) : q = r := by
    induction p using Quotient.inductionOn with
    | _ y =>
      induction q using Quotient.inductionOn with
      | _ x =>
        induction r using Quotient.inductionOn with
        | _ z =>
          obtain ⟨hYx, hNeYx⟩ := (hExternal _ _).mp hpq
          obtain ⟨hYz, hNeYz⟩ := (hExternal _ _).mp hpr
          have hKyX : K y x := (originalUpperSetoid_mk S J K hJK.le y x).mp hYx
          have hKyZ : K y z := (originalUpperSetoid_mk S J K hJK.le y z).mp hYz
          have hNotYx : ¬ J y x := by
            intro h
            exact hNeYx (Quotient.sound h)
          have hNotYz : ¬ J y z := by
            intro h
            exact hNeYz (Quotient.sound h)
          have hIndexY : relativeIndex J.val K.val y = 2 :=
            (relativeIndex_uniform S H J K y a).trans htwo
          exact Quotient.sound
            (original_index_two_unique_external
              S H J K hJK.le y hIndexY
                x hKyX hNotYx z hKyZ hNotYz)
  funext q r
  apply propext
  constructor
  · rintro ⟨m, hqm, hmr⟩
    have hmq : R m q :=
      originalQuotientOrbital_symmetric S H J a b q m hqm
    exact hUnique m q r hmq ((relPow_one R m r).mp hmr)
  · intro hqr
    subst r
    obtain ⟨m, hqm⟩ := originalQuotientOrbital_serial S H J a b q
    refine ⟨m, hqm, ?_⟩
    exact (relPow_one R m q).mpr
      (originalQuotientOrbital_symmetric S H J a b q m hqm)

/-- For literal original source STRONG atom menus, equality of represented
real relations detects equality of the underlying menus. -/
private theorem originalMenu_ext_of_rel {i : ι}
    (A B : S.Menu i i) (h : S.menuRel A = S.menuRel B) : A = B := by
  calc
    A = S.diversityGuard (S.menuRel A) :=
      (S.diversityGuard_menuRel A).symm
    _ = S.diversityGuard (S.menuRel B) := by rw [h]
    _ = B := S.diversityGuard_menuRel B

/-- C15: EVERY ODD positive exponent has precisely the actual complete
external OLD quotient-orbital STRONG atom palette. The integer k encodes
exponent 2k+1, not a zero-length STRONG identity. -/
theorem original_index_two_odd_strong_palette
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (J K : ColourEq S i) (hJK : J ⋖ K)
    (hJ : (⊥ : ColourEq S i) < J)
    (a b : X i) (hab : K a b) (hne : ¬ J a b)
    (htwo : relativeIndex J.val K.val a = 2)
    (k : Nat) :
    originalStrongPalettePower S
        (originalQuotientOrbitalPalette S (G := G) J a b) (2*k) =
      originalQuotientOrbitalPalette S (G := G) J a b := by
  let R := originalQuotientOrbital S (G := G) J a b
  let T := originalQuotientOrbitalPalette S (G := G) J a b
  have hSq := originalQuotient_index_two_square S H J K hJK a b hab hne htwo
  have hOdd : relPow R (2*k+1) = R :=
    (relPow_alternating_of_square R hSq k).1
  apply originalMenu_ext_of_rel S
  calc
    S.menuRel (originalStrongPalettePower S T (2*k)) =
        strongDiversityPower (S.menuRel T) (2*k) :=
      menuRel_originalStrongPalettePower S H T (2*k)
    _ = strongDiversityPower (quotientDiversity J.val R) (2*k) := by
      rw [originalQuotientOrbitalPalette_semantics S H J a b]
    _ = quotientDiversity J.val (relPow R (2*k+1)) :=
      original_quotient_strongPower S H sap J hJ R (2*k)
    _ = quotientDiversity J.val R := by rw [hOdd]
    _ = S.menuRel T :=
      (originalQuotientOrbitalPalette_semantics S H J a b).symm

/-- C15: EVERY POSITIVE EVEN exponent is the true original OLD
J-diversity palette, NOT OLD identity. The quotient diagonal pulled
back to distinct actual J-real points is nonempty because J>Id. -/
theorem original_index_two_even_strong_palette
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (J K : ColourEq S i) (hJK : J ⋖ K)
    (hJ : (⊥ : ColourEq S i) < J)
    (a b : X i) (hab : K a b) (hne : ¬ J a b)
    (htwo : relativeIndex J.val K.val a = 2)
    (k : Nat) :
    originalStrongPalettePower S
        (originalQuotientOrbitalPalette S (G := G) J a b) (2*k+1) =
      originalEquivDiversityPalette S J := by
  let R := originalQuotientOrbital S (G := G) J a b
  let T := originalQuotientOrbitalPalette S (G := G) J a b
  have hSq := originalQuotient_index_two_square S H J K hJK a b hab hne htwo
  have hEven : relPow R (2*k+2) = Eq :=
    (relPow_alternating_of_square R hSq k).2
  apply originalMenu_ext_of_rel S
  calc
    S.menuRel (originalStrongPalettePower S T (2*k+1)) =
        strongDiversityPower (S.menuRel T) (2*k+1) :=
      menuRel_originalStrongPalettePower S H T (2*k+1)
    _ = strongDiversityPower (quotientDiversity J.val R) (2*k+1) := by
      rw [originalQuotientOrbitalPalette_semantics S H J a b]
    _ = quotientDiversity J.val (relPow R (2*k+2)) :=
      original_quotient_strongPower S H sap J hJ R (2*k+1)
    _ = quotientDiversity J.val Eq := by rw [hEven]
    _ = (fun x y : X i => x ≠ y ∧ J x y) :=
      quotientDiversity_diagonal J.val
    _ = S.menuRel (originalEquivDiversityPalette S J) :=
      (originalEquivDiversityPalette_semantics S J).symm

end CCO.TerminalLattice
