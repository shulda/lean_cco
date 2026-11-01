import CCO.TerminalLattice.FullCoverAperiodicity
import CCO.RawExact.QuotientSourcePalette

/-!
# B050 C17: ONE eventual quotient-walk threshold from finite OLD pair colours

The quotient G-orbital palette is finite because it is a projection of
the actual finite optional OLD fine-colour palette. This proof chooses
a representative of EVERY realized old optional pair colour (including
the genuine old diagonal) and transports the C16 all-length threshold
using original pair homogeneity. It does NOT assume finite quotient
carrier, an enlarged induced-reduct group, NR2, SAP, CCO or exactness.

The resulting N applies to ALL q,r in K/J, INCLUDING q=r. The latter
is an honest positive quotient return, not an inserted identity edge.
-/

universe u v w t
namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- C17: the SAME source G-equivariant quotient orbital has a single
uniform threshold above which its literal RAW quotient walk relation
is exactly K/J (including the quotient diagonal). The bound is
maximized over the original finite optional fine pair colours.
This is a genuine ORIGINAL-source theorem with a FULL cover and
only local exclusion of relative index two. -/
theorem originalQuotient_uniform_full_powers
    (H : HomogeneousSource S G) {i : ι}
    (J K : ColourEq S i) (hJK : J ⋖ K)
    (a b : X i) (hab : K a b) (hne : ¬ J a b)
    (hNotTwo : relativeIndex J.val K.val a ≠ 2) :
    ∃ N : Nat, 0 < N ∧
      ∀ n, N ≤ n →
        ∀ q r : Quotient J.val,
          relPow (originalQuotientOrbital S (G := G) J a b) n q r ↔
            originalUpperSetoid S J K hJK.le q r := by
  classical
  letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
  letI : Fintype (S.Atom i i) := S.finiteAtom i i
  let R := originalQuotientOrbital S (G := G) J a b
  let rep : Option (S.Atom i i) → X i × X i :=
    RawExact.QuotientPalette.colourRepresentatives S
  have hC (c : Option (S.Atom i i)) :
      S.colour (rep c).1 (rep c).2 = c :=
    RawExact.QuotientPalette.colourRepresentatives_spec S c
  have hLocal :
      ∀ c : Option (S.Atom i i),
        ∃ N : Nat, 0 < N ∧
          ∀ n, N ≤ n →
            ∀ x y : X i,
              S.colour x y = c → K x y →
                relPow R n (Quotient.mk J.val x) (Quotient.mk J.val y) := by
    intro c
    by_cases hRepK : K (rep c).1 (rep c).2
    · obtain ⟨N, hN, hWalk⟩ :=
        originalQuotient_all_large_walks S H J K hJK
          a b hab hne hNotTwo
          (Quotient.mk J.val (rep c).1)
          (Quotient.mk J.val (rep c).2)
          ((originalUpperSetoid_mk S J K hJK.le _ _).mpr hRepK)
      refine ⟨N, hN, ?_⟩
      intro n hn x y hCol _
      obtain ⟨g, hg₁, hg₂⟩ :=
        S.pair_homogeneous_of_homogeneous H
          (rep c).1 x (rep c).2 y ((hC c).trans hCol.symm)
      have hmoved :=
        relPow_group_invariant R
          (originalQuotientOrbital_invariant S H J a b)
          n g _ _ (hWalk n hn)
      change relPow R n
        (Quotient.mk J.val (g • (rep c).1))
        (Quotient.mk J.val (g • (rep c).2)) at hmoved
      simpa only [hg₁, hg₂] using hmoved
    · refine ⟨1, by omega, ?_⟩
      intro n hn x y hCol hK
      have hOld : K (rep c).1 (rep c).2 :=
        (K.property (rep c).1 (rep c).2 x y
          ((hC c).trans hCol.symm)).mpr hK
      exact False.elim (hRepK hOld)
  choose threshold hPositive hWalk using hLocal
  let bound : Nat :=
    (Finset.univ : Finset (Option (S.Atom i i))).sup threshold
  let N : Nat := max 1 bound
  have hN : 0 < N := by simp [N]
  refine ⟨N, hN, ?_⟩
  intro n hn q r
  constructor
  · intro hp
    exact originalQuotientConnected_le_upper
      S H J K hJK.le a b hab q r ⟨n, hp⟩
  · intro hupper
    induction q using Quotient.inductionOn with
    | _ x =>
      induction r using Quotient.inductionOn with
      | _ y =>
        have hK : K x y :=
          (originalUpperSetoid_mk S J K hJK.le x y).mp hupper
        have hMax : threshold (S.colour x y) ≤ bound :=
          Finset.le_sup (Finset.mem_univ _)
        have hLe : threshold (S.colour x y) ≤ n :=
          hMax.trans ((le_max_right _ _).trans hn)
        exact hWalk (S.colour x y) n hLe x y rfl hK

end CCO.TerminalLattice
