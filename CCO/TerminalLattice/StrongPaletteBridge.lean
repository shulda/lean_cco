import CCO.TerminalLattice.FullCoverStrongRelation
import CCO.RawStrongBridge
import CCO.StrongGeometry

/-!
# B050 C18: EXACT original old fine-atom STRONG palette powers

For a complete OLD original-G quotient orbital, the literal menu of
OLD diversity atoms is the diversity guard of the full real quotient
pullback, not an arbitrary fine subrelation. The same-sort original
three-vertex palette product `AtomicSource.product` is represented
EXACTLY by real `strongCompose`; pair homogeneity, not a new
colour-table product axiom, discharges the only semantic transport.

Therefore C17 uniform quotient relation powers + original SAP
freshness prove the source's true STRONG palette power result
`T^{star n} = K^circ`, including all old J-diversity atoms and
excluding true OLD identity. No CCO, global NR2, exactness, mixed-sort
commutation or quotient homogeneity is used.
-/

universe u v w t
namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- Source-tight same-sort bridge: genuine three-point STRONG atom
triangles are exactly the actual three-distinct-real-point compositions,
with the endpoints pinned via OLD pair homogeneity. Does not rely on
SAP, CCO, quotient actions or exact-product calculus. -/
theorem menuRel_product_eq_strongCompose
    (H : HomogeneousSource S G) {i : ι}
    (A B : S.Menu i i) :
    S.menuRel (S.product A B) =
      strongCompose (S.menuRel A) (S.menuRel B) := by
  funext x z
  apply propext
  constructor
  · rintro ⟨c, ⟨a, ha, b, hb, u, v, w, huv, hvw, huw⟩, hxz⟩
    obtain ⟨g, hgu, hgw⟩ :=
      (S.pair_homogeneous_of_homogeneous H) u x w z
        (huw.trans hxz.symm)
    have hxzNe : x ≠ z := by
      intro h
      exact S.atomRel_ne hxz (congrArg (Sigma.mk i) h)
    have hxy : S.colour x (g • v) = some a := by
      have h := S.colourInvariant_of_homogeneous H g u v
      rw [hgu] at h
      exact h.trans huv
    have hyz : S.colour (g • v) z = some b := by
      have h := S.colourInvariant_of_homogeneous H g v w
      rw [hgw] at h
      exact h.trans hvw
    have hxNe : x ≠ g • v := by
      intro h
      exact S.atomRel_ne hxy (congrArg (Sigma.mk i) h)
    have hzNe : g • v ≠ z := by
      intro h
      exact S.atomRel_ne hyz (congrArg (Sigma.mk i) h)
    exact ⟨hxzNe, g • v, hxNe, hzNe, ⟨a, ha, hxy⟩, ⟨b, hb, hyz⟩⟩
  · rintro ⟨hxzNe, y, _, _, ⟨a, ha, hxy⟩, ⟨b, hb, hyz⟩⟩
    have hTagged : (⟨i, x⟩ : Sigma X) ≠ ⟨i, z⟩ := by
      intro h
      have heq : x = z := by
        simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using h
      exact hxzNe heq
    obtain ⟨c, hxz⟩ := S.some_colour_of_ne x z hTagged
    exact ⟨c, ⟨a, ha, b, hb, x, y, z, hxy, hyz, hxz⟩, hxz⟩

/-- For a genuine original colour-invariant OLD diversity predicate,
its actual OLD atomic colour menu reconstructs it EXACTLY. No quotient
assumption enters, and the true diagonal is excluded rather than
renamed an STRONG identity atom. -/
theorem menuRel_diversityGuard_of_colourInvariant
    {i : ι} (R : X i → X i → Prop)
    (hColor : ColourInvariant S i R)
    (hDiv : ∀ x y, R x y → x ≠ y) :
    S.menuRel (S.diversityGuard R) = R := by
  funext x y
  apply propext
  constructor
  · rintro ⟨a, ⟨u, v, hRuv, hcuv⟩, hxy⟩
    exact (hColor u v x y (hcuv.trans hxy.symm)).mp hRuv
  · intro hR
    cases hc : S.colour x y with
    | none =>
        have heq : x = y := by
          have heq := (S.colour_none_iff x y).mp hc
          simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using heq
        exact False.elim (hDiv x y hR heq)
    | some a =>
        exact ⟨a, ⟨x, y, hR, hc⟩, hc⟩

/-- The literal source OLD diversity palette associated with a complete
external quotient orbital of the ORIGINAL G-action. -/
def originalQuotientOrbitalPalette {i : ι}
    (J : ColourEq S i) (a b : X i) : S.Menu i i :=
  S.diversityGuard (quotientDiversity J.val
    (originalQuotientOrbital S (G := G) J a b))

/-- The original G-complete quotient orbital's OLD diversity pullback
is exactly its OLD atomic menu predicate. It is not a fine subset and
the quotient diagonal is not omitted. -/
theorem originalQuotientOrbitalPalette_semantics
    (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i) (a b : X i) :
    S.menuRel (originalQuotientOrbitalPalette S (G := G) J a b) =
      quotientDiversity J.val (originalQuotientOrbital S (G := G) J a b) := by
  letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
  let R : X i → X i → Prop :=
    quotientDiversity J.val (originalQuotientOrbital S (G := G) J a b)
  have hColor : ColourInvariant S i R := by
    apply groupInvariant_colourInvariant S H
    intro g x y
    rintro ⟨hne, hOrbit⟩
    constructor
    · intro h
      exact hne (smul_left_cancel g h)
    · have hMove := originalQuotientOrbital_invariant S H J a b
        g (Quotient.mk J.val x) (Quotient.mk J.val y) hOrbit
      simpa only [originalQuotient_mk_smul S H J] using hMove
  have hDiv : ∀ x y, R x y → x ≠ y := fun x y h => h.1
  exact menuRel_diversityGuard_of_colourInvariant S R hColor hDiv

/-- The original diversity palette of an ACTUAL invariant equivalence
K; equality at old endpoints remains absent. -/
def originalEquivDiversityPalette {i : ι}
    (K : ColourEq S i) : S.Menu i i :=
  S.diversityGuard K.val.r

theorem originalEquivDiversityPalette_semantics {i : ι}
    (K : ColourEq S i) :
    S.menuRel (originalEquivDiversityPalette S K) =
      (fun x y : X i => x ≠ y ∧ K x y) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨a, ⟨u, v, hKuv, hcuv⟩, hxy⟩
    have hKxy : K x y :=
      (K.property u v x y (hcuv.trans hxy.symm)).mp hKuv
    have hne : x ≠ y := by
      intro h
      exact S.atomRel_ne hxy (congrArg (Sigma.mk i) h)
    exact ⟨hne, hKxy⟩
  · rintro ⟨hne, hK⟩
    cases hc : S.colour x y with
    | none =>
        have heq : x = y := by
          have hh := (S.colour_none_iff x y).mp hc
          simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hh
        exact False.elim (hne heq)
    | some a =>
        exact ⟨a, ⟨x, y, hK, hc⟩, hc⟩

/-- Literal positive same-sort STRONG atom-menu powers. The index n
represents exponent n+1, so ZERO is NOT an identity profile. -/
def originalStrongPalettePower {i : ι}
    (T : S.Menu i i) : Nat → S.Menu i i
  | 0 => T
  | n+1 => S.product T (originalStrongPalettePower T n)

theorem menuRel_originalStrongPalettePower
    (H : HomogeneousSource S G) {i : ι}
    (T : S.Menu i i) :
    ∀ n, S.menuRel (originalStrongPalettePower S T n) =
      strongDiversityPower (S.menuRel T) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change S.menuRel (S.product T (originalStrongPalettePower S T n)) =
        strongCompose (S.menuRel T) (strongDiversityPower (S.menuRel T) n)
      rw [menuRel_product_eq_strongCompose S H T
        (originalStrongPalettePower S T n), ih]

/-- ACTUAL C18 SOURCE STRONG PALETTE THEOREM, not merely a quotient
relation statement: in any homogeneous ORIGINAL SAP source, for
J>Id and J⋖K in the FULL original invariant lattice with local
[K:J]!=2, the complete OLD external quotient orbital's literal
STRONG powers equal ALL fine old K-diversity atoms at every large
positive exponent. No global NR2, source CCO or exactness. -/
theorem originalQuotient_uniform_strong_palette_powers
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (J K : ColourEq S i) (hJK : J ⋖ K)
    (hJ : (⊥ : ColourEq S i) < J)
    (a b : X i) (hab : K a b) (hne : ¬ J a b)
    (hNotTwo : relativeIndex J.val K.val a ≠ 2) :
    ∃ N : Nat, 0 < N ∧
      ∀ n, N ≤ n →
        originalStrongPalettePower S
          (originalQuotientOrbitalPalette S (G := G) J a b) (n-1) =
          originalEquivDiversityPalette S K := by
  obtain ⟨N, hN, hRel⟩ :=
    originalQuotient_uniform_strong_relation_powers
      S H sap J K hJK hJ a b hab hne hNotTwo
  refine ⟨N, hN, ?_⟩
  intro n hn
  let T := originalQuotientOrbitalPalette S (G := G) J a b
  let B := originalEquivDiversityPalette S K
  have hSemantic :
      S.menuRel (originalStrongPalettePower S T (n-1)) =
        S.menuRel B := by
    rw [menuRel_originalStrongPalettePower S H T,
      originalQuotientOrbitalPalette_semantics S H J a b,
      originalEquivDiversityPalette_semantics S K]
    exact hRel n hn
  calc
    originalStrongPalettePower S T (n-1) =
        S.diversityGuard (S.menuRel (originalStrongPalettePower S T (n-1))) :=
      (S.diversityGuard_menuRel _).symm
    _ = S.diversityGuard (S.menuRel B) := by rw [hSemantic]
    _ = B := S.diversityGuard_menuRel B

end CCO.TerminalLattice
