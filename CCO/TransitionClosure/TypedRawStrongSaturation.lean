import CCO.TransitionClosure.TypedFreshAtomMotion
import CCO.TerminalLattice.StrongPaletteBridge

/-!
# B049 source07 C05: genuine typed RAW (J ; t ; K) vs STRONG saturation

Here J and K are actual NONZERO ORIGINAL invariant equivalences
on potentially DIFFERENT named original sorts i and j. The genuine
typed diversity atom a : Atom i j belongs to the OLD finite source.
RAW exteriors retain their logical identity, but all STRONG
factors are REAL diversity palettes, never a synthetic unit.

The forward inclusion physically duplicates collapsed intermediate
points by original visible SAP and fixed-source homogeneous group
motion, pinning the exact old output endpoint pair. The converse
glues two genuinely witnessed OLD triangles through original
two-point homogeneity on their *matching mixed-sort fine atom*.
No quotient SAP, hidden section, typed commutation, CCO, NR2,
Set-Pasch, or unproved generic product provider is involved.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ k : ι, MulAction G (X k)]

open ParityHasse.Original
open CCO.TerminalLattice

/-- The ACTUAL equality-inclusive RAW J;t;K relation at two
possibly different original sorts. The specified middle OLD
atomic edge is a genuine diversity edge; both outside steps can
be logical equality. -/
def originalRawTypedSandwich
    {i j : ι}
    (J : ColourEq S i) (K : ColourEq S j)
    (a : S.Atom i j) : X i → X j → Prop :=
  fun x y => ∃ (u : X i) (v : X j),
    J x u ∧ S.atomRel a u v ∧ K v y

/-- SOURCE07 TSC, with BOTH original exterior equivalences NONZERO.
The left side is the genuine diversity slice of RAW J;t;K,
and the right is the literal original strong menu product
J° star {t} star K°. It is not an equality-inclusive STRONG
unit law. In particular i and j need NOT be the same sort,
and the OLD output pair's fine atom is pinned throughout.

This proof has original homogeneous AgeSAP only; neither old nor
quotient semantic CCO, full cover, terminality or NR2 is used. -/
theorem original_raw_typed_J_atom_K_guard_eq_strong
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι}
    (J : ColourEq S i) (K : ColourEq S j)
    (hJ : (⊥ : ColourEq S i) < J)
    (hK : (⊥ : ColourEq S j) < K)
    (a : S.Atom i j) :
    S.diversityGuard (originalRawTypedSandwich S J K a) =
      S.product (originalEquivDiversityPalette S J)
        (S.product ({a} : S.Menu i j)
          (originalEquivDiversityPalette S K)) := by
  classical
  let JD : S.Menu i i := originalEquivDiversityPalette S J
  let KD : S.Menu j j := originalEquivDiversityPalette S K
  apply Set.Subset.antisymm
  · rintro c ⟨x,y,⟨u,v,hJxu,hUV,hKvy⟩,hxy⟩
    let forbiddenLeft : Finset (Sigma X) :=
      {⟨i,x⟩,⟨j,y⟩}
    obtain ⟨u',huAvoid,hJuu',hu'v⟩ :=
      original_fresh_typed_atom_left_in_equiv
        S H sap J hJ a u v hUV forbiddenLeft
    have hu'X : (⟨i,u'⟩ : Sigma X) ≠ ⟨i,x⟩ := by
      intro h
      exact huAvoid (by simp [forbiddenLeft,h])
    have hu'Y : (⟨i,u'⟩ : Sigma X) ≠ ⟨j,y⟩ := by
      intro h
      exact huAvoid (by simp [forbiddenLeft,h])
    let forbiddenRight : Finset (Sigma X) :=
      {⟨j,y⟩,⟨i,u'⟩}
    obtain ⟨v',hvAvoid,hKvv',hu'v'⟩ :=
      original_fresh_typed_atom_right_in_equiv
        S H sap K hK a u' v hu'v forbiddenRight
    have hv'Y : (⟨j,v'⟩ : Sigma X) ≠ ⟨j,y⟩ := by
      intro h
      exact hvAvoid (by simp [forbiddenRight,h])
    have hJxu' : J x u' := J.val.trans hJxu hJuu'
    have hKv'y : K v' y := K.val.trans (K.val.symm hKvv') hKvy
    obtain ⟨jAtom,hxuj⟩ :=
      S.some_colour_of_ne x u' hu'X.symm
    obtain ⟨kAtom,hv'y⟩ :=
      S.some_colour_of_ne v' y hv'Y
    obtain ⟨bAtom,hu'y⟩ :=
      S.some_colour_of_ne u' y hu'Y
    have hJD : jAtom ∈ JD := ⟨x,u',hJxu',hxuj⟩
    have hKD : kAtom ∈ KD := ⟨v',y,hKv'y,hv'y⟩
    exact ⟨jAtom,hJD,bAtom,
      ⟨a,by simp,kAtom,hKD,⟨u',v',y,hu'v',hv'y,hu'y⟩⟩,
      ⟨x,u',y,hxuj,hu'y,hxy⟩⟩
  · intro c hc
    obtain ⟨jAtom,hJD,bAtom,hInner,
      ⟨x,u,y,hxu,huy,hxy⟩⟩ := hc
    obtain ⟨a',ha',kAtom,hKD,
      ⟨u0,v0,y0,hu0v0,hv0y0,hu0y0⟩⟩ := hInner
    have haEq : a' = a := Set.mem_singleton_iff.mp ha'
    subst a'
    obtain ⟨g,hgu,hgy⟩ :=
      S.pair_homogeneous_of_homogeneous H u0 u y0 y
        (hu0y0.trans huy.symm)
    have hUV : S.atomRel a u (g • v0) := by
      have hMove := S.colourInvariant_of_homogeneous H g u0 v0
      change S.colour u (g • v0) = some a
      simpa only [hgu] using hMove.trans hu0v0
    have hVY : S.colour (g • v0) y = some kAtom := by
      have hMove := S.colourInvariant_of_homogeneous H g v0 y0
      simpa only [hgy] using hMove.trans hv0y0
    have hJxu : J x u := by
      obtain ⟨p,q,hJpq,hpq⟩ := hJD
      exact (J.property p q x u (hpq.trans hxu.symm)).mp hJpq
    have hKvy : K (g • v0) y := by
      obtain ⟨p,q,hKpq,hpq⟩ := hKD
      exact (K.property p q (g • v0) y
        (hpq.trans hVY.symm)).mp hKpq
    exact ⟨x,y,⟨u,g • v0,hJxu,hUV,hKvy⟩,hxy⟩

end CCO.TransitionClosure
