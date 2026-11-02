import CCO.TransitionClosure.TypedFreshAtomMotion
import CCO.TerminalLattice.StrongPaletteBridge
import CCO.TerminalLattice.OriginalModularity

/-!
# B049 source07 C06–C08: two ORIGINAL nonzero equivalences' RAW join

The OLD equality-inclusive RAW composite J;K is an invariant
same-sort equivalence. This file proves that on ACTUAL distinct old
endpoints its diversity restriction equals the genuine two-letter
STRONG menu product J° star K°. A RAW middle point equal to x or y
is replaced by an actual fresh ORIGINAL J- or K-class point while
fixing the other endpoint and its old fine atomic colour.

All finite SAP bases are complete and omit the point moved.
No equality atom is inserted into the STRONG product. This needs
original homogeneous SAP but neither CCO, FULL cover, NR2, exact
domains, quotient SAP nor a mixed-sort commuting rule.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ k : ι, MulAction G (X k)]

open ParityHasse.Original
open CCO.TerminalLattice

/-- SOURCE07 TSC2: the actual DIVERSITY restriction of equality-
inclusive J;K equals genuine J° star K° on one original sort,
with BOTH J,K strictly larger than logical identity. -/
theorem original_raw_equiv_equiv_guard_eq_strong
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι}
    (J K : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    (hK : (⊥ : ColourEq S i) < K) :
    S.diversityGuard (RawSymmetric.compose J.val.r K.val.r) =
      S.product (originalEquivDiversityPalette S J)
        (originalEquivDiversityPalette S K) := by
  classical
  let JD : S.Menu i i := originalEquivDiversityPalette S J
  let KD : S.Menu i i := originalEquivDiversityPalette S K
  apply Set.Subset.antisymm
  · rintro c ⟨x,y,⟨z,hJxz,hKzy⟩,hxy⟩
    have hxyNe : x ≠ y := by
      intro h
      exact S.atomRel_ne hxy (congrArg (Sigma.mk i) h)
    have hMiddle :
        ∃ z' : X i, z' ≠ x ∧ z' ≠ y ∧ J x z' ∧ K z' y := by
      by_cases hzx : z = x
      · subst z
        obtain ⟨z',hAvoid,hJnew,hFine⟩ :=
          original_fresh_typed_atom_left_in_equiv S H sap
            J hJ c x y hxy
            ({(⟨i,x⟩ : Sigma X), ⟨i,y⟩} : Finset (Sigma X))
        have hzX : z' ≠ x := by
          intro heq
          exact hAvoid (by simp [heq])
        have hzY : z' ≠ y := by
          intro heq
          exact hAvoid (by simp [heq])
        have hKy : K z' y :=
          (K.property x y z' y (hxy.trans hFine.symm)).mp hKzy
        exact ⟨z',hzX,hzY,hJnew,hKy⟩
      · by_cases hzy : z = y
        · subst z
          obtain ⟨z',hAvoid,hKnew,hFine⟩ :=
            original_fresh_typed_atom_right_in_equiv S H sap
              K hK c x y hxy
              ({(⟨i,x⟩ : Sigma X), ⟨i,y⟩} : Finset (Sigma X))
          have hzX : z' ≠ x := by
            intro heq
            exact hAvoid (by simp [heq])
          have hzY : z' ≠ y := by
            intro heq
            exact hAvoid (by simp [heq])
          have hJnew : J x z' :=
            (J.property x y x z' (hxy.trans hFine.symm)).mp hJxz
          exact ⟨z',hzX,hzY,hJnew,K.val.symm hKnew⟩
        · exact ⟨z,hzx,hzy,hJxz,hKzy⟩
    obtain ⟨z',hzX,hzY,hJnew,hKnew⟩ := hMiddle
    have hXzTag : (⟨i,x⟩ : Sigma X) ≠ ⟨i,z'⟩ := by
      intro h
      have hEq : x = z' := by
        simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using h
      exact hzX hEq.symm
    have hZyTag : (⟨i,z'⟩ : Sigma X) ≠ ⟨i,y⟩ := by
      intro h
      exact hzY (by
        simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using h)
    obtain ⟨a,hXz⟩ := S.some_colour_of_ne x z' hXzTag
    obtain ⟨b,hZy⟩ := S.some_colour_of_ne z' y hZyTag
    have hJD : a ∈ JD := ⟨x,z',hJnew,hXz⟩
    have hKD : b ∈ KD := ⟨z',y,hKnew,hZy⟩
    exact ⟨a,hJD,b,hKD,⟨x,z',y,hXz,hZy,hxy⟩⟩
  · intro c hc
    obtain ⟨a,hJD,b,hKD,⟨x,z,y,hXz,hZy,hxy⟩⟩ := hc
    have hJxz : J x z := by
      obtain ⟨u,v,hJuv,hUV⟩ := hJD
      exact (J.property u v x z (hUV.trans hXz.symm)).mp hJuv
    have hKzy : K z y := by
      obtain ⟨u,v,hKuv,hUV⟩ := hKD
      exact (K.property u v z y (hUV.trans hZy.symm)).mp hKuv
    exact ⟨x,y,⟨z,hJxz,hKzy⟩,hxy⟩

/-- The SAME diversity formula equals the OLD FULL invariant
equivalence JOIN's diversity palette, because in an original
homogeneous symmetric source J;K is literally its represented
RAW equivalence join. No distributivity or exactness is assumed. -/
theorem original_raw_equiv_join_guard_eq_strong
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι}
    (J K : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    (hK : (⊥ : ColourEq S i) < K) :
    originalEquivDiversityPalette S (ColourEq.join S H J K) =
      S.product (originalEquivDiversityPalette S J)
        (originalEquivDiversityPalette S K) := by
  have hRaw :
      (ColourEq.join S H J K).val.r =
        RawSymmetric.compose J.val.r K.val.r := by
    funext x y
    apply propext
    exact ParityHasse.Original.sup_relation_iff S H J K x y
  change S.diversityGuard ((ColourEq.join S H J K).val.r) =
    S.product (originalEquivDiversityPalette S J)
      (originalEquivDiversityPalette S K)
  rw [hRaw]
  exact original_raw_equiv_equiv_guard_eq_strong
    S H sap J K hJ hK

end CCO.TransitionClosure
