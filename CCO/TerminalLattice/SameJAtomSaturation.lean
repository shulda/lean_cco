import CCO.TerminalLattice.SameJFibreMotion
import CCO.TerminalLattice.StrongPaletteBridge

/-!
# B050 C21: NARROW same-J saturation of one OLD fine atom

The RAW relation J;t;J is equality-inclusive at the two external
J-steps, whereas the STRONG product has genuine diversity edges.
We prove the exact endpoint-diversity equality without importing B049
or assuming a unit law for arbitrary OLD fine palettes.

The only substantive step is to duplicate BOTH possible collapsed
intermediate OLD real vertices, using the previously proved complete
stabilizer SAP orbit helper with a fresh original J-anchor.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- Genuine three-edge RAW J;t;J condition, permitting equality at
the two J sides but not at the middle fine diversity edge. -/
def originalRawJSandwich {i : ι}
    (J : ColourEq S i) (tAtom : S.Atom i i) : X i → X i → Prop :=
  fun x z => ∃ u v : X i, J x u ∧ S.atomRel tAtom u v ∧ J v z

/-- SOURCE C21: for an ORIGINAL nontrivial invariant J, the true
diversity slice of the equality-inclusive old RAW J;t;J sandwich
equals the literal OLD STRONG atom-menu product
J^circ star {t} star J^circ.

This is a narrow internal proof under old homogeneous AgeSAP. It does
not use quotient-cover hypotheses, CCO, NR2, exactness, a B049 oracle,
or any synthetic STRONG identity. -/
theorem original_raw_J_atom_J_guard_eq_strong
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (J : ColourEq S i) (hJ : (⊥ : ColourEq S i) < J)
    (tAtom : S.Atom i i) :
    S.diversityGuard (originalRawJSandwich S J tAtom) =
      S.product (originalEquivDiversityPalette S J)
        (S.product ({tAtom} : S.Menu i i)
          (originalEquivDiversityPalette S J)) := by
  classical
  let D : S.Menu i i := originalEquivDiversityPalette S J
  apply Set.Subset.antisymm
  · rintro c ⟨x,z,⟨u,v,hJxu,hUV,hJvz⟩,hxz⟩
    have hxzne : x ≠ z := by
      intro heq
      exact S.atomRel_ne hxz (congrArg (Sigma.mk i) heq)
    obtain ⟨u', huAvoid, hJuu', hu'v⟩ :=
      original_fresh_atom_endpoint_in_J S H sap J hJ tAtom
        u v hUV ({x,z,v} : Finset (X i))
    have hvu' : S.atomRel tAtom v u' := by
      simpa only [S.symmetricLoop] using (S.colour_swap u' v tAtom).mp hu'v
    obtain ⟨v', hvAvoid, hJvv', hv'u'⟩ :=
      original_fresh_atom_endpoint_in_J S H sap J hJ tAtom
        v u' hvu' ({x,z,u'} : Finset (X i))
    have hu'v' : S.atomRel tAtom u' v' := by
      simpa only [S.symmetricLoop] using (S.colour_swap v' u' tAtom).mp hv'u'
    have hxu'Ne : x ≠ u' := by
      intro h
      exact huAvoid (by simp [h])
    have hu'zNe : u' ≠ z := by
      intro h
      exact huAvoid (by simp [h])
    have hu'v'Ne : u' ≠ v' := by
      intro h
      exact hvAvoid (by simp [h])
    have hv'zNe : v' ≠ z := by
      intro h
      exact hvAvoid (by simp [h])
    have hJxu' : J x u' := J.val.trans hJxu hJuu'
    have hJv'z : J v' z := J.val.trans (J.val.symm hJvv') hJvz
    have hStrong :
        strongCompose (S.menuRel D)
          (strongCompose (S.menuRel ({tAtom} : S.Menu i i))
            (S.menuRel D)) x z := by
      refine ⟨hxzne, u', hxu'Ne, hu'zNe, ?_, ?_⟩
      · rw [show D = originalEquivDiversityPalette S J from rfl,
          originalEquivDiversityPalette_semantics S J]
        exact ⟨hxu'Ne, hJxu'⟩
      · refine ⟨hu'zNe, v', hu'v'Ne, hv'zNe, ?_, ?_⟩
        · exact ⟨tAtom, by simp, hu'v'⟩
        · rw [show D = originalEquivDiversityPalette S J from rfl,
            originalEquivDiversityPalette_semantics S J]
          exact ⟨hv'zNe, hJv'z⟩
    have hMenu :
        S.menuRel (S.product D
          (S.product ({tAtom} : S.Menu i i) D)) x z := by
      rw [menuRel_product_eq_strongCompose S H D
        (S.product ({tAtom} : S.Menu i i) D),
        menuRel_product_eq_strongCompose S H ({tAtom} : S.Menu i i) D]
      exact hStrong
    obtain ⟨d, hd, hdxz⟩ := hMenu
    have heq : d = c := Option.some.inj (hdxz.symm.trans hxz)
    exact heq ▸ hd
  · intro c hc
    obtain ⟨x,z,hxz⟩ := S.realized c
    have hMenu :
        S.menuRel (S.product D
          (S.product ({tAtom} : S.Menu i i) D)) x z :=
      ⟨c, hc, hxz⟩
    rw [menuRel_product_eq_strongCompose S H D
      (S.product ({tAtom} : S.Menu i i) D),
      menuRel_product_eq_strongCompose S H ({tAtom} : S.Menu i i) D] at hMenu
    obtain ⟨_,u,_,_,hJstep,hSecond⟩ := hMenu
    obtain ⟨_,v,_,_,hAtom,hJlast⟩ := hSecond
    have hJxu : J x u := by
      rw [show D = originalEquivDiversityPalette S J from rfl,
          originalEquivDiversityPalette_semantics S J] at hJstep
      exact hJstep.2
    have hJvz : J v z := by
      rw [show D = originalEquivDiversityPalette S J from rfl,
          originalEquivDiversityPalette_semantics S J] at hJlast
      exact hJlast.2
    obtain ⟨a,ha,huv⟩ := hAtom
    have haEq : a = tAtom := by
      simpa only [Set.mem_singleton_iff] using ha
    subst a
    exact ⟨x,z,⟨u,v,hJxu,huv,hJvz⟩,hxz⟩

end CCO.TerminalLattice
