import CCO.TransitionClosure.TypedFreshAtomMotion
import CCO.TerminalLattice.StrongPaletteBridge

/-!
# B049 source07 C05: genuine OMITTED identity exteriors

The frozen TSC theorem has four cases: both exterior equivalences
nonzero, only the original left one nonzero, only the original right
one nonzero, or neither. A zero (identity) exterior is OMITTED in
the STRONG word, NEVER treated as the empty diversity palette
or a new identity atom. Both one-sided RAW relations retain true
logical equality at their optional exterior step.

All typed atom interiors remain original named sorts; all required
freshness comes from the original homogeneous AgeSAP source.
No source CCO, NR2, quotient SAP or mixed-sort commutation enters.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ k : ι, MulAction G (X k)]

open ParityHasse.Original
open CCO.TerminalLattice

/-- The equality-inclusive RAW relation J;t with NO right
equivalence exterior factor. -/
def originalRawTypedLeftExterior {i j : ι}
    (J : ColourEq S i) (a : S.Atom i j) : X i → X j → Prop :=
  fun x y => ∃ u : X i, J x u ∧ S.atomRel a u y

/-- SOURCE07 TSC with the right exterior IDENTITY: omit that
factor from the STRONG expression, and retain a genuine REAL
left diversity J-factor. -/
theorem original_raw_typed_left_exterior_guard_eq_strong
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι}
    (J : ColourEq S i) (hJ : (⊥ : ColourEq S i) < J)
    (a : S.Atom i j) :
    S.diversityGuard (originalRawTypedLeftExterior S J a) =
      S.product (originalEquivDiversityPalette S J)
        ({a} : S.Menu i j) := by
  classical
  let JD : S.Menu i i := originalEquivDiversityPalette S J
  apply Set.Subset.antisymm
  · rintro c ⟨x,y,⟨u,hJxu,hUY⟩,hXY⟩
    have hMiddle :
        ∃ u' : X i, x ≠ u' ∧ J x u' ∧ S.atomRel a u' y := by
      by_cases hux : u = x
      · subst u
        obtain ⟨u',hAvoid,hJu',hAtom⟩ :=
          original_fresh_typed_atom_left_in_equiv S H sap
            J hJ a x y hUY ({(⟨i,x⟩ : Sigma X)} : Finset (Sigma X))
        have hxne : x ≠ u' := by
          intro h
          exact hAvoid (by simp [h])
        exact ⟨u',hxne,hJu',hAtom⟩
      · exact ⟨u,(fun h => hux h.symm),hJxu,hUY⟩
    obtain ⟨u',hxne,hJxu',hAtom⟩ := hMiddle
    have hxTag : (⟨i,x⟩ : Sigma X) ≠ ⟨i,u'⟩ := by
      intro h
      exact hxne (by
        simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using h)
    obtain ⟨jAtom,hXU⟩ := S.some_colour_of_ne x u' hxTag
    have hj : jAtom ∈ JD := ⟨x,u',hJxu',hXU⟩
    exact ⟨jAtom,hj,a,by simp,⟨x,u',y,hXU,hAtom,hXY⟩⟩
  · intro c hc
    obtain ⟨jAtom,hj,a',ha',⟨x,u,y,hXU,hUY,hXY⟩⟩ := hc
    have hEq : a' = a := Set.mem_singleton_iff.mp ha'
    subst a'
    have hJxu : J x u := by
      obtain ⟨p,q,hJpq,hPQ⟩ := hj
      exact (J.property p q x u (hPQ.trans hXU.symm)).mp hJpq
    exact ⟨x,y,⟨u,hJxu,hUY⟩,hXY⟩

/-- The equality-inclusive RAW relation t;K with NO left
equivalence exterior factor. -/
def originalRawTypedRightExterior {i j : ι}
    (K : ColourEq S j) (a : S.Atom i j) : X i → X j → Prop :=
  fun x y => ∃ v : X j, S.atomRel a x v ∧ K v y

/-- SOURCE07 TSC with the left exterior IDENTITY: omit that
factor from the STRONG expression, while retaining a genuine
OLD right diversity K-factor. -/
theorem original_raw_typed_right_exterior_guard_eq_strong
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι}
    (K : ColourEq S j) (hK : (⊥ : ColourEq S j) < K)
    (a : S.Atom i j) :
    S.diversityGuard (originalRawTypedRightExterior S K a) =
      S.product ({a} : S.Menu i j)
        (originalEquivDiversityPalette S K) := by
  classical
  let KD : S.Menu j j := originalEquivDiversityPalette S K
  apply Set.Subset.antisymm
  · rintro c ⟨x,y,⟨v,hXV,hKvy⟩,hXY⟩
    have hMiddle :
        ∃ v' : X j, v' ≠ y ∧ S.atomRel a x v' ∧ K v' y := by
      by_cases hvy : v = y
      · subst v
        obtain ⟨v',hAvoid,hKnew,hAtom⟩ :=
          original_fresh_typed_atom_right_in_equiv S H sap
            K hK a x y hXV ({(⟨j,y⟩ : Sigma X)} : Finset (Sigma X))
        have hyne : v' ≠ y := by
          intro h
          exact hAvoid (by simp [h])
        exact ⟨v',hyne,hAtom,K.val.symm hKnew⟩
      · exact ⟨v,hvy,hXV,hKvy⟩
    obtain ⟨v',hvne,hAtom,hKvy'⟩ := hMiddle
    have hvTag : (⟨j,v'⟩ : Sigma X) ≠ ⟨j,y⟩ := by
      intro h
      exact hvne (by
        simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using h)
    obtain ⟨kAtom,hVY⟩ := S.some_colour_of_ne v' y hvTag
    have hk : kAtom ∈ KD := ⟨v',y,hKvy',hVY⟩
    exact ⟨a,by simp,kAtom,hk,⟨x,v',y,hAtom,hVY,hXY⟩⟩
  · intro c hc
    obtain ⟨a',ha',kAtom,hk,⟨x,v,y,hXV,hVY,hXY⟩⟩ := hc
    have hEq : a' = a := Set.mem_singleton_iff.mp ha'
    subst a'
    have hKvy : K v y := by
      obtain ⟨p,q,hKpq,hPQ⟩ := hk
      exact (K.property p q v y (hPQ.trans hVY.symm)).mp hKpq
    exact ⟨x,y,⟨v,hXV,hKvy⟩,hXY⟩

/-- With BOTH exteriors the true old identity relation, the
diversity restriction is exactly the existing OLD atom singleton.
No zero-length STRONG factor or synthetic unit is introduced. -/
theorem original_raw_typed_no_exterior_guard_eq_atom
    {i j : ι} (a : S.Atom i j) :
    S.diversityGuard (S.atomRel a) = ({a} : S.Menu i j) := by
  rw [S.atomRel_as_menu a]
  exact S.diversityGuard_menuRel ({a} : S.Menu i j)

end CCO.TransitionClosure
