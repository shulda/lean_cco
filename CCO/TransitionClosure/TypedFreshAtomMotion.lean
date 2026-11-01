import CCO.TerminalLattice.FibreSAP
import CCO.StabilizerSAP
import CCO.SAPPoint
import Mathlib.Data.Finset.Basic

/-!
# B049 source07 C01–C05: typed original SAP endpoint duplication

The RAW/STRONG saturation formula for J;t;K has genuinely typed
original endpoints i,j. Its OLD middle diversity atom can therefore
connect DIFFERENT original sorts. We cannot silently reuse the
same-sort B050 endpoint-motion lemma or enlarge the acting group.

This lemma uses the ORIGINAL homogeneous group on the full dependent
sum, plus actual OLD finite-age SAP, to duplicate one ORIGINAL
typed diversity edge's left endpoint within a NONZERO original
invariant J-class, fixing its right endpoint exactly. The new point
avoids ANY finite collection of tagged old points of arbitrary sorts.

No semantic CCO, quotient SAP, identity atom, mixed-sort commutation,
countability axiom or hypothetical fresh-class provider is used.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ k : ι, MulAction G (X k)]

open ParityHasse.Original
open CCO.TerminalLattice

/-- Given a REAL OLD typed atomic diversity edge u--a--v from
sort i to sort j, every actual nonzero invariant J on sort i
allows us to move u inside its own J-class outside any specified
finite set of tagged old points, while preserving the exact OLD
atom a to the same fixed right endpoint v.

The fixed base is the COMPLETE induced set {anchor,v}; it does not
contain the point being moved. J-class freshness is itself proved
from actual ORIGINAL AgeSAP (B050), not assumed for a quotient. -/
theorem original_fresh_typed_atom_left_in_equiv
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι}
    (J : ColourEq S i) (hJ : (⊥ : ColourEq S i) < J)
    (a : S.Atom i j) (u : X i) (v : X j)
    (huv : S.atomRel a u v)
    (forbidden : Finset (Sigma X)) :
    ∃ u' : X i,
      (⟨i,u'⟩ : Sigma X) ∉ forbidden ∧
      J u u' ∧ S.atomRel a u' v := by
  classical
  obtain ⟨anchor,hAvoid,hClass⟩ :=
    freshFibre_of_original_SAP S H sap J hJ
      (Quotient.mk J.val u) ({u} : Finset (X i))
  have hAnchorNe : anchor ≠ u := by
    intro h
    exact hAvoid (by simp [h])
  have hJua : J u anchor :=
    J.val.symm (Quotient.exact hClass)
  let pA : Sigma X := ⟨i,anchor⟩
  let pV : Sigma X := ⟨j,v⟩
  let pU : Sigma X := ⟨i,u⟩
  let base : FiniteInduced (X := X) :=
    FiniteInduced.ofFinset ({pA,pV} : Finset (Sigma X))
  have hAin : pA ∈ base.vertices := by
    simp [base,FiniteInduced.ofFinset]
  have hVin : pV ∈ base.vertices := by
    simp [base,FiniteInduced.ofFinset]
  have hUnot : pU ∉ base.vertices := by
    intro h
    have hPair : pU = pA ∨ pU = pV := by
      simpa [base,FiniteInduced.ofFinset] using h
    rcases hPair with hEq | hEq
    · have hu : u = anchor := by
        simpa only [pU,pA,Sigma.mk.injEq,heq_eq_eq,true_and] using hEq
      exact hAnchorNe hu.symm
    · exact S.atomRel_ne huv hEq
  have hFinite : (↑forbidden : Set (Sigma X)).Finite :=
    forbidden.finite_toSet
  obtain ⟨outTag,hOrbit,hNotForbidden⟩ :=
    RealAction.orbit_has_fresh_point_of_SAP
      S H sap base pU hUnot (↑forbidden : Set (Sigma X)) hFinite
  obtain ⟨g,hgFix,hgU⟩ := hOrbit
  have hSort : outTag.1 = i := by
    calc
      outTag.1 = (g • pU).1 := congrArg Sigma.fst hgU.symm
      _ = i := by simp only [pU,Sigma.smul_mk]
  obtain ⟨u',huTag⟩ := tagged_exists_of_sort (X := X) outTag i hSort
  have hFixA : g • pA = pA :=
    (RealAction.mem_pointwiseStabilizer base.vertices g).mp
      hgFix pA hAin
  have hFixV : g • pV = pV :=
    (RealAction.mem_pointwiseStabilizer base.vertices g).mp
      hgFix pV hVin
  have hga : g • anchor = anchor := by
    simpa only [pA,Sigma.smul_mk,Sigma.mk.injEq,
      heq_eq_eq,true_and] using hFixA
  have hgv : g • v = v := by
    simpa only [pV,Sigma.smul_mk,Sigma.mk.injEq,
      heq_eq_eq,true_and] using hFixV
  have hgu : g • u = u' := by
    rw [huTag] at hgU
    simpa only [pU,Sigma.smul_mk,Sigma.mk.injEq,
      heq_eq_eq,true_and] using hgU
  have hJnewAnchor : J u' anchor := by
    have hMove :=
      colourInvariant_groupInvariant S H J.2 g u anchor hJua
    simpa only [hgu,hga] using hMove
  have hJnew : J u u' :=
    J.val.trans hJua (J.val.symm hJnewAnchor)
  have hAtom : S.atomRel a u' v := by
    have hMove := S.colourInvariant_of_homogeneous H g u v
    change S.colour u' v = some a
    simpa only [hgu,hgv] using hMove.trans huv
  refine ⟨u',?_,hJnew,hAtom⟩
  simpa only [huTag, Finset.mem_coe] using hNotForbidden

/-- The right-endpoint counterpart is obtained by ACTUALLY reversing
the OLD typed fine atom and invoking the proved left-endpoint motion
in the genuine target sort. Mixed-sort direction is reversed only via
the source's typed converse and never by same-sort commutation. -/
theorem original_fresh_typed_atom_right_in_equiv
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i j : ι}
    (K : ColourEq S j) (hK : (⊥ : ColourEq S j) < K)
    (a : S.Atom i j) (u : X i) (v : X j)
    (huv : S.atomRel a u v)
    (forbidden : Finset (Sigma X)) :
    ∃ v' : X j,
      (⟨j,v'⟩ : Sigma X) ∉ forbidden ∧
      K v v' ∧ S.atomRel a u v' := by
  have hReverse : S.atomRel (S.conv a) v u :=
    (S.colour_swap u v a).mp huv
  obtain ⟨v',hAvoid,hClass,hReverseAtom⟩ :=
    original_fresh_typed_atom_left_in_equiv
      S H sap K hK (S.conv a) v u hReverse forbidden
  have hForward : S.atomRel a u v' := by
    have hSwap := (S.colour_swap v' u (S.conv a)).mp hReverseAtom
    simpa only [S.conv_invol] using hSwap
  exact ⟨v',hAvoid,hClass,hForward⟩

end CCO.TransitionClosure
