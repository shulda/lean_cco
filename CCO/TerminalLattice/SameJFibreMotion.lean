import CCO.TerminalLattice.OldAbsorption
import CCO.TerminalLattice.FibreSAP
import Mathlib.Data.Finset.Basic

/-!
# B050 C21: move one endpoint of an actual OLD atom inside its J-class

The original homogeneous/SAP source gives arbitrarily many new
representatives of a one-edge atomic orbital, while keeping its other
endpoint AND a fresh J-anchor fixed. The new endpoint therefore lies in
the SAME original J-class as the first. We do NOT assume t is
J-saturated or invoke any B049 result. This lemma is the narrow
source-strength provider for (J;t;J)^circ=J^circ*{t}*J^circ.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- B050 C21: given an OLD diversity edge u-t-v, a genuinely
nontrivial invariant J and any finite forbidden set, duplicate u
inside J[u], keeping v and the OLD atom t fixed, outside that set.

The proof uses ORIGINAL SAP on the complete two-point base
{fresh J-anchor, v}. The anchor is selected from the original J-class
by the previously PROVED infinite-fibre theorem, not postulated. -/
theorem original_fresh_atom_endpoint_in_J
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (J : ColourEq S i) (hJ : (⊥ : ColourEq S i) < J)
    (tAtom : S.Atom i i) (u v : X i)
    (huv : S.atomRel tAtom u v)
    (forbidden : Finset (X i)) :
    ∃ u' : X i,
      u' ∉ forbidden ∧ J u u' ∧ S.atomRel tAtom u' v := by
  classical
  obtain ⟨anchor, hAnchorAvoid, hAnchorClass⟩ :=
    freshFibre_of_original_SAP S H sap J hJ
      (Quotient.mk J.val u) ({u,v} : Finset (X i))
  have hAnchorU : anchor ≠ u := by
    intro heq
    exact hAnchorAvoid (by simp [heq])
  have hAnchorV : anchor ≠ v := by
    intro heq
    exact hAnchorAvoid (by simp [heq])
  have hUVne : u ≠ v := by
    intro heq
    exact S.atomRel_ne huv (congrArg (Sigma.mk i) heq)
  have hJuAnchor : J u anchor :=
    J.val.symm (Quotient.exact hAnchorClass)
  let pA : Sigma X := ⟨i, anchor⟩
  let pV : Sigma X := ⟨i, v⟩
  let pU : Sigma X := ⟨i, u⟩
  let base : FiniteInduced (X := X) :=
    FiniteInduced.ofFinset ({pA, pV} : Finset (Sigma X))
  have hAin : pA ∈ base.vertices := by
    simp [base, FiniteInduced.ofFinset]
  have hVin : pV ∈ base.vertices := by
    simp [base, FiniteInduced.ofFinset]
  have hUnot : pU ∉ base.vertices := by
    intro hu
    have hc : u = anchor ∨ u = v := by
      simpa [base, FiniteInduced.ofFinset, pA, pU, pV] using hu
    rcases hc with ha | hv
    · exact hAnchorU ha.symm
    · exact hUVne hv
  let forbiddenTag : Set (Sigma X) :=
    (fun x : X i => (⟨i,x⟩ : Sigma X)) '' (↑forbidden : Set (X i))
  have hFinite : forbiddenTag.Finite := forbidden.finite_toSet.image _
  obtain ⟨outTag, hOrbit, hNotForbidden⟩ :=
    RealAction.orbit_has_fresh_point_of_SAP S H sap base
      pU hUnot forbiddenTag hFinite
  obtain ⟨g, hgFix, hgU⟩ := hOrbit
  have hSort : outTag.1 = i := by
    calc
      outTag.1 = (g • pU).1 := congrArg Sigma.fst hgU.symm
      _ = i := by simp only [pU, Sigma.smul_mk]
  obtain ⟨u', huTag⟩ := tagged_exists_of_sort (X := X) outTag i hSort
  have hFixA : g • pA = pA :=
    (RealAction.mem_pointwiseStabilizer base.vertices g).mp
      hgFix pA hAin
  have hFixV : g • pV = pV :=
    (RealAction.mem_pointwiseStabilizer base.vertices g).mp
      hgFix pV hVin
  have hga : g • anchor = anchor := by
    simpa only [pA, Sigma.smul_mk, Sigma.mk.injEq,
      heq_eq_eq, true_and] using hFixA
  have hgv : g • v = v := by
    simpa only [pV, Sigma.smul_mk, Sigma.mk.injEq,
      heq_eq_eq, true_and] using hFixV
  have hgu : g • u = u' := by
    rw [huTag] at hgU
    simpa only [pU, Sigma.smul_mk, Sigma.mk.injEq,
      heq_eq_eq, true_and] using hgU
  have hJnewAnchor : J u' anchor := by
    have hMove :=
      colourInvariant_groupInvariant S H J.2 g u anchor hJuAnchor
    simpa only [hgu,hga] using hMove
  have hJnew : J u u' :=
    J.val.trans hJuAnchor (J.val.symm hJnewAnchor)
  have hAtom : S.atomRel tAtom u' v := by
    have hMove := S.colourInvariant_of_homogeneous H g u v
    change S.colour u' v = some tAtom
    simpa only [hgu,hgv] using hMove.trans huv
  refine ⟨u', ?_, hJnew, hAtom⟩
  intro h
  exact hNotForbidden ⟨u',h,huTag.symm⟩

end CCO.TerminalLattice
