import CCO.UnaryFreshFrames.SAPAvoidance

/-! Full-automorphism algebraicity and the source hereditary unary criterion.
The direct group H.Aut is used here: no arbitrary subgroup orbit is inferred
from SAP. The criterion quantifies over EVERY finite hidden parameter set. -/
universe u v
namespace CCO.UnaryFreshFrames.Structure
variable {L : Language.{u}} {V : Type v} (H : Structure L V)

theorem full_fixer_closure_eq (A : Set V) :
    fixer H.Aut (H.closure A) = fixer H.Aut A := by
  ext g
  constructor
  · intro hg x hx
    exact hg x (H.subset_closure A hx)
  · intro hg
    exact H.closure_fixed g hg

theorem full_orbitOver_closure_eq (A : Set V) (x : V) :
    orbitOver H.Aut (H.closure A) x = orbitOver H.Aut A x := by
  unfold orbitOver
  rw [H.full_fixer_closure_eq]

theorem closure_subset_full_dcl (A : Set V) : H.closure A ⊆ Dcl H.Aut A := by
  intro x hx g
  exact H.closure_fixed g.val g.property x hx

theorem full_acl_eq_closure (hfin : H.LocallyFinite)
    (hInf : H.InfiniteClosedOrbits H.Aut) {A : Set V} (hA : A.Finite) :
    Acl H.Aut A = H.closure A := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hnot
    have hi := hInf (H.closure A) (hfin A hA) (H.closure_closed A) x hnot
    rw [H.full_orbitOver_closure_eq] at hi
    exact hi hx
  · exact (H.closure_subset_full_dcl A).trans (dcl_subset_acl H.Aut A)

theorem full_dcl_eq_closure (hfin : H.LocallyFinite)
    (hInf : H.InfiniteClosedOrbits H.Aut) {A : Set V} (hA : A.Finite) :
    Dcl H.Aut A = H.closure A := by
  apply Set.Subset.antisymm
  · exact (dcl_subset_acl H.Aut A).trans (by rw [H.full_acl_eq_closure hfin hInf hA])
  · exact H.closure_subset_full_dcl A

theorem infiniteClosedOrbits_iff_full_acl (hfin : H.LocallyFinite) :
    H.InfiniteClosedOrbits H.Aut ↔
      ∀ (A : Set V), A.Finite → Acl H.Aut A = H.closure A := by
  refine ⟨fun h A hA => H.full_acl_eq_closure hfin h hA, ?_⟩
  intro h A hA hc x hx hOrbit
  have he := h A hA
  have hmem : x ∈ H.closure A := he ▸ hOrbit
  exact hx (H.closure_eq hc ▸ hmem)

/-- `lem:unary-homogeneous-sap-criterion`, equation UA.
Countability is retained from the source statement; the stronger preceding
proofs require only actual finite closed homogeneity and local finiteness. -/
theorem hereditary_unary_sap_criterion [Countable V] (hfin : H.LocallyFinite)
    (hom : H.Homogeneous) :
    H.AgeSAP ↔ ∀ (T : Set V), T.Finite → Acl H.Aut T = H.closure T :=
  (H.ageSAP_iff_infiniteClosedOrbits hfin hom).trans
    (H.infiniteClosedOrbits_iff_full_acl hfin)

/-- The source's additional dcl conclusion, on every finite HIDDEN set. -/
theorem hereditary_sap_full_dcl [Countable V] (hfin : H.LocallyFinite)
    (hom : H.Homogeneous) (sap : H.AgeSAP) {T : Set V} (hT : T.Finite) :
    Dcl H.Aut T = H.closure T :=
  H.full_dcl_eq_closure hfin (H.infiniteClosedOrbits_of_ageSAP hfin hom sap) hT

end CCO.UnaryFreshFrames.Structure
