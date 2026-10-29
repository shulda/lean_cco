import CCO.SafeReadings.GateDescent
import Mathlib.Algebra.Order.BigOperators.Group.Finset

universe u v w z t
namespace CCO.SafeReadings
open Selectors
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {Λ : Type z} [Group Λ] {N : Type t} {Q : Family S}

/-- Orbits of actual evaluated tagged menus. No free action is required. -/
def tagOrbitSetoid (A : PureTagAction S Λ N) : Setoid (TaggedMenu S) where
  r D E := ∃ g, A.act g D = E
  iseqv := ⟨fun D => ⟨1,A.one D⟩,
    by
      rintro D E ⟨g,h⟩
      refine ⟨g⁻¹,?_⟩
      rw [← h,A.inv_act],
    by
      rintro D E F ⟨g,hg⟩ ⟨h,hh⟩
      exact ⟨h*g,by rw [A.mul,hg,hh]⟩⟩

def orbitClass (A : PureTagAction S Λ N) (D : TaggedMenu S) : Quotient (tagOrbitSetoid S A) :=
  Quotient.mk _ D

/-- Only represented nonsingleton orbits are charged by the iteration. -/
def representedOrbits (A : PureTagAction S Λ N) (J : Family S) :
    Set (Quotient (tagOrbitSetoid S A)) := orbitClass S A '' (J \ atomicFamily S)

noncomputable def orbitCount (A : PureTagAction S Λ N) (J : Family S) : Nat :=
  Nat.card (representedOrbits S A J)

theorem representedOrbits_mono (A : PureTagAction S Λ N) {J K : Family S} (h : K ⊆ J) :
    representedOrbits S A K ⊆ representedOrbits S A J := by
  rintro _ ⟨D,⟨hD,ha⟩,rfl⟩
  exact ⟨D,⟨h hD,ha⟩,rfl⟩

theorem orbitCount_mono (A : PureTagAction S Λ N) {J K : Family S} (h : K ⊆ J) :
    orbitCount S A K ≤ orbitCount S A J :=
  Set.ncard_le_ncard (representedOrbits_mono S A h)
    ((Set.toFinite (J \ atomicFamily S)).image (orbitClass S A))

theorem orbitCount_terminal (A : PureTagAction S Λ N) {J : Family S} (h : Terminal S J) :
    orbitCount S A J = 0 := by
  have he : J \ atomicFamily S = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro D ⟨hD,ha⟩
    exact ha (h D hD)
  simp [orbitCount,representedOrbits,he]

/-- The subtracted atomic family is exactly the excluded size-one case. -/
theorem not_atomic_iff_two_le (C : MenuCalculus S Q) {D : TaggedMenu S} (hD : D ∈ Q) :
    D ∉ atomicFamily S ↔ 2 ≤ Nat.card D.2.2 := by
  letI := S.finiteAtom D.1 D.2.1
  have hp : 0 < D.2.2.ncard := (Set.ncard_pos).mpr (C.nonempty hD)
  have he : D ∈ atomicFamily S ↔ D.2.2.ncard = 1 := Set.ncard_eq_one.symm
  change (¬ D ∈ atomicFamily S) ↔ 2 ≤ D.2.2.ncard
  rw [he]
  omega

/-- Removing one member of an invariant family removes its whole orbit. -/
theorem removed_whole_orbit (A : PureTagAction S Λ N) {K : Family S}
    (hK : A.Invariant K) {D : TaggedMenu S} (hD : D ∉ K) (g : Λ) : A.act g D ∉ K := by
  intro h
  have h' := hK g⁻¹ _ h
  rw [A.inv_act] at h'
  exact hD h'

theorem orbitCount_strict (A : PureTagAction S Λ N) {J K : Family S}
    (hK : Current S Q K) (hKI : A.Invariant K) (hsub : K ⊆ J)
    (hstrict : Nat.card K < Nat.card J) : orbitCount S A K < orbitCount S A J := by
  have hproper : K ⊂ J := Set.ssubset_iff_subset_ne.mpr ⟨hsub,by
    intro heq
    exact (ne_of_lt hstrict) (congrArg (fun T : Family S => Nat.card T) heq)⟩
  obtain ⟨D,hDJ,hDK⟩ := Set.exists_of_ssubset hproper
  have hDa : D ∉ atomicFamily S := fun h => hDK (atomicFamily_subset S hK h)
  have hclassJ : orbitClass S A D ∈ representedOrbits S A J := ⟨D,⟨hDJ,hDa⟩,rfl⟩
  have hclassK : orbitClass S A D ∉ representedOrbits S A K := by
    rintro ⟨E,⟨hEK,_⟩,hclass⟩
    obtain ⟨g,hg⟩ := Quotient.exact hclass
    exact hDK (hg ▸ hKI g E hEK)
  apply Set.ncard_lt_ncard (ht := (Set.toFinite (J \ atomicFamily S)).image (orbitClass S A))
  refine Set.ssubset_iff_subset_ne.mpr ⟨representedOrbits_mono S A hsub,?_⟩
  intro heq
  exact hclassK (heq.symm ▸ hclassJ)

theorem IsVisibleGate.image_subset (C : MenuCalculus S Q) (A : PureTagAction S Λ N)
    {J K : Family S} {R : Contraction S J K} (h : IsVisibleGate S (Q := Q) A R) : K ⊆ J := by
  obtain ⟨F,hF,_,hV,hK,_⟩ := h.actual_gate
  rw [hK]
  exact gateImage_subset S C hF h.current_domain hV

/-- A changed current menu and every translate are absent from the fixed image. -/
theorem proper_gate_removed_orbit (C : MenuCalculus S Q) (A : PureTagAction S Λ N)
    {F J : Family S} (hF : Filter S Q F) (hJ : Current S Q J)
    (hV : Visible S F J) (hFI : A.Invariant F) (hJI : A.Invariant J)
    {i j} {D : S.Menu i j} (hchange : gate S F D ≠ D) (g : Λ) :
    A.act g (⟨i,j,D⟩ : TaggedMenu S) ∉ gateImage S F J := by
  apply removed_whole_orbit S A (A.invariant_gateImage F J hFI hJI)
  intro hD
  rw [gateImage_eq_fixed S C hF hJ hV] at hD
  exact hchange hD.2

/-- Later images remain nested in the actual initial family. -/
theorem visible_chain_subset (C : MenuCalculus S Q) (A : PureTagAction S Λ N)
    {J K : Family S} {n : Nat} (chain : DescentChain S (IsVisibleGate S (Q := Q) A) J K n) :
    K ⊆ J := by
  induction chain with
  | nil J => exact Set.Subset.rfl
  | cons R _ tail ih => exact ih.trans (R.property.image_subset S C A)

/-- Stabilizers of endpoint tags fix literal evaluated menus, including atoms. -/
theorem stabilizer_fixes_menu (A : PureTagAction S Λ N) (g : Λ) (D : TaggedMenu S)
    (hi : A.tag g D.1 = D.1) (hj : A.tag g D.2.1 = D.2.1) : A.act g D = D :=
  A.tagged_names_injective ⟨(A.source g D).trans hi,(A.target g D).trans hj⟩ (A.literal g D)

/-- Post-hoc orbit bound for the SAME finite gate-descent chain. -/
theorem visible_chain_orbit_bound (C : MenuCalculus S Q) (A : PureTagAction S Λ N)
    {J K : Family S} {n : Nat} (chain : DescentChain S (IsVisibleGate S (Q := Q) A) J K n) :
    n + orbitCount S A K ≤ orbitCount S A J := by
  induction chain with
  | nil J => simp
  | cons R hstrict tail ih =>
    have hdrop := orbitCount_strict S A R.property.current_image R.property.invariant_image
      (R.property.image_subset S C A) hstrict
    omega

theorem orbitCount_le_menu_count (A : PureTagAction S Λ N) {J : Family S} (hJ : Current S Q J) :
    orbitCount S A J ≤ Nat.card J - Nat.card (atomicFamily S) := by
  have h := Set.ncard_image_le (f := orbitClass S A) (s := J \ atomicFamily S)
  change (representedOrbits S A J).ncard ≤ _ at h
  change (representedOrbits S A J).ncard ≤ J.ncard - (atomicFamily S).ncard
  simpa only [Set.ncard_sdiff (atomicFamily_subset S hJ)] using h

/-- Each hom-family counts distinct evaluated sets, not presentations. -/
def homFamily (J : Family S) (i j : ι) : Set (S.Menu i j) :=
  {D | (⟨i,j,D⟩ : TaggedMenu S) ∈ J}

theorem family_card (J : Family S) :
    Nat.card J = S.finiteSort.elems.sum fun i =>
      S.finiteSort.elems.sum fun j => Nat.card (homFamily S J i j) := by
  classical
  letI := S.finiteSort
  letI : ∀ i j, Fintype (S.Atom i j) := S.finiteAtom
  letI : ∀ i j, Fintype (homFamily S J i j) := fun i j => Fintype.ofFinite _
  let e : (Σ i, Σ j, homFamily S J i j) ≃ J :=
    { toFun := fun D => ⟨⟨D.1,D.2.1,D.2.2.val⟩,D.2.2.property⟩
      invFun := fun D => ⟨D.val.1,D.val.2.1,⟨D.val.2.2,D.property⟩⟩
      left_inv := by rintro ⟨i,j,D,hD⟩; rfl
      right_inv := by rintro ⟨⟨i,j,D⟩,hD⟩; rfl }
  rw [← Nat.card_congr e,Nat.card_eq_fintype_card]
  simp only [Fintype.card_sigma,Nat.card_eq_fintype_card]
  rfl

theorem hom_atoms_card_le {J : Family S} (hJ : Current S Q J) (i j : ι) :
    Nat.card (S.Atom i j) ≤ Nat.card (homFamily S J i j) := by
  let f : S.Atom i j → homFamily S J i j := fun a => ⟨{a},hJ.singleton a⟩
  apply Nat.card_le_card_of_injective f
  intro a b hab
  exact Set.singleton_injective (congrArg Subtype.val hab)

theorem orbitCount_le_sum (A : PureTagAction S Λ N) {J : Family S} (hJ : Current S Q J) :
    orbitCount S A J ≤ S.finiteSort.elems.sum (fun i =>
      S.finiteSort.elems.sum fun j => Nat.card (homFamily S J i j) - Nat.card (S.Atom i j)) := by
  have h := orbitCount_le_menu_count S A hJ
  rw [family_card S J,Selectors.atomicFamily_card S] at h
  have he : S.finiteSort.elems.sum (fun i => S.finiteSort.elems.sum fun j =>
      Nat.card (homFamily S J i j) - Nat.card (S.Atom i j)) =
      S.finiteSort.elems.sum (fun i => S.finiteSort.elems.sum fun j => Nat.card (homFamily S J i j)) -
      S.finiteSort.elems.sum (fun i => S.finiteSort.elems.sum fun j => Nat.card (S.Atom i j)) := by
    rw [← Finset.sum_tsub_distrib _ (fun i _ =>
      Finset.sum_le_sum (fun j _ => hom_atoms_card_le S hJ i j))]
    apply Finset.sum_congr rfl
    intro i hi
    exact Finset.sum_tsub_distrib _ (fun j _ => hom_atoms_card_le S hJ i j)
  rw [he]
  exact h

theorem orbitCount_le_sum_of_hom_bound (A : PureTagAction S Λ N) {J : Family S}
    (hJ : Current S Q J) (b : ι → ι → Nat)
    (hb : ∀ i j, Nat.card (homFamily S J i j) ≤ b i j) :
    orbitCount S A J ≤ S.finiteSort.elems.sum (fun i =>
      S.finiteSort.elems.sum fun j => b i j - Nat.card (S.Atom i j)) := by
  apply (orbitCount_le_sum S A hJ).trans
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
    (fun j _ => Nat.sub_le_sub_right (hb i j) _))

/-- Orbit refinement of the actual finite descent, without a second iteration. -/
theorem pure_gate_iteration_orbit_bound (C : MenuCalculus S Q)
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    (A : PureTagAction S Λ N) (hQI : A.Invariant Q) (hNoReturn : NoReturn S Q A)
    (J : Family S) (hJ : Current S Q J) (hInv : A.Invariant J) :
    ∃ K, Current S Q K ∧ A.Invariant K ∧ Terminal S K ∧
      ∃ n, n ≤ orbitCount S A J ∧ n ≤ Nat.card J - Nat.card (atomicFamily S) ∧
        ∃ chain : DescentChain S (IsVisibleGate S (Q := Q) A) J K n,
          A.Covariant (DescentChain.composite chain) := by
  obtain ⟨K,hK,hKI,hTerm,n,hBound,chain,hCov⟩ :=
    pure_gate_iteration S C hPoint hEdge A hQI hNoReturn J hJ hInv
  have horbit := visible_chain_orbit_bound S C A chain
  exact ⟨K,hK,hKI,hTerm,n,by omega,hBound,chain,hCov⟩

end CCO.SafeReadings
