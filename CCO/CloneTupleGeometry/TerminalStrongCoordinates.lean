import CCO.CloneTupleGeometry.TerminalTupleDomain
import CCO.CloneTupleGeometry.FiniteTypedExact
import CCO.CloneTupleGeometry.DiagonalAndMeet
import CCO.CloneTupleGeometry.StrongClone

/-! Genuine positive STRONG presentations of every selected terminal FULL
MI kernel. A RAW word is first proved on the actual new clone source;
logical identity letters are removed and accepted relational SAP separates
its positions. The nonempty clone atom excludes the empty identity branch.
Two finite exact-product applications then recover a singleton spectrum. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w
namespace CCO.CloneTupleGeometry.OwnerStage
open APCharacter.Towers ParityHasse.Original TerminalLattice
noncomputable section
variable (B : OwnerStage.{u,v,w})

/-- Every selected terminal MI diversity support contains the actual
clone atom, witnessed by two distinct clones of one actual owner. -/
theorem clone_atom_mem_MI (i : B.Sorts) (J : FullCloneProperMI B.source i) :
    Sum.inr ⟨rfl⟩ ∈ originalEquivDiversityPalette (CloneSAP.source B.source) J.val := by
  obtain ⟨x⟩ := B.source.nonemptySort i
  refine ⟨(x,0),(x,1),?_,?_⟩
  · exact fullCloneKernel_le_nonidentity B.source i J.val J.property.1 rfl
  · exact (CloneSAP.source_clone_iff B.source (x,0) (x,1)).mpr ⟨rfl,Nat.zero_ne_one⟩

/-- The actual terminal MI RAW word gives one genuine positive STRONG
profile; no exactness or positive-word presentation is supplied by callers. -/
theorem terminal_MI_positive_word (ht : B.Terminal) (i : B.Sorts)
    (J : FullCloneProperMI B.source i) :
    ∃ p : PositiveWord (CloneSAP.source B.source) i i,
      PositiveWord.profile (CloneSAP.source B.source) p =
        originalEquivDiversityPalette (CloneSAP.source B.source) J.val := by
  obtain ⟨word,hw⟩ := RealClosure.Bounds.terminal_one_raw_word
    (CloneSAP.source B.source) (CloneSAP.homogeneous B.source B.homogeneous) (B.terminal_sortNR2 ht i) J.val
  have hg : (CloneSAP.source B.source).diversityGuard
      (RawWord.relation (CloneSAP.source B.source) word) =
      originalEquivDiversityPalette (CloneSAP.source B.source) J.val := by
    rw [hw]
    rfl
  rcases PositiveWord.raw_guard_empty_or_positive_profile_of_SAP
      (CloneSAP.source B.source) (CloneSAP.homogeneous B.source B.homogeneous) (CloneSAP.strong_amalgamation B.source B.ap) word with he | ⟨p,hp⟩
  · have hc := B.clone_atom_mem_MI i J
    rw [← hg,he] at hc
    exact False.elim hc
  · exact ⟨p,hp.symm.trans hg⟩

/-- Nonempty positive STRONG exactness is discharged at the NEW terminal
clone source, independently of the AP-only original owner multiplication. -/
theorem terminal_MI_strong_exact (ht : B.Terminal) (i : B.Sorts)
    (J : FullCloneProperMI B.source i) :
    StrongExact.Exact (CloneSAP.source B.source)
      (originalEquivDiversityPalette (CloneSAP.source B.source) J.val) := by
  obtain ⟨p,hp⟩ := B.terminal_MI_positive_word ht i J
  refine ⟨⟨Sum.inr ⟨rfl⟩,B.clone_atom_mem_MI i J⟩,[p],?_⟩
  ext a
  simp only [StrongExact.present,List.mem_singleton,forall_eq,← hp]
  rfl

/-- Right clone multiplication fixes every actual clone-source diversity
atom, including the same-owner clone atom. Logical equality is absent. -/
theorem clone_strong_right {i j : B.Sorts} (a : (CloneSAP.source B.source).Atom i j) :
    (CloneSAP.source B.source).product {a} {Sum.inr ⟨rfl⟩} = {a} := by
  cases a with
  | inl a => exact pure_clone_strong_right B.source a
  | inr e =>
      cases e.down
      exact pure_clone_strong_square B.source i

/-- Left clone multiplication has the corresponding literal rule. -/
theorem clone_strong_left {i j : B.Sorts} (a : (CloneSAP.source B.source).Atom i j) :
    (CloneSAP.source B.source).product {Sum.inr ⟨rfl⟩} {a} = {a} := by
  cases a with
  | inl a => exact pure_clone_strong_left B.source a
  | inr e =>
      cases e.down
      exact pure_clone_strong_square B.source i

/-- The first nonempty exact distribution collapses the entire right
family. Each product is exact at the actual terminal SAP+HOM CCO source. -/
theorem terminal_right_cylinders_meet (ht : B.Terminal) {i j : B.Sorts}
    (a : (CloneSAP.source B.source).Atom i j) :
    ({b | ∀ L : FullCloneProperMI B.source j,
      b ∈ (CloneSAP.source B.source).product {a}
        (originalEquivDiversityPalette (CloneSAP.source B.source) L.val)} :
      (CloneSAP.source B.source).Menu i j) = {a} := by
  have he := original_typed_exact_finite_right_meet
    (CloneSAP.source B.source) (CloneSAP.homogeneous B.source B.homogeneous) (CloneSAP.strong_amalgamation B.source B.ap) (CloneSAP.CCO.cco_forward B.source B.cco)
    {a} (fun L : FullCloneProperMI B.source j =>
      originalEquivDiversityPalette (CloneSAP.source B.source) L.val)
    (StrongExact.exact_singleton _ a) (B.terminal_MI_strong_exact ht j)
    (by rw [pure_clone_all_MI_diversity_meet]; exact ⟨Sum.inr ⟨rfl⟩,rfl⟩)
  rw [pure_clone_all_MI_diversity_meet,B.clone_strong_right] at he
  exact he.symm

/-- The second exact distribution recovers the original actual clone
atom from ALL mixed MI cylinders, including the visible equality marker. -/
theorem terminal_strong_cylinder_singleton (ht : B.Terminal) {i j : B.Sorts}
    (a : (CloneSAP.source B.source).Atom i j) :
    ({b | ∀ J : FullCloneProperMI B.source i, ∀ L : FullCloneProperMI B.source j,
      b ∈ (CloneSAP.source B.source).product
        (originalEquivDiversityPalette (CloneSAP.source B.source) J.val)
        ((CloneSAP.source B.source).product {a}
          (originalEquivDiversityPalette (CloneSAP.source B.source) L.val))} :
      (CloneSAP.source B.source).Menu i j) = {a} := by
  let rights (L : FullCloneProperMI B.source j) :=
    (CloneSAP.source B.source).product {a}
      (originalEquivDiversityPalette (CloneSAP.source B.source) L.val)
  have hr : ∀ L, StrongExact.Exact (CloneSAP.source B.source) (rights L) := by
    intro L
    exact original_typed_exact_product (CloneSAP.source B.source)
      (CloneSAP.homogeneous B.source B.homogeneous) (CloneSAP.strong_amalgamation B.source B.ap) (CloneSAP.CCO.cco_forward B.source B.cco)
      (StrongExact.exact_singleton _ a) (B.terminal_MI_strong_exact ht j L)
  have hm : ({b | ∀ L, b ∈ rights L} : (CloneSAP.source B.source).Menu i j) = {a} :=
    B.terminal_right_cylinders_meet ht a
  have he := original_typed_exact_finite_double_meet
    (CloneSAP.source B.source) (CloneSAP.homogeneous B.source B.homogeneous) (CloneSAP.strong_amalgamation B.source B.ap) (CloneSAP.CCO.cco_forward B.source B.cco)
    (fun J : FullCloneProperMI B.source i =>
      originalEquivDiversityPalette (CloneSAP.source B.source) J.val)
    rights (B.terminal_MI_strong_exact ht i) hr
    (by rw [pure_clone_all_MI_diversity_meet]; exact ⟨Sum.inr ⟨rfl⟩,rfl⟩)
    (by rw [hm]; exact ⟨a,rfl⟩)
  rw [pure_clone_all_MI_diversity_meet,hm,B.clone_strong_left] at he
  exact he.symm

end
end CCO.CloneTupleGeometry.OwnerStage
