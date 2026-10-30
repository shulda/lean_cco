import CCO.UnaryFreshFrames.FullFrames
import CCO.UnaryFreshFrames.Scope
import CCO.UnaryFreshFrames.UniformBounds
import CCO.UnaryFreshFrames.Quotient.AFF
import CCO.UnaryFreshFrames.Quotient.SAPNecessity

/-! All FIVE B039 source exports. The AFF construction is a separate theorem
whose hypotheses contain no homogeneity, countability or full-Aut real-base
orbit condition. The final homogeneous conclusion retains the source scope.
Every projection and every factor term is actual existing named syntax. -/
universe u v
namespace CCO.UnaryFreshFrames.Structure
variable {L : Language.{u}} {V : Type v} (H : Structure L V)

def RealSortTransitive (G : Subgroup H.Aut) (real : Set L.Sorts) : Prop :=
  ∀ i ∈ real, Quotient.Transitive (G := G) (M := H.Carrier i)

theorem source_transitive {real : Set L.Sorts} (S : H.NamedQuotientSystem real)
    (G : Subgroup H.Aut) (ht : H.RealSortTransitive G real) : S.SourceTransitive G :=
  fun q => ht (S.projection q).source (S.source_real q)

theorem AFF {real : Set L.Sorts} (S : H.NamedQuotientSystem real)
    (G : Subgroup H.Aut) (ht : H.RealSortTransitive G real)
    (hfinite : ∀ x : V, (H.closureAt x).Finite) (hk : S.KernelClauses) :
    H.FreshFrames (H.realSet real) := by
  intro A B hA hB hclosed _ hAB
  exact H.quotient_system_fresh_frame S G (H.source_transitive S G ht)
    hfinite hk A B hA hclosed hB hAB

/-- `thm:typed-abstract-fresh-frame-sap`, including equation AFF. The actual
subgroup G supplies quotient-fibre avoidance; FULL Aut supplies real-base
orbit infinitude only AFTER the frame has been constructed. -/
theorem typed_abstract_fresh_frame_sap (scope : H.FinalScope)
    (G : Subgroup H.Aut) {real : Set L.Sorts} (S : H.NamedQuotientSystem real)
    (ht : H.RealSortTransitive G real) (hk : S.KernelClauses)
    (hReal : H.FullRealBaseOrbits (H.realSet real)) :
    H.FreshFrames (H.realSet real) ∧
      (∀ T : Set V, T.Finite → Acl H.Aut T = H.closure T ∧ Dcl H.Aut T = H.closure T) ∧
      H.AgeSAP := by
  have hf := H.AFF S G ht (fun x => scope.locallyFinite {x} (Set.finite_singleton x)) hk
  have hi := H.full_infiniteClosedOrbits_of_frames scope.locallyFinite hf hReal
  exact ⟨hf, fun T hT => ⟨H.full_acl_eq_closure scope.locallyFinite hi hT,
    H.full_dcl_eq_closure scope.locallyFinite hi hT⟩,
    (H.ageSAP_iff_infiniteClosedOrbits scope.locallyFinite scope.homogeneous).mpr hi⟩

/-- `cor:typed-abstract-relative-kernel-sap-iff`, equation RK. The forward
implication assumes SAP ALONE over the unchanged structural hypotheses; it
does not assume either kernel clause or a real-base orbit premise. -/
theorem typed_abstract_relative_kernel_sap_iff (scope : H.FinalScope)
    (G : Subgroup H.Aut) {real : Set L.Sorts} (S : H.NamedQuotientSystem real)
    (ht : H.RealSortTransitive G real) :
    H.AgeSAP ↔
      (∀ D : Set V, D.Finite → D ⊆ H.realSet real → Acl H.Aut D = H.closure D) ∧
        S.KernelClauses := by
  constructor
  · intro sap
    have hi := H.infiniteClosedOrbits_of_ageSAP scope.locallyFinite scope.homogeneous sap
    exact ⟨fun D hD _ => H.full_acl_eq_closure scope.locallyFinite hi hD,
      H.kernel_clauses_of_ageSAP S G (H.source_transitive S G ht)
        scope.locallyFinite scope.homogeneous sap⟩
  · rintro ⟨hReal, hk⟩
    exact (H.typed_abstract_fresh_frame_sap scope G S ht hk
      (H.full_real_orbits_of_acl hReal)).2.2

/-- C36 in the final source scope derives actual FINITE singleton bounds;
finite language supplies the finite real-sort family, not a term oracle. -/
theorem source_uniform_real_bound (scope : H.FinalScope) (G : Subgroup H.Aut)
    (real : Set L.Sorts) (ht : H.RealSortTransitive G real) :
    ∃ N : ℕ, ∀ x : V, H.sort x ∈ real →
      (H.closureAt x).Finite ∧ (H.closureAt x).ncard ≤ N := by
  let : Finite L.Sorts := scope.finiteLanguage.1
  exact @uniform_real_singleton_bound L V H scope.locallyFinite G (fun i => i ∈ real)
    (Finite.of_injective Subtype.val Subtype.val_injective) ht

end Structure

namespace Source

abbrev foundational_real_frame_orbits := @Structure.fresh_frames_iff
abbrev unary_homogeneous_sap_criterion := @Structure.hereditary_unary_sap_criterion
abbrev foundational_quotient_fibre_avoidance := @Structure.named_fibre_avoidance
abbrev typed_abstract_fresh_frame_sap := @Structure.typed_abstract_fresh_frame_sap
abbrev typed_abstract_relative_kernel_sap_iff := @Structure.typed_abstract_relative_kernel_sap_iff

end Source
end CCO.UnaryFreshFrames
