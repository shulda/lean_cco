import CCO.PointGeneratedSAP.Forward
import CCO.PointGeneratedSAP.Reverse

/-! The selected source lemma and its displayed PGO equation. All bases
are full point-generated objects; original real homogeneity suffices. -/
universe u v
namespace CCO.PointGeneratedSAP
open UnaryFreshFrames
variable {L : Language.{u}} {V : Type v} {H : Structure L V}
variable {O : Original L V H} (C : Interpretation H O)
namespace Interpretation

/-- `lem:typed-point-generated-sap-criterion` and its PGO equation. -/
theorem typed_point_generated_sap_criterion (hom : O.Homogeneous) :
    AgeSAP O ↔ C.PGO :=
  ⟨C.PGO_of_ageSAP hom,C.ageSAP_of_PGO hom⟩

/-- The displayed equation with the literal ORIGINAL full-stabilizer orbit. -/
theorem original_action_equation (hom : O.Homogeneous) :
    AgeSAP O ↔ ∀ D : Set O.Real, D.Finite → ∀ u,
      u ∉ H.closure (Subtype.val '' D) →
      {v | ∃ g : O.Aut, (∀ d ∈ D, g • d = d) ∧ C.lift g • u = v}.Infinite := by
  rw [C.typed_point_generated_sap_criterion hom]
  apply forall_congr'
  intro D
  apply imp_congr_right
  intro _
  apply forall_congr'
  intro u
  apply imp_congr_right
  intro _
  have he : C.orbitOver D u = {v | ∃ g : O.Aut, (∀ d ∈ D, g • d = d) ∧ C.lift g • u = v} := by
    ext v
    exact C.mem_orbitOver_iff D u v
  rw [he]

end Interpretation
end CCO.PointGeneratedSAP
