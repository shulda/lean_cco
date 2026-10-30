import CCO.UnaryFreshFrames.Source
import CCO.UnaryFreshFrames.SAPCopies

/-! Concrete consumers request an actual real frame and actual strong age
amalgam from the proved RK direction. No principal proof is a consumer input. -/
universe u v
namespace CCO.UnaryFreshFrames.Structure
variable {L : Language.{u}} {V : Type v} (H : Structure L V)

theorem constructed_fresh_frame (scope : H.FinalScope) (G : Subgroup H.Aut)
    {real : Set L.Sorts} (S : H.NamedQuotientSystem real)
    (ht : H.RealSortTransitive G real) (hk : S.KernelClauses)
    (A B : Set V) (hA : A.Finite) (hB : B.Finite) (hcA : H.Closed A)
    (hAB : A ⊆ B) :
    ∃ D : Set V, D.Finite ∧ D ⊆ H.realSet real ∧
      A ⊆ H.closure D ∧ H.closure D ∩ B = A :=
  H.quotient_system_fresh_frame S G (H.source_transitive S G ht)
    (fun x => scope.locallyFinite {x} (Set.finite_singleton x)) hk A B hA hcA hB hAB

theorem constructed_strong_amalgam (scope : H.FinalScope) (G : Subgroup H.Aut)
    {real : Set L.Sorts} (S : H.NamedQuotientSystem real)
    (ht : H.RealSortTransitive G real) (hk : S.KernelClauses)
    (hReal : H.FullRealBaseOrbits (H.realSet real))
    (A B C : H.Piece) (s : A.Embedding B.points) (t : A.Embedding C.points) :
    ∃ (D : H.Piece) (l : B.Embedding D.points) (r : C.Embedding D.points),
      (∀ x, l.point ⟨s.point x, s.mem_point x⟩ = r.point ⟨t.point x, t.mem_point x⟩) ∧
      ∀ x y, l.point x = r.point y → ∃ a, s.point a = x.val ∧ t.point a = y.val :=
  (H.typed_abstract_fresh_frame_sap scope G S ht hk hReal).2.2 A B C s t

end CCO.UnaryFreshFrames.Structure
