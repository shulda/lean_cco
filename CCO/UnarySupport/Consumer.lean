import CCO.UnarySupport.Bounds
import CCO.UnarySupport.LocalTheorem

/-! Receiving use of BOTH source results. Actual irreducible K membership
first forces totality of a genuinely partial input. That derived totality,
not an additional totality premise, then feeds the binary local theorem. -/
universe u v w
namespace CCO.UnarySupport
open Structure
variable {L : Signature.{u}} {V : Type v} {W : Type w}

theorem local_hn_readout [Finite V] (C : Structure L V) (H : Structure L W)
    (CompletedTarget : Structure L W → Prop) (hH : CompletedTarget H)
    {K : Class.{u,v} L} (hCompleted : CompletedClass K) (hK : C.IrreduciblesIn K)
    (hbin : ∀ R, L.arity R ≤ 2) (f : Hom C H) (hf : f.LocallyInduced) :
    C.FullUnaryAdmissible K ∧
    (∀ S (hS : C.IsClosed S), S.Nonempty → (C.induce S hS).Irreducible →
      ∃ e : Embedding (C.induce S hS) H, ∀ x : S, e.point x = f.point x.val) ∧
    (f.NullaryAgreement → f.HomEmbedding) ∧
    (∀ m, UniformOneGeneratedBound K m → ∀ B : Finset V,
      Nat.card (C.closure (B : Set V)) ≤ m * B.card) := by
  have hHN := C.hn_irreducible_forces_unary_admissible hCompleted hK
  have hlocal := typed_binary_irreducible_local_cover C H CompletedTarget hH
    hHN.2.1 hbin f hf
  refine ⟨hHN.2.2.2.1, ?_, hlocal.2.2, ?_⟩
  · intro S hS hne hirr
    exact ⟨f.restrictionEmbedding hS (hlocal.2.1 S hS hne hirr), fun _ => rfl⟩
  · intro m hm B
    exact (hHN.2.2.2.2 m hm).2.1 B

end CCO.UnarySupport
