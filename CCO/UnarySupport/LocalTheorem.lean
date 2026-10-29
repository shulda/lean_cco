import CCO.UnarySupport.NullaryGate

universe u v w
namespace CCO.UnarySupport
open Structure
variable {L : Signature.{u}} {V : Type v} {W : Type w}

theorem pair_cover_of_total (C : Structure L V) (_hC : C.Total)
    (hbin : ∀ R, L.arity R ≤ 2) (S : Set V) (hS : C.IsClosed S)
    (_hne : S.Nonempty) (hirr : (C.induce S hS).Irreducible)
    (x y : S) (hxy : x ≠ y) :
    ∃ A, (C.induce S hS).LocalSupport A ∧ x ∈ A ∧ y ∈ A :=
  (C.induce S hS).pair_support hbin hirr x y hxy

/-- First pinned source result. `Completed` is the CALLER'S actual target
class; its membership hypothesis is retained and unused. It is not a newly
derived completeness notion. Core lemmas above work for every target.
The nonempty HE clause is unconditional; the empty/nullary clause explicitly
requires agreement. Positive-arity and nonempty-source corollaries are separate. -/
theorem typed_binary_irreducible_local_cover [Finite V]
    (C : Structure L V) (H : Structure L W)
    (Completed : Structure L W → Prop) (_hH : Completed H)
    (hC : C.Total) (hbin : ∀ R, L.arity R ≤ 2)
    (f : Hom C H) (hf : f.LocallyInduced) :
    (∀ S (hS : C.IsClosed S), S.Nonempty → (C.induce S hS).Irreducible →
      ∀ x y : S, x ≠ y → ∃ A, (C.induce S hS).LocalSupport A ∧ x ∈ A ∧ y ∈ A) ∧
    f.NonemptyHomEmbedding ∧ (f.NullaryAgreement → f.HomEmbedding) :=
  ⟨pair_cover_of_total C hC hbin, f.locallyInduced_nonempty hC hbin hf,
    f.locallyInduced_full hC hbin hf⟩

end CCO.UnarySupport
