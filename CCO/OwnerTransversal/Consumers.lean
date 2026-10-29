import CCO.OwnerTransversal.TransversalCompletion
import CCO.OwnerTransversal.TransversalInstance
import CCO.OwnerTransversal.Primitivity

/-! End-to-end actual-source consumers.  The countable transversal is
the internally constructed `TransversalAge.U`, and its model is built
from the actual source age.  No external model, EPPA, original SAP or
countable-existence provider appears among the hypotheses. -/
universe v w t
namespace CCO.OwnerTransversal
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R))

/-- Every named sort of this SAME internally built actual transversal
is primitive under its FULL named-owner/fine-colour automorphism group. -/
theorem residual_owner_sorts_primitive (s : ↥B)
    (Q : SortEquivalence S H R B (TransversalAge.model S H R B) s) :
    Q.eqv = ⊥ ∨ Q.eqv = ⊤ :=
  Q.eqv_eq_bot_or_top

/-- A protected finite typed CCO request is completed in N_B, separated
into actual source packets, and embedded into the actual internal U.
Every recorded edge, every owner and the ENTIRE completed fine matrix
are retained.  Protected real images are literal throughout the source
completion; their resulting matrix is retained in U as well. -/
theorem protected_pattern_in_primitive_transversal
    {n : Nat} (P : OriginPattern S H R (Fin n))
    (overB : ∀ x, P.owner x ∈ B)
    (compatible : ∀ x y a, P.edge x y = some a →
      ownerSaturate R.E.val (S.atomRel a) (P.owner x).out (P.owner y).out)
    (cycles : ∀ C : SimpleCycle P.records.diagram, CycleHom C)
    (A : Finset (Fin n)) (complete : RawRecords.CompleteOn S P.records A)
    (j : Fin n → NamedCarrier S H R B)
    (hj : ∀ x ∈ A, ∀ y ∈ A, ∀ a, P.edge x y = some a →
      col S (j x).val (j y).val = some a)
    (hOwn : ∀ x ∈ A, owner S H R (j x).val = P.owner x)
    (hSep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      ¬ finitePacket S H (j x).val (j y).val) :
    ∃ (f : OriginMap S H R B P) (e : Fin n ↪ TransversalAge.U S H R B),
      (∀ x ∈ A, f.point x = j x) ∧ f.PacketSeparated ∧
      (∀ x, ((TransversalAge.limitTable S H R B).owner (e x)).val = P.owner x) ∧
      (∀ x y a, P.edge x y = some a →
        (TransversalAge.limitTable S H R B).colour (e x) (e y) = some a) ∧
      (∀ x y, (TransversalAge.limitTable S H R B).colour (e x) (e y) =
        col S (f.point x).val (f.point y).val) ∧
      (∀ x ∈ A, ∀ y ∈ A,
        (TransversalAge.limitTable S H R B).colour (e x) (e y) = col S (j x).val (j y).val) ∧
      (∀ s : ↥B, ∀ Q : SortEquivalence S H R B (TransversalAge.model S H R B) s,
        Q.eqv = ⊥ ∨ Q.eqv = ⊤) := by
  obtain ⟨f,hfix,hSeparated⟩ := protected_transversal_CCO S H R B P
    overB compatible cycles A complete j hj hOwn hSep
  obtain ⟨e,hOwner,hColour⟩ := (TransversalAge.model S H R B).embed f.point hSeparated
  refine ⟨f,e,hfix,hSeparated,?_,?_,hColour,?_,?_⟩
  · intro x
    exact (hOwner x).trans (f.owner x)
  · intro x y a ha
    exact (hColour x y).trans (f.edge x y a ha)
  · intro x hx y hy
    exact (hColour x y).trans (by rw [hfix x hx,hfix y hy])
  · exact residual_owner_sorts_primitive S H R B

end
end CCO.OwnerTransversal
