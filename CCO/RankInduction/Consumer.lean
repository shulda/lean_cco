import CCO.RankInduction.Source

/-! Genuine common-carrier use of the constructed global result: an
arbitrary original partial map, an arbitrary point motion and a selected
unsafe-clique transport all act inside the SAME closed finite witness. -/

universe v w t
namespace CCO.RankInduction
noncomputable section
open RawExact Owners.Product

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] [Countable M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)

include H cco in
theorem constructed_witness_use (safe : Set (S.Atom () ()))
    (hs : FiniteLift.StrongClosedAmalgamation (FiniteLift.FullAut G M)
      (FiniteLift.aclSet (FiniteLift.FullAut G M)) (S.menuRel safe))
    (A0 : Set M) (finiteA : A0.Finite) (nonemptyA : A0.Nonempty) :
    ∃ W : Set M, AbsoluteWitness (G := G) S safe A0 W ∧
      FiniteLift.aclSet (FiniteLift.FullAut G M) W = W ∧
      ∀ (p : OrbitalPartial (G := G) (Subtype.val : W → M)),
        p.domain ⊆ {x | x.val ∈ A0} → (∀ x, p.map x ∈ {x | x.val ∈ A0}) →
        ∀ (x y : W) (Z : Set W),
          FiniteLift.Unsafe (fun a b : W => S.menuRel safe a.val b.val) Z →
          ∀ z ∈ Z, ∃ β τ α : OrbitalAut G M (Subtype.val : W → M),
            p.Extends β ∧ τ.val x = y ∧
              (∀ a ∈ Z, (α.val a).val ∈ FiniteLift.aclSet (FiniteLift.FullAut G M) A0) ∧
              (α.val z).val ∈ A0 := by
  obtain ⟨W,hW,hclosed,transitive⟩ := closed_transitive_witness S H cco safe hs A0 finiteA nonemptyA
  refine ⟨W,hW,hclosed,?_⟩
  intro p dom ran x y Z hZ z hz
  obtain ⟨β,hβ⟩ := hW.extensions p dom ran
  obtain ⟨τ,hτ⟩ := transitive x y
  obtain ⟨α,hα,hz'⟩ := hW.roots Z hZ z hz
  exact ⟨β,τ,α,hβ,hτ,hα,hz'⟩

end
end CCO.RankInduction
