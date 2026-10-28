import CCO.RealHull.Geometry.FibreFullness
import Mathlib.SetTheory.Cardinal.Finite

/-! A looped original fibre colour produces an arbitrarily large actual
clique over the same complete anchor. Finiteness therefore excludes it,
before any Ramsey or finite-fibre globalisation argument. -/

universe v w t
namespace CCO.RealHull.Canonical
open Geometry

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable [DecidableEq M] (A : Finset M) (q : ↥A → Atom S)
variable [Nonempty (FibreSet S A q)]
variable {G : Type t} [Group G] [MulAction G M]

theorem looped_fibre_clique (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (r : Atom S)
    (hr : ∀ a : ↥A, r ∈ square S (q a)) (hloop : r ∈ square S r)
    (n : ℕ) :
    ∃ f : Fin n → FibreSet S A q, Function.Injective f ∧
      ∀ i j, i ≠ j → col S (f i).val (f j).val = some r := by
  classical
  let c : InducedAtom S () (FibreSet S A q) :=
    ⟨r, fibre_pair_realize S A q H cco r hr⟩
  let D : CompleteDiagram (S := fibreSource S A q) (Fin n) := {
    diagram := {
      finite_type := inferInstance
      vertexSort := fun _ => ()
      edge := fun _ _ _ => some c
      edge_reverse := by
        intro x y h d
        simp only [(fibreSource S A q).symmetricLoop]
    }
    complete := by intro x y h; exact ⟨c, rfl⟩
  }
  have htri : FibreOriginalTriangles S A q D := by
    intro i j k hij hjk hik a b d ha hb hd
    have ha' : c = a := Option.some.inj ha
    have hb' : c = b := Option.some.inj hb
    have hd' : c = d := Option.some.inj hd
    subst a; subst b; subst d
    exact (mem_row S r r r).mp hloop
  obtain ⟨f, hf, he⟩ := original_complete_in_fibre S A q H cco D htri
  exact ⟨f, hf, fun i j hij => he i j hij c rfl⟩

theorem finite_fibre_excludes_looped (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) [Finite (FibreSet S A q)] :
    ∀ r : Atom S, (∀ a : ↥A, r ∈ square S (q a)) → r ∉ square S r := by
  intro r hr hloop
  obtain ⟨f, hf, _⟩ := looped_fibre_clique S A q H cco r hr hloop
    (Nat.card (FibreSet S A q) + 1)
  have hcard := Nat.card_le_card_of_injective f hf
  simp only [Nat.card_fin] at hcard
  exact Nat.not_succ_le_self _ hcard

end CCO.RealHull.Canonical
