import CCO.FiniteFibres.Automorphisms
import CCO.FiniteFibres.AtomicAdapter
import CCO.FiniteFibres.Group.FiniteAction

/-! Generic finite real source support, ready to instantiate at the ACTUAL
B009 fibres. The full automorphism and palette bounds are proved here; no
conditional finite-size or Hasse provider is passed by a source consumer. -/
universe u v t
namespace CCO.FiniteFibres

variable {A : Type u} (S : AtomicSource.{0,u,v} Unit (fun _ => A)) [Finite A]
variable {G : Type t} [Group G] [MulAction G A] (H : HomogeneousSource S G)
include H

/-- Every finite homogeneous symmetric CCO source is a bounded power of two.
Homogeneity is used only to supply transitivity of the FULL target action;
the palette bound independently uses the actual bipartition bit code. -/
theorem finite_atomic_card (cco : CCO.SemanticCCO.{0,u,0,v} S) :
    ∃ m : Nat, Nat.card A = 2^m ∧ m ≤ Nat.card (S.Atom () ()) := by
  classical
  letI : Fintype A := Fintype.ofFinite _
  letI : Fintype (S.Atom () ()) := S.finiteAtom () ()
  let T := targetOfAtomic S
  have hcco : SemanticCCO T := targetOfAtomic_CCO S cco
  obtain ⟨k,hk⟩ := automorphism_two_group T hcco
  let a : Fin T.size := Fintype.equivFin A (Classical.choice (S.nonemptySort ()))
  obtain ⟨m,hm⟩ := Group.transitive_card_two_power hk (targetOfAtomic_transitive S H) a
  have hcard : Nat.card A = 2^m := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fin,targetOfAtomic,T] using hm
  refine ⟨m,hcard,?_⟩
  have hbound : Nat.card A ≤ 2 ^ Nat.card (S.Atom () ()) := by
    simpa only [T,targetOfAtomic,Nat.card_eq_fintype_card] using cardinal_le_palette T hcco
  rw [hcard] at hbound
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hbound

end CCO.FiniteFibres
