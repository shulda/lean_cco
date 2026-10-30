import CCO.APCharacter.SourceAge.UnarySourceHomogeneity
import CCO.APCharacter.MarkedSource
import CCO.APCharacter.Rank.Consumer

/-! The actual homogeneous character split discharges every rank hypothesis.
The child palettes are the literal occurring old names in the SAME original
carriers; there is no supplied rank/colour-loss/whole-homogeneity callback. -/
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace CCO.APCharacter.SourceAge.CharacterRank
open RigidGroupoid.Geometry RigidGroupoid.Phase
open UnarySource
open scoped BigOperators
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}
variable (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (I : Identification S H (P.completion_property cco))

def activeParents (_P : SourcePhase S H C A) : Finset ι := by
  classical
  letI := S.finiteSort
  exact Finset.univ.filter (fun i => Nonempty (Bridge S A i))

theorem mem_active (i : ι) : i ∈ activeParents P ↔ Nonempty (Bridge S A i) := by
  classical
  simp [activeParents]

theorem active_nonempty : (activeParents P).Nonempty :=
  ⟨r,(mem_active P r).mpr ⟨(Arrow.id A).toBridge⟩⟩

def activeBitEquiv {i : ι} (hi : Nonempty (Bridge S A i)) : β I i ≃ Bit where
  toFun := Subtype.val
  invFun ε := ⟨ε,fun hn => False.elim (hn hi)⟩
  left_inv x := Subtype.ext rfl
  right_inv _ := rfl

def inactiveBitEquiv {i : ι} (hi : ¬Nonempty (Bridge S A i)) : β I i ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨0,fun _ => rfl⟩
  left_inv x := Subtype.ext (x.property hi).symm
  right_inv x := by cases x; rfl

theorem active_card {i : ι} (hi : i ∈ activeParents P) : Fintype.card (β I i) = 2 := by
  have he := Fintype.card_congr (activeBitEquiv P cco I ((mem_active P i).mp hi))
  exact he.trans (ZMod.card 2)

theorem inactive_card {i : ι} (hi : i ∉ activeParents P) : Fintype.card (β I i) = 1 := by
  have hn : ¬Nonempty (Bridge S A i) := fun h => hi ((mem_active P i).mpr h)
  exact (Fintype.card_congr (inactiveBitEquiv P cco I hn)).trans Fintype.card_unit

theorem lost_colour {i : ι} (hi : i ∈ activeParents P) :
    ∃ a : S.Atom i i, ∀ b : β I i, ¬Rank.Occurs S (β I) (tag I) ⟨i,b⟩ ⟨i,b⟩ a := by
  let h := (mem_active P i).mp hi
  obtain ⟨a,_,ha⟩ := P.actual_lost_atom (⟨i,h⟩ : Reached S A)
  refine ⟨a,?_⟩
  intro b hex
  obtain ⟨x,y,hxy⟩ := hex
  have hallow := (global_marking I).2 (⟨i,x.val⟩ : Sigma X) (⟨i,y.val⟩ : Sigma X)
  have hx : mark I ⟨i,x.val⟩ = b.val := congrArg Subtype.val x.property
  have hy : mark I ⟨i,y.val⟩ = b.val := congrArg Subtype.val y.property
  rw [hxy,hx,hy] at hallow
  exact ha b.val hallow

theorem actual_rank_drop :
    letI := S.finiteSort
    Rank.potential (fun c : Rank.Child (β I) => Nat.card ((source I).Atom c c)) <
      Rank.potential (fun i => Nat.card (S.Atom i i)) := by
  letI := S.finiteSort
  have h := Rank.homogeneous_character_rank_drop S (β I) (tag I) (inhabited I)
    H (homogeneous I) (activeParents P) (active_nonempty P)
    (fun i hi => active_card P cco I hi)
    (fun i hi => inactive_card P cco I hi)
    (fun i hi => lost_colour P cco I hi)
  exact h.2.2.1.trans_lt h.2.2.2

end
end CCO.APCharacter.SourceAge.CharacterRank
