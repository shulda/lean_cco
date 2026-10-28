import CCO.ExactCRT.AbstractRelations
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! B008 C02–03: finite class Helly is exactly distributivity for a
binary sublattice of permuting represented equivalences. Ambient equality
and ambient top need not be members. -/

universe u
namespace CCO.ExactCRT.Abstract

variable {A : Type u} (S : Sublattice (Setoid A))

/-- The literal three-class proof of the difficult distributive inclusion. -/
theorem inf_sup_le_of_helly (comm : Commutes S) (helly : ClassHelly S)
    (E F G : S) : E ⊓ (F ⊔ G) ≤ (E ⊓ F) ⊔ (E ⊓ G) := by
  rintro x y ⟨hE, hFG⟩
  have hfg : comp F.val G.val x y := by
    rw [← join_eq_comp F.val G.val (comm F G)]
    exact hFG
  obtain ⟨z, hxz, hzy⟩ := hfg
  let rel : Fin 3 → S := ![E, F, G]
  let centre : Fin 3 → A := ![x, x, y]
  have hp : ∀ i j, ∃ w, (rel i).val (centre i) w ∧ (rel j).val (centre j) w := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact ⟨x, E.val.refl x, E.val.refl x⟩
    · exact ⟨x, E.val.refl x, F.val.refl x⟩
    · exact ⟨y, hE, G.val.refl y⟩
    · exact ⟨x, F.val.refl x, E.val.refl x⟩
    · exact ⟨x, F.val.refl x, F.val.refl x⟩
    · exact ⟨z, hxz, G.val.symm hzy⟩
    · exact ⟨y, G.val.refl y, hE⟩
    · exact ⟨z, G.val.symm hzy, hxz⟩
    · exact ⟨y, G.val.refl y, G.val.refl y⟩
  obtain ⟨w, hw⟩ := helly 3 rel centre hp
  have hew : E.val x w := hw 0
  have hfw : F.val x w := hw 1
  have hgyw : G.val y w := hw 2
  have hleft : (E ⊓ F).val x w := ⟨hew, hfw⟩
  have hright : (E ⊓ G).val w y := ⟨E.val.trans (E.val.symm hew) hE, G.val.symm hgyw⟩
  have hcomp : comp (E ⊓ F).val (E ⊓ G).val x y := ⟨w, hleft, hright⟩
  rw [← join_eq_comp (E ⊓ F).val (E ⊓ G).val (comm _ _)] at hcomp
  exact hcomp

/-- C02: no finiteness or ambient bounds are needed. -/
@[instance_reducible] def distribLattice_of_helly (comm : Commutes S) (helly : ClassHelly S) :
    DistribLattice S :=
  DistribLattice.ofInfSupLe (inf_sup_le_of_helly S comm helly)

def Distributive : Prop :=
  ∀ E F G : S, E ⊓ (F ⊔ G) ≤ E ⊓ F ⊔ E ⊓ G

theorem nonemptyInf_sup (dist : Distributive S) {n : Nat} (E : Fin (n+1) → S) (F : S) :
    nonemptyInf S (fun i => E i ⊔ F) = nonemptyInf S E ⊔ F := by
  let : DistribLattice S := DistribLattice.ofInfSupLe dist
  induction n with
  | zero => rfl
  | succ n ih =>
    change (E 0 ⊔ F) ⊓ nonemptyInf S (fun i : Fin (n+1) => E i.succ ⊔ F) =
      (E 0 ⊓ nonemptyInf S (fun i : Fin (n+1) => E i.succ)) ⊔ F
    rw [ih]
    exact (sup_inf_right _ _ _).symm

/-- C03: induction keeps the previous intersection nonempty and internal.
The zero/one cases use respectively inhabitedness/the actual centre. -/
theorem classHelly_of_distrib [Nonempty A] (comm : Commutes S)
    (dist : Distributive S) : ClassHelly S := by
  let : DistribLattice S := DistribLattice.ofInfSupLe dist
  intro n
  induction n with
  | zero =>
    intro E centre _
    obtain ⟨x⟩ := ‹Nonempty A›
    exact ⟨x, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro E centre hp
    cases n with
    | zero =>
      exact ⟨centre 0, fun i => by have hi : i = 0 := Fin.eq_zero i; subst i; exact (E 0).val.refl _⟩
    | succ n =>
      let tail : Fin (n+1) → S := fun i => E i.succ
      obtain ⟨z, hz⟩ := ih tail (fun i => centre i.succ) (fun i j => hp i.succ j.succ)
      let M : S := nonemptyInf S tail
      have hj : ∀ i : Fin (n+1), (tail i ⊔ E 0).val z (centre 0) := by
        intro i
        obtain ⟨p, h0p, hip⟩ := hp 0 i.succ
        have hzip : (tail i).val z p := (tail i).val.trans ((tail i).val.symm (hz i)) hip
        have hpr : comp (tail i).val (E 0).val z (centre 0) :=
          ⟨p, hzip, (E 0).val.symm h0p⟩
        rw [← join_eq_comp (tail i).val (E 0).val (comm _ _)] at hpr
        exact hpr
      have hjoin : (M ⊔ E 0).val z (centre 0) := by
        rw [show M ⊔ E 0 = nonemptyInf S (fun i => tail i ⊔ E 0) from (nonemptyInf_sup S dist tail (E 0)).symm]
        exact (nonemptyInf_rel S _ _ _).mpr hj
      have hm : comp M.val (E 0).val z (centre 0) := by
        rw [← join_eq_comp M.val (E 0).val (comm _ _)]
        exact hjoin
      obtain ⟨w, hzw, hw0⟩ := hm
      refine ⟨w, ?_⟩
      intro i
      refine Fin.cases ((E 0).val.symm hw0) (fun j => ?_) i
      have hjw := (nonemptyInf_rel S tail z w).mp hzw j
      exact (tail j).val.trans (hz j) hjw

/-- The first two source conditions are equivalent. -/
theorem distributive_iff_classHelly [Nonempty A] (comm : Commutes S) :
    Distributive S ↔ ClassHelly S :=
  ⟨classHelly_of_distrib S comm, fun helly => inf_sup_le_of_helly S comm helly⟩

end CCO.ExactCRT.Abstract
