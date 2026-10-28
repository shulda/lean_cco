import CCO.RealHull.Geometry.ClassFullAut
import CCO.RealHull.Geometry.ClassCCO
import CCO.RealHull.Geometry.ClassSizes

/-! Downstream actual-class consumers, independent of finite-fibre existence.
They become applicable to a fibre only AFTER that fibre has been shown to be
one global equivalence class. -/
universe u v w z t
namespace CCO.RealHull.Geometry
open ParityHasse.Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) (i : ι)

theorem equality_class_subsingleton (a : X i) :
    Subsingleton (ClassPoint S i (⊥ : ColourEq S i) a) := ⟨by
  intro x y
  apply Subtype.ext
  exact (show a = x.val from x.property).symm.trans y.property⟩

theorem equality_class_atom_empty (a : X i) :
    IsEmpty (InducedAtom S i {x | (⊥ : ColourEq S i) a x}) := ⟨by
  intro c
  obtain ⟨x,y,hc⟩ := c.property
  have hx : a = x.val := x.property
  have hy : a = y.val := y.property
  have hn : S.colour x.val y.val = none := by
    rw [← hx,← hy]
    exact (S.colour_none_iff a a).mpr rfl
  rw [hn] at hc
  cases hc⟩

variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]
variable (H : HomogeneousSource S G) (E : ColourEq S i) (a : X i)
include H

/-- All finite chains, and in fact all indexed families, have unique lifts in
the correct original interval. Global uniqueness outside this interval is not
asserted. The full order isomorphism preserves chain relations automatically.
-/
theorem class_family_lift_unique {J : Type z}
    (C : J → ColourEq (classSource S i E a) ()) :
    ∃! F : J → Set.Iic E, ∀ j, classRestrict S i E a (F j) = C j := by
  let e := classIntervalIso S i E a H
  refine ⟨fun j => e.symm (C j),fun j => e.apply_symm_apply (C j),?_⟩
  intro F hF
  funext j
  apply e.injective
  exact (hF j).trans (e.apply_symm_apply (C j)).symm

theorem class_full_family_lift_unique {J : Type z}
    (C : J → InducedFullEq S i {x | E a x}) :
    ∃! F : J → Set.Iic E, ∀ j, classFullIntervalIso S i H E a (F j) = C j := by
  let e := classFullIntervalIso S i H E a
  refine ⟨fun j => e.symm (C j),fun j => e.apply_symm_apply (C j),?_⟩
  intro F hF
  funext j
  exact e.injective ((hF j).trans (e.apply_symm_apply (C j)).symm)

noncomputable def liftClassChain {n : Nat}
    (C : Fin (n+1) → ColourEq (classSource S i E a) ()) : Fin (n+1) → Set.Iic E :=
  fun j => (classIntervalIso S i E a H).symm (C j)

theorem lifted_class_chain_strict {n : Nat}
    (C : Fin (n+1) → ColourEq (classSource S i E a) ()) (hC : StrictMono C) :
    StrictMono (liftClassChain S i H E a C) :=
  (classIntervalIso S i E a H).symm.strictMono.comp hC

theorem lifted_class_chain_indices {n : Nat}
    (C : Fin (n+1) → ColourEq (classSource S i E a) ())
    (j k : Fin (n+1)) (p : ClassPoint S i E a) :
    relativeIndex (liftClassChain S i H E a C j).val.val
      (liftClassChain S i H E a C k).val.val p.val =
      relativeIndex (C j).val (C k).val p := by
  have h := class_relativeIndex S i E a
    (liftClassChain S i H E a C j) (liftClassChain S i H E a C k) p
  have hj : classRestrict S i E a (liftClassChain S i H E a C j) = C j :=
    (classIntervalIso S i E a H).apply_symm_apply (C j)
  have hk : classRestrict S i E a (liftClassChain S i H E a C k) = C k :=
    (classIntervalIso S i E a H).apply_symm_apply (C k)
  rw [hj,hk] at h
  exact h

/-- One actual source statement tying full Aut class inheritance, arbitrary
formal-vertex CCO and the full original finite interval/size consumers. -/
theorem actual_class_package (cco : SemanticCCO.{u,v,0,w} S) :
    HomogeneousSource (classSource S i E a) (inducedAut S i {x | E a x}) ∧
    SemanticCCO.{0,v,z,w} (classSource S i E a) ∧
    Nonempty (Set.Iic E ≃o InducedFullEq S i {x | E a x}) ∧
    (Finite (ClassPoint S i E a) →
      ∃ n : Nat, Nat.card (ClassPoint S i E a) = 2^n ∧
        n ≤ Nat.card (InducedAtom S i {x | E a x})) := by
  refine ⟨class_homogeneous S i H E a,class_semanticCCO S i H cco E a,
    ⟨classFullIntervalIso S i H E a⟩,?_⟩
  intro hfin
  letI := hfin
  exact finite_class_size_power_two S i H cco E a

end CCO.RealHull.Geometry
