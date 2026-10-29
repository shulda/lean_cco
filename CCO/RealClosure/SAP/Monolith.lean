import CCO.RealClosure.SAP.InvariantLattice

/-! C21: one unique least nonidentity equivalence, directly from SAP.
The nonsymmetric ambient-action lattice is used throughout. -/
universe v w t
namespace CCO.RealClosure.SAP
variable {M : Type v} {G : Type t} [Group G] [MulAction G M]
namespace InvariantEq

def IsMonolith (L : InvariantEq G M) : Prop :=
  L ≠ ⊥ ∧ ∀ E : InvariantEq G M, E ≠ ⊥ → L ≤ E

theorem class_infinite (S : Source.{v,w} M) (H : S.Homogeneous (G := G))
    (sap : S.AgeSAP) {E : InvariantEq G M} (hE : E ≠ ⊥) (x : M) :
    Set.Infinite {y | E x y} := by
  exact (infinite_meet_class S H sap hE hE x).mono (fun _ h => h.1)

theorem meet_ne_bot (S : Source.{v,w} M) (H : S.Homogeneous (G := G))
    (sap : S.AgeSAP) [Nonempty M] {E F : InvariantEq G M}
    (hE : E ≠ ⊥) (hF : F ≠ ⊥) : E ⊓ F ≠ ⊥ := by
  intro he
  let x : M := Classical.choice inferInstance
  have hi := infinite_meet_class S H sap hE hF x
  rw [he] at hi
  exact hi (by simpa only [bot_apply,Set.setOf_eq_eq_singleton'] using Set.finite_singleton x)

theorem top_ne_bot [Infinite M] : (⊤ : InvariantEq G M) ≠ ⊥ := by
  intro h
  have hsub : Subsingleton M := ⟨fun x y => by
    have ht : (⊤ : InvariantEq G M) x y := trivial
    rw [h] at ht
    exact ht⟩
  letI := hsub
  exact not_finite M

theorem exists_monolith (S : Source.{v,w} M) (H : S.Homogeneous (G := G))
    (sap : S.AgeSAP) [Infinite M] :
    ∃ L : InvariantEq G M, IsMonolith L := by
  letI := finite S H
  obtain ⟨L,hL,hmin⟩ := wellFounded_lt.has_min
    {E : InvariantEq G M | E ≠ ⊥} ⟨⊤,top_ne_bot⟩
  refine ⟨L,hL,?_⟩
  intro E hE
  have hmeet : L ⊓ E = L := by
    apply le_antisymm inf_le_left
    by_contra hn
    exact hmin (L ⊓ E) (meet_ne_bot S H sap hL hE)
      (lt_of_le_of_ne inf_le_left (Ne.symm (ne_of_not_le hn)))
  rw [← hmeet]
  exact inf_le_right

def monolith : InvariantEq G M :=
  familyMeet (fun E : {E : InvariantEq G M // E ≠ ⊥} => E.val)

theorem monolith_le {E : InvariantEq G M} (hE : E ≠ ⊥) :
    (monolith : InvariantEq G M) ≤ E :=
  fun _ _ h => h ⟨E,hE⟩

theorem monolith_property (S : Source.{v,w} M) (H : S.Homogeneous (G := G))
    (sap : S.AgeSAP) [Infinite M] : IsMonolith (monolith : InvariantEq G M) := by
  obtain ⟨L,hL,hle⟩ := exists_monolith S H sap
  refine ⟨?_,fun _ hE => monolith_le hE⟩
  intro hm
  have hLm : L ≤ (monolith : InvariantEq G M) := le_familyMeet (fun E => hle E.val E.property)
  exact hL (le_antisymm (hm ▸ hLm) bot_le)

theorem monolith_unique {L K : InvariantEq G M} (hL : IsMonolith L)
    (hK : IsMonolith K) : L = K :=
  le_antisymm (hL.2 K hK.1) (hK.2 L hL.1)

theorem monolith_class_infinite (S : Source.{v,w} M) (H : S.Homogeneous (G := G))
    (sap : S.AgeSAP) [Infinite M] (x : M) :
    Set.Infinite {y | (monolith : InvariantEq G M) x y} :=
  class_infinite S H sap (monolith_property S H sap).1 x

/-- No nonidentity invariant equivalence has finite classes. This proves
that the greatest finite-class relation is real identity, without exactness. -/
theorem finite_class_iff_bot (S : Source.{v,w} M) (H : S.Homogeneous (G := G))
    (sap : S.AgeSAP) (E : InvariantEq G M) (x : M) :
    Set.Finite {y | E x y} ↔ E = ⊥ := by
  constructor
  · intro hf
    by_contra hn
    exact class_infinite S H sap hn x hf
  · rintro rfl
    simpa only [bot_apply,Set.setOf_eq_eq_singleton'] using Set.finite_singleton x

def IsInfiniteDirection (E : InvariantEq G M) : Prop :=
  (∀ x, Set.Infinite {y | E x y}) ∧
    ∀ F : InvariantEq G M, F < E → ∀ x, Set.Finite {y | F x y}

theorem direction_iff_monolith (S : Source.{v,w} M) (H : S.Homogeneous (G := G))
    (sap : S.AgeSAP) [Infinite M] (E : InvariantEq G M) :
    IsInfiniteDirection E ↔ E = (monolith : InvariantEq G M) := by
  have hm := monolith_property S H sap
  constructor
  · rintro ⟨hE,hmin⟩
    have hne : E ≠ ⊥ := by
      intro he
      have hi := hE (Classical.choice (inferInstance : Nonempty M))
      rw [he] at hi
      exact hi (by simpa only [bot_apply,Set.setOf_eq_eq_singleton'] using Set.finite_singleton _)
    apply le_antisymm ?_ (hm.2 E hne)
    by_contra hn
    have hlt : (monolith : InvariantEq G M) < E :=
      lt_of_le_of_ne (hm.2 E hne) (Ne.symm (ne_of_not_le hn))
    exact monolith_class_infinite S H sap (Classical.choice inferInstance)
      (hmin monolith hlt _)
  · rintro rfl
    refine ⟨monolith_class_infinite S H sap,?_⟩
    intro F hF x
    apply (finite_class_iff_bot S H sap F x).mpr
    by_contra hn
    exact not_le_of_gt hF (hm.2 F hn)

end InvariantEq
end CCO.RealClosure.SAP
