import CCO.SafeReadings.SourceSelectors

/-! The literal maximum loop-palette size is positive as soon as one named
sort is present. Thus the quantitative source bound uses exactly max_t |P_tt|,
with no artificial lower cutoff and no CCO or safety assumption. -/
universe u v w z t r
namespace CCO.SafeReadings
open Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]

/-- A single actual named sort supplies a loop atom by homogeneous SAP. -/
theorem maxLoopPalette_eq_rawMax (H : HomogeneousSource S G) (sap : AgeSAP S) (i : ι) :
    maxLoopPalette S = S.finiteSort.elems.sup (fun t => Nat.card (S.Atom t t)) := by
  have hn : (Set.univ : S.Menu i i).Nonempty := (StrongExact.exact_top_of_SAP S H sap).1
  obtain ⟨a,_⟩ := hn
  have hc : 0 < Nat.card (S.Atom i i) :=
    Nat.card_pos_iff.mpr ⟨⟨a⟩, (S.finiteAtom i i).finite⟩
  have hle : Nat.card (S.Atom i i) ≤ S.finiteSort.elems.sup (fun t => Nat.card (S.Atom t t)) :=
    Finset.le_sup (f := fun t => Nat.card (S.Atom t t)) (S.finiteSort.complete i)
  exact max_eq_right (by omega)

variable {Λ : Type z} [Group Λ] [Finite Λ] {N : Type t} (A : PureTagAction S Λ N)

/-- The exact source maximum, counting iterations of the same parametric return. -/
theorem uniform_return_iterate_full_rawMax (H : HomogeneousSource S G) (sap : AgeSAP S)
    (primitive : SortwisePrimitive S) {i j : ι} {T : S.Menu i j → S.Menu i j}
    {g : Λ} {eps : Bool} (hT : UniformNormalForm S A T g eps true)
    (D : S.Menu i j) (hD : D.Nonempty) :
    T^[4 * Nat.card Λ * (S.finiteSort.elems.sup fun t => Nat.card (S.Atom t t))] D = Set.univ := by
  rw [← maxLoopPalette_eq_rawMax S H sap i]
  exact uniform_return_iterate_full_global S A (S.realPointGluing_of_SAP H sap)
    (S.realEdgeGluing_of_SAP H sap) H primitive hT D hD

/-- A positive path gives ONE operator with the literal maximum bound
for EVERY nonempty parallel raw input, including nonexact ones. -/
theorem positive_return_uniform_bound_rawMax (H : HomogeneousSource S G) (sap : AgeSAP S)
    (primitive : SortwisePrimitive S) {Q : Family S}
    (hne : ∀ {i j} {D : S.Menu i j}, (⟨i,j,D⟩ : TaggedMenu S) ∈ Q → D.Nonempty)
    {i j : ι} (D : S.Menu i j)
    (hpath : PositiveGenerated S A Q ⟨i,j,D⟩ ⟨i,j,D⟩ true) :
    ∃ (T : S.Menu i j → S.Menu i j) (g : Λ) (eps : Bool),
      UniformNormalForm S A T g eps true ∧ T D = D ∧
      ∀ E : S.Menu i j, E.Nonempty →
        T^[4 * Nat.card Λ * (S.finiteSort.elems.sup fun t => Nat.card (S.Atom t t))] E = Set.univ := by
  rw [← maxLoopPalette_eq_rawMax S H sap i]
  exact positive_return_uniform_bound S A (S.realPointGluing_of_SAP H sap)
    (S.realEdgeGluing_of_SAP H sap) H primitive hne D hpath

end CCO.SafeReadings
