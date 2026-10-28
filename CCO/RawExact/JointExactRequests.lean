import CCO.RawExact.ActualOrbitalExact

/-!
# C20 requests constructed from actual exact quotient kernels

All finite index universes are supported by reindexing through `Fin`.
Surjectivity chooses only the finitely many displayed representatives;
no equivariant or functorial section is used.
-/

universe u v w z q

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- The C20 mixed-request construction from the exact kernels of actual
equivariant quotient maps. The only open source provider is C13. -/
theorem joint_real_point_requests_of_exact_kernels
    {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G)
    (hHelly : HeterogeneousExactBallHelly S)
    {I : Type z} [Finite I] {m : ι}
    (sort : I → ι) (Q : I → Type q)
    [∀ t : I, MulAction G (Q t)]
    (π : ∀ t : I, X (sort t) → Q t)
    (ontoπ : ∀ t, Function.Surjective (π t))
    (equivπ : ∀ t (g : G) c, π t (g • c) = g • π t c)
    (K : ∀ t, NonemptyExact S (sort t) (sort t))
    (hK : ∀ t, GroupActions.kernel (π t) = evaluate S (K t).words)
    (x : X m) (source target : ∀ t : I, Q t)
    (hPairOrbit : ∀ p q : I,
      GroupActions.orbital (G := G)
        (source p) (source q) (target p) (target q)) :
    ∃ y : X m, ∀ t : I,
      GroupActions.orbital (G := G) x (source t) y (target t) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let e := Fintype.equivFin I
  let n := Fintype.card I
  let sort' : Fin n → ι := fun t => sort (e.symm t)
  let Q' : Fin n → Type q := fun t => Q (e.symm t)
  let π' : ∀ t : Fin n, X (sort' t) → Q' t :=
    fun t => π (e.symm t)
  let source' : ∀ t : Fin n, Q' t := fun t => source (e.symm t)
  let target' : ∀ t : Fin n, Q' t := fun t => target (e.symm t)
  have hExact : ∀ t : Fin n, ∃ D : NonemptyExact S m (sort' t),
      evaluate S D.words =
        GroupActions.pullback (fun y : X m => y) (π' t)
          (GroupActions.orbital (G := G) x (source' t)) := by
    intro t
    obtain ⟨c, hc⟩ := ontoπ (e.symm t) (source' t)
    obtain ⟨D, hD⟩ := exact_actual_request_of_helly S H hHelly
      (π (e.symm t)) (equivπ (e.symm t))
      (K (e.symm t)) (hK (e.symm t)) x c
    refine ⟨D, ?_⟩
    simpa only [hc] using hD
  let D : ∀ t : Fin n, NonemptyExact S m (sort' t) :=
    fun t => (hExact t).choose
  have hRequest : ∀ t : Fin n,
      evaluate S (D t).words =
        GroupActions.pullback (fun y : X m => y) (π' t)
          (GroupActions.orbital (G := G) x (source' t)) :=
    fun t => (hExact t).choose_spec
  let b : ∀ t : Fin n, X (sort' t) :=
    fun t => (ontoπ (e.symm t) (target' t)).choose
  have hb : ∀ t : Fin n, π' t (b t) = target' t :=
    fun t => (ontoπ (e.symm t) (target' t)).choose_spec
  have hPairs : ∀ p q : Fin n,
      GroupActions.orbital (G := G)
        (source' p) (source' q) (target' p) (target' q) :=
    fun p q => hPairOrbit (e.symm p) (e.symm q)
  obtain ⟨y, hy⟩ := joint_real_point_requests_of_ball_helly S
    sort' Q' π' x source' target' b hb hPairs D hRequest hHelly
  refine ⟨y, ?_⟩
  intro t
  obtain ⟨t', rfl⟩ := e.symm.surjective t
  exact hy t'

end CCO.RawExact
