import CCO.RawExact.ExactBallHellySource
import CCO.RawExact.ExactSaturations
import CCO.RawExact.ActualOrbitalExact
import Mathlib.Logic.Function.Basic

/-!
# C24: triangle fullness of actual full-exact quotient orbital diagrams

The specified relations are complete ACTUAL original-group pair orbits.
Logical diagonals, reversal and distinct formal vertices are recorded
explicitly. Local triangle witnesses are transported by genuine original
group elements to the already chosen classes. Exact pulled-back orbitals
and the genuine source C13 theorem then add the next class. No SAP or
pre-existing quotient homogeneity/CCO is used.
-/

universe u v w z t r

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

private theorem finite_ball_helly_of_provider
    (hHelly : HeterogeneousExactBallHelly S)
    {I : Type z} [Finite I] {m : ι}
    (sort : I → ι) (D : ∀ i, NonemptyExact S m (sort i))
    (centres : ∀ i, X (sort i))
    (hPair : ∀ p q,
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty) :
    ∃ x : X m, ∀ i, evaluate S (D i).words x (centres i) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let e := Fintype.equivFin I
  obtain ⟨x, hx⟩ := hHelly (fun n => sort (e.symm n))
    (fun n => D (e.symm n)) (fun n => centres (e.symm n))
    (fun p q => hPair (e.symm p) (e.symm q))
  refine ⟨x, ?_⟩
  intro i
  obtain ⟨n, rfl⟩ := e.symm.surjective i
  exact hx n

/-- Exact quotient orbital requests with one common new quotient sort
satisfy finite 2-Helly. All relations are actual full pair orbitals,
not arbitrary invariant unions or fictitious quotient atoms. -/
theorem actual_quotient_request_helly_of_CCO
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {I : Type z} [Finite I] {m : ι}
    (A : Type v) [MulAction G A]
    (τ : X m → A) (ontoτ : Function.Surjective τ)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (E : NonemptyExact S m m)
    (hE : GroupActions.kernel τ = evaluate S E.words)
    (sort : I → ι) (Q : I → Type v) [∀ i, MulAction G (Q i)]
    (π : ∀ i, X (sort i) → Q i)
    (ontoπ : ∀ i, Function.Surjective (π i))
    (equivπ : ∀ i (g : G) x, π i (g • x) = g • π i x)
    (K : ∀ i, NonemptyExact S (sort i) (sort i))
    (hK : ∀ i, GroupActions.kernel (π i) = evaluate S (K i).words)
    (R : ∀ i, A → Q i → Prop)
    (hActual : ∀ i, ∃ a b, R i = GroupActions.orbital (G := G) a b)
    (centres : ∀ i, Q i)
    (hPair : ∀ p q, ∃ a : A, R p a (centres p) ∧ R q a (centres q)) :
    ∃ a : A, ∀ i, R i a (centres i) := by
  classical
  have hHelly : HeterogeneousExactBallHelly S :=
    heterogeneousExactBallHelly_of_CCO S H cco
  have hExact : ∀ i, ∃ D : NonemptyExact S m (sort i),
      evaluate S D.words = GroupActions.pullback τ (π i) (R i) := by
    intro i
    obtain ⟨a, b, hR⟩ := hActual i
    obtain ⟨x, rfl⟩ := ontoτ a
    obtain ⟨y, rfl⟩ := ontoπ i b
    obtain ⟨B, hB⟩ := actual_original_orbital_exact S H x y
    obtain ⟨D, hD⟩ := exact_actual_orbit_pullback_of_helly S H hHelly
      τ (π i) equivτ (equivπ i) E (K i) hE (hK i) x y B hB
    refine ⟨D, ?_⟩
    rw [hR]
    exact hD
  let D : ∀ i, NonemptyExact S m (sort i) := fun i => (hExact i).choose
  have hD : ∀ i, evaluate S (D i).words =
      GroupActions.pullback τ (π i) (R i) := fun i => (hExact i).choose_spec
  let b : ∀ i, X (sort i) := fun i => (ontoπ i (centres i)).choose
  have hb : ∀ i, π i (b i) = centres i :=
    fun i => (ontoπ i (centres i)).choose_spec
  have hBalls : ∀ p q,
      (ball (evaluate S (D p).words) (b p) ∩
        ball (evaluate S (D q).words) (b q)).Nonempty := by
    intro p q
    obtain ⟨a, hap, haq⟩ := hPair p q
    obtain ⟨x, rfl⟩ := ontoτ a
    refine ⟨x, ?_, ?_⟩
    · change evaluate S (D p).words x (b p)
      rw [hD p]
      change R p (τ x) (π p (b p))
      rwa [hb p]
    · change evaluate S (D q).words x (b q)
      rw [hD q]
      change R q (τ x) (π q (b q))
      rwa [hb q]
  obtain ⟨x, hx⟩ := finite_ball_helly_of_provider S hHelly sort D b hBalls
  refine ⟨τ x, ?_⟩
  intro i
  have h := hx i
  rw [hD i] at h
  change R i (τ x) (π i (b i)) at h
  rwa [hb i] at h

/-- A complete legal typed orbital diagram. Its labels name actual
G-pair orbits; diagonal equality and distinct-vertex separation are
logical constraints, not extra diversity colours. -/
structure ActualOrbitalDiagram (G : Type t) {K : Type z}
    (Q : K → Type v) [Group G] [∀ k, MulAction G (Q k)] (V : Type r) where
  sort : V → K
  relation : ∀ p q : V, Q (sort p) → Q (sort q) → Prop
  actual : ∀ p q, ∃ a b,
    relation p q = GroupActions.orbital (G := G) a b
  reverse : ∀ p q x y, relation p q x y ↔ relation q p y x
  diagonal : ∀ p x y, relation p p x y ↔ x = y
  separates : ∀ p q, p ≠ q → ∀ x y, relation p q x y →
    (⟨sort p, x⟩ : Sigma Q) ≠ ⟨sort q, y⟩

namespace ActualOrbitalDiagram

variable {G : Type t} [Group G] {K : Type z} {Q : K → Type v}
variable [∀ k, MulAction G (Q k)] {V : Type r}
variable (D : ActualOrbitalDiagram G Q V)

/-- All induced subdiagrams on at most three vertices are realizable.
Repeated indices retain the zero/one/two-vertex boundary cases. -/
def TrianglesLegal : Prop :=
  ∀ p q r, ∃ x y z,
    D.relation p q x y ∧ D.relation p r x z ∧ D.relation q r y z

theorem relation_invariant (p q : V) (g : G)
    (x : Q (D.sort p)) (y : Q (D.sort q))
    (h : D.relation p q x y) :
    D.relation p q (g • x) (g • y) := by
  obtain ⟨a, b, hR⟩ := D.actual p q
  rw [hR] at h ⊢
  exact GroupActions.orbital_invariant a b h g

theorem pair_transport (p q : V)
    (x x' : Q (D.sort p)) (y y' : Q (D.sort q))
    (h : D.relation p q x y) (h' : D.relation p q x' y') :
    GroupActions.orbital (G := G) x y x' y' := by
  obtain ⟨a, b, hR⟩ := D.actual p q
  rw [hR] at h h'
  rwa [GroupActions.orbital_eq_of_mem a b x y h] at h'

end ActualOrbitalDiagram

/-- C24 actual quotient triangle fullness. Every finite complete typed
diagram with all induced diagrams on at most three vertices in the
actual age has an injective realization in the actual quotient sorts.
Original semantic CCO and genuine full-exact kernels supply the entire
proof; no quotient homogeneity, quotient CCO or SAP is assumed. -/
theorem actual_quotient_triangle_fullness_of_CCO
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {K : Type z} (Q : K → Type v) [∀ k, MulAction G (Q k)]
    (root : K → ι) (π : ∀ k, X (root k) → Q k)
    (ontoπ : ∀ k, Function.Surjective (π k))
    (equivπ : ∀ k (g : G) c, π k (g • c) = g • π k c)
    (E : ∀ k, NonemptyExact S (root k) (root k))
    (hE : ∀ k, GroupActions.kernel (π k) = evaluate S (E k).words)
    {V : Type r} [Finite V] (D : ActualOrbitalDiagram G Q V)
    (hTriangles : D.TrianglesLegal) :
    ∃ point : ∀ p, Q (D.sort p),
      (∀ p q, D.relation p q (point p) (point q)) ∧
      Function.Injective (fun p => (⟨D.sort p, point p⟩ : Sigma Q)) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have hFinite : ∀ A : Finset V, ∃ point : ∀ p, Q (D.sort p),
      ∀ p ∈ A, ∀ q ∈ A, D.relation p q (point p) (point q) := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
        refine ⟨fun p => π (D.sort p)
          (Classical.choice (S.nonemptySort (root (D.sort p)))), ?_⟩
        intro p hp
        exact (Finset.notMem_empty p hp).elim
    | @insert n A hn ih =>
        obtain ⟨point, hPoint⟩ := ih
        let I := ↥A
        let R : ∀ p : I, Q (D.sort n) → Q (D.sort p.val) → Prop :=
          fun p => D.relation n p.val
        have hPair : ∀ p q : I, ∃ a : Q (D.sort n),
            R p a (point p.val) ∧ R q a (point q.val) := by
          intro p q
          obtain ⟨x, y, z, hnP, hnQ, hPQ⟩ := hTriangles n p.val q.val
          obtain ⟨g, hgy, hgz⟩ := D.pair_transport p.val q.val
            y (point p.val) z (point q.val) hPQ
            (hPoint p.val p.property q.val q.property)
          refine ⟨g • x, ?_, ?_⟩
          · have h := D.relation_invariant n p.val g x y hnP
            simpa only [hgy] using h
          · have h := D.relation_invariant n q.val g x z hnQ
            simpa only [hgz] using h
        obtain ⟨x, hx⟩ := actual_quotient_request_helly_of_CCO S H cco
          (Q (D.sort n)) (π (D.sort n)) (ontoπ (D.sort n))
          (equivπ (D.sort n)) (E (D.sort n)) (hE (D.sort n))
          (fun p : I => root (D.sort p.val))
          (fun p : I => Q (D.sort p.val))
          (fun p : I => π (D.sort p.val))
          (fun p : I => ontoπ (D.sort p.val))
          (fun p : I => equivπ (D.sort p.val))
          (fun p : I => E (D.sort p.val))
          (fun p : I => hE (D.sort p.val))
          R (fun p => D.actual n p.val) (fun p => point p.val) hPair
        let point' : ∀ p, Q (D.sort p) := Function.update point n x
        have hOld : ∀ p ∈ A, point' p = point p := by
          intro p hp
          have hpn : p ≠ n := by
            intro heq
            exact hn (heq ▸ hp)
          exact Function.update_of_ne hpn _ _
        refine ⟨point', ?_⟩
        intro p hp q hq
        rcases Finset.mem_insert.mp hp with hpn | hpA
        · subst p
          rcases Finset.mem_insert.mp hq with hqn | hqA
          · subst q
            exact (D.diagonal n _ _).mpr rfl
          · rw [hOld q hqA]
            simpa only [point', Function.update_self] using hx ⟨q, hqA⟩
        · rcases Finset.mem_insert.mp hq with hqn | hqA
          · subst q
            rw [hOld p hpA]
            apply (D.reverse p n _ _).mpr
            simpa only [point', Function.update_self] using hx ⟨p, hpA⟩
          · rw [hOld p hpA, hOld q hqA]
            exact hPoint p hpA q hqA
  obtain ⟨point, hPoint⟩ := hFinite Finset.univ
  have hAll : ∀ p q, D.relation p q (point p) (point q) :=
    fun p q => hPoint p (Finset.mem_univ p) q (Finset.mem_univ q)
  refine ⟨point, hAll, ?_⟩
  intro p q hpq
  by_contra hne
  exact D.separates p q hne (point p) (point q) (hAll p q) hpq

end CCO.RawExact
