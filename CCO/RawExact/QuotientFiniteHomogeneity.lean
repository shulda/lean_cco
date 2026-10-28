import CCO.RawExact.FiniteRealignment

/-!
# Finite tuple lifting on actual quotient sorts

Finite orbital graphs are converted to literal finite partial
isomorphisms, then lifted by the proved C21 source theorem. Repeated
source tuple values need no arbitrary representative convention: actual
pair orbitals force the selected graph values to agree.
-/

universe u v w z t r

namespace CCO.RawExact

namespace JointBackAndForth

variable {G : Type t} [Group G] {K : Type z} {Q : K → Type v}
variable [∀ k, MulAction G (Q k)]

/-- A genuine finite orbital graph determines an actual finite partial
isomorphism agreeing with EVERY graph row, including repeated sources. -/
theorem finite_map_of_graph (graph : Graph G Q) :
    ∃ f : FiniteJointPartialIso G Q, ∀ row ∈ graph.val,
      (⟨row.1, row.2.1⟩ : Sigma Q) ∈ f.domain ∧
      f.send ⟨row.1, row.2.1⟩ = row.2.2 := by
  classical
  let domain : Finset (Sigma Q) := graph.val.image (fun row => ⟨row.1, row.2.1⟩)
  have hRow : ∀ p ∈ domain, ∃ y : Q p.1,
      (⟨p.1, p.2, y⟩ : Row Q) ∈ graph.val := by
    intro p hp
    obtain ⟨row, hrow, heq⟩ := Finset.mem_image.mp hp
    cases row with
    | mk k pair =>
      cases pair with
      | mk x y =>
        subst p
        exact ⟨y, hrow⟩
  let send : ∀ p : Sigma Q, Q p.1 :=
    fun p => if hp : p ∈ domain then (hRow p hp).choose else p.2
  have hSend : ∀ p ∈ domain, (⟨p.1, p.2, send p⟩ : Row Q) ∈ graph.val := by
    intro p hp
    simpa only [send, dite_eq_left hp] using (hRow p hp).choose_spec
  have hPreserve : ∀ p q, p ∈ domain → q ∈ domain →
      GroupActions.orbital (G := G) p.2 q.2 (send p) (send q) := by
    intro p q hp hq
    exact graph.property _ (hSend p hp) _ (hSend q hq)
  refine ⟨⟨domain, send, hPreserve⟩, ?_⟩
  intro row hrow
  have hp : (⟨row.1, row.2.1⟩ : Sigma Q) ∈ domain :=
    Finset.mem_image.mpr ⟨row, hrow, rfl⟩
  refine ⟨hp, ?_⟩
  exact graph.functional row.1 row.2.1 (send ⟨row.1, row.2.1⟩) row.2.2
    (hSend _ hp) hrow

end JointBackAndForth

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Quotient-only finite maps are lifted by including their finite
domain in the proved real-plus-quotient source theorem. -/
theorem finite_quotient_group_lifting_of_CCO
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    [∀ i, Countable (X i)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {K : Type z} [Finite K]
    (Q : K → Type v) [∀ k, MulAction G (Q k)]
    (root : K → ι) (π : ∀ k, X (root k) → Q k)
    (ontoπ : ∀ k, Function.Surjective (π k))
    (equivπ : ∀ k (g : G) c, π k (g • c) = g • π k c)
    (E : ∀ k, NonemptyExact S (root k) (root k))
    (hE : ∀ k, GroupActions.kernel (π k) = evaluate S (E k).words)
    (f : FiniteJointPartialIso G Q) :
    ∃ h : G, ∀ p ∈ f.domain, h • p.2 = f.send p := by
  classical
  let embed : Sigma Q → Sigma (JointFamily X Q) := fun p => ⟨.inr p.1, p.2⟩
  let send : ∀ p : Sigma (JointFamily X Q), JointFamily X Q p.1 := fun p =>
    match p with
    | ⟨.inl _, x⟩ => x
    | ⟨.inr k, x⟩ => f.send ⟨k, x⟩
  let domain := f.domain.image embed
  have hPreserve : ∀ p q, p ∈ domain → q ∈ domain →
      GroupActions.orbital (G := G) p.2 q.2 (send p) (send q) := by
    intro p q hp hq
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
    exact f.preserves p' q' hp' hq'
  let joint : FiniteJointPartialIso G (JointFamily X Q) := ⟨domain, send, hPreserve⟩
  obtain ⟨h, hh⟩ := finite_joint_group_lifting_of_CCO S H cco
    Q root π ontoπ equivπ E hE joint
  refine ⟨h, ?_⟩
  intro p hp
  exact hh (embed p) (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

/-- Every finite actual quotient orbital graph is induced by ONE
original G-element, with the actual source C21 providers discharged. -/
theorem finite_quotient_graph_lifting_of_CCO
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    [∀ i, Countable (X i)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {K : Type z} [Finite K]
    (Q : K → Type v) [∀ k, MulAction G (Q k)]
    (root : K → ι) (π : ∀ k, X (root k) → Q k)
    (ontoπ : ∀ k, Function.Surjective (π k))
    (equivπ : ∀ k (g : G) c, π k (g • c) = g • π k c)
    (E : ∀ k, NonemptyExact S (root k) (root k))
    (hE : ∀ k, GroupActions.kernel (π k) = evaluate S (E k).words)
    (graph : JointBackAndForth.Graph G Q) :
    ∃ h : G, ∀ row ∈ graph.val, h • row.2.1 = row.2.2 := by
  obtain ⟨f, hf⟩ := JointBackAndForth.finite_map_of_graph graph
  obtain ⟨h, hh⟩ := finite_quotient_group_lifting_of_CCO S H cco
    Q root π ontoπ equivπ E hE f
  refine ⟨h, ?_⟩
  intro row hrow
  obtain ⟨hp, hsend⟩ := hf row hrow
  exact (hh ⟨row.1, row.2.1⟩ hp).trans hsend

/-- The arbitrary finite-tuple form includes repeated real/quotient
values and is exactly the interface needed for actual quotient source
homogeneity. No injection or tuple-realization provider is assumed. -/
theorem finite_quotient_tuple_lifting_of_CCO
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    [∀ i, Countable (X i)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {K : Type z} [Finite K]
    (Q : K → Type v) [∀ k, MulAction G (Q k)]
    (root : K → ι) (π : ∀ k, X (root k) → Q k)
    (ontoπ : ∀ k, Function.Surjective (π k))
    (equivπ : ∀ k (g : G) c, π k (g • c) = g • π k c)
    (E : ∀ k, NonemptyExact S (root k) (root k))
    (hE : ∀ k, GroupActions.kernel (π k) = evaluate S (E k).words)
    {I : Type r} [Finite I]
    (sort : I → K) (source target : ∀ i, Q (sort i))
    (hPair : ∀ i j, GroupActions.orbital (G := G)
      (source i) (source j) (target i) (target j)) :
    ∃ h : G, ∀ i, h • source i = target i := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let row : I → JointBackAndForth.Row Q :=
    fun i => ⟨sort i, source i, target i⟩
  let rows := Finset.univ.image row
  have hValid : ∀ p ∈ rows, ∀ q ∈ rows,
      GroupActions.orbital (G := G) p.2.1 q.2.1 p.2.2 q.2.2 := by
    intro p hp q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    exact hPair i j
  let graph : JointBackAndForth.Graph G Q := ⟨rows, hValid⟩
  obtain ⟨h, hh⟩ := finite_quotient_graph_lifting_of_CCO S H cco
    Q root π ontoπ equivπ E hE graph
  refine ⟨h, ?_⟩
  intro i
  exact hh (row i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

end CCO.RawExact
