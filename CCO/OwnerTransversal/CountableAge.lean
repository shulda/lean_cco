import Mathlib.ModelTheory.Fraisse
import Mathlib.ModelTheory.DirectLimit

/-! An internal finite-chart Fraïssé construction.  The inputs are genuine
finite structures, their embeddings, and JEP/AP.  No ambient source or
homogeneous-limit provider is an input. -/

open scoped FirstOrder
open FirstOrder FirstOrder.Language CategoryTheory Set

universe u v
namespace CCO.OwnerTransversal.CountableAge

variable (L : FirstOrder.Language.{u,v})

/-- A countable catalogue of actual finite structures.  Isomorphic copies
of chart substructures are represented, and amalgams remain in the catalogue. -/
structure Data where
  Chart : Type
  [countableChart : Countable Chart]
  [nonemptyChart : Nonempty Chart]
  Carrier : Chart → Type
  [finiteCarrier : ∀ i, Finite (Carrier i)]
  [structureCarrier : ∀ i, L.Structure (Carrier i)]
  hereditary : ∀ (A : Type) [L.Structure A] [Finite A] (i : Chart),
    (A ↪[L] Carrier i) → ∃ j : Chart, Nonempty (A ≃[L] Carrier j)
  joint : ∀ i j : Chart, ∃ k : Chart,
    Nonempty (Carrier i ↪[L] Carrier k) ∧ Nonempty (Carrier j ↪[L] Carrier k)
  amalgamate : ∀ (i j k : Chart) (f : Carrier i ↪[L] Carrier j)
    (g : Carrier i ↪[L] Carrier k),
    ∃ (q : Chart) (fj : Carrier j ↪[L] Carrier q) (gk : Carrier k ↪[L] Carrier q),
      fj.comp f = gk.comp g

attribute [instance] Data.countableChart Data.nonemptyChart Data.finiteCarrier Data.structureCarrier

namespace Data
variable {L} (D : Data L)

/-- An actual embedding whose finite extension must eventually be realized. -/
structure Request where
  source : D.Chart
  target : D.Chart
  map : D.Carrier source ↪[L] D.Carrier target

instance finiteEmbedding (i j : D.Chart) : Finite (D.Carrier i ↪[L] D.Carrier j) :=
  Finite.of_injective (fun f : D.Carrier i ↪[L] D.Carrier j => (f : D.Carrier i → D.Carrier j))
    (fun _ _ h => DFunLike.ext' h)

instance : Countable D.Request := by
  classical
  exact Function.Injective.countable
    (f := fun r : D.Request => (⟨r.source,r.target,r.map⟩ : Σ i j, D.Carrier i ↪[L] D.Carrier j))
    (by intro a b h; cases a; cases b; cases h; rfl)

instance : Nonempty D.Request := by
  let i : D.Chart := Classical.choice inferInstance
  exact ⟨⟨i,i,Embedding.refl L _⟩⟩

/-- A finite family of extension requests into one chart has a common
actual amalgam.  AP is used successively, retaining all earlier maps. -/
theorem amalgamate_finite {I : Type} (s : Finset I) (r : I → D.Request)
    (c : D.Chart) (e : ∀ i, D.Carrier (r i).source ↪[L] D.Carrier c) :
    ∃ (q : D.Chart) (f : D.Carrier c ↪[L] D.Carrier q),
      ∀ i ∈ s, ∃ g : D.Carrier (r i).target ↪[L] D.Carrier q,
        g.comp (r i).map = f.comp (e i) := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨c,Embedding.refl L _,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨q,f,hf⟩ := ih
    obtain ⟨z,a,b,hab⟩ := D.amalgamate (r i).source (r i).target q
      (r i).map (f.comp (e i))
    refine ⟨z,b.comp f,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ⟨a,by simpa only [Embedding.comp_assoc] using hab⟩
    · obtain ⟨g,hg⟩ := hf j hj
      exact ⟨b.comp g,by rw [Embedding.comp_assoc,hg,Embedding.comp_assoc]⟩

/-- Every genuine finite embedding is listed, including identity and empty-base requests. -/
noncomputable def requests : ℕ → D.Request :=
  (exists_surjective_nat D.Request).choose

theorem requests_surjective : Function.Surjective D.requests :=
  (exists_surjective_nat D.Request).choose_spec

/-- The actual result of a finite round. -/
structure Round (c : D.Chart) (n : ℕ) where
  target : D.Chart
  map : D.Carrier c ↪[L] D.Carrier target
  realizes : ∀ i : Fin (n+1), ∀ e : D.Carrier (D.requests i).source ↪[L] D.Carrier c,
    ∃ g : D.Carrier (D.requests i).target ↪[L] D.Carrier target,
      g.comp (D.requests i).map = map.comp e

/-- At round n, every embedding of the first n request bases into the
CURRENT finite stage is handled.  Older embeddings compose into that stage. -/
theorem round_nonempty (c : D.Chart) (n : ℕ) : Nonempty (D.Round c n) := by
  classical
  let I := Σ i : Fin (n+1), D.Carrier (D.requests i).source ↪[L] D.Carrier c
  let (i : Fin (n+1)) : Fintype (D.Carrier (D.requests i).source ↪[L] D.Carrier c) :=
    Fintype.ofFinite _
  let : Fintype I := inferInstance
  obtain ⟨q,f,hf⟩ := D.amalgamate_finite (Finset.univ : Finset I)
    (fun i => D.requests i.1) c (fun i => i.2)
  exact ⟨⟨q,f,fun i e => hf ⟨i,e⟩ (Finset.mem_univ _)⟩⟩

noncomputable def next (c : D.Chart) (n : ℕ) : D.Round c n :=
  Classical.choice (D.round_nonempty c n)

/-- The chain of finite stages; all successors are actual AP amalgams. -/
noncomputable def stage : ℕ → D.Chart
  | 0 => Classical.choice inferInstance
  | n+1 => (D.next (stage n) n).target

noncomputable def step (n : ℕ) : D.Carrier (D.stage n) ↪[L] D.Carrier (D.stage (n+1)) :=
  (D.next (D.stage n) n).map

noncomputable def chain (i j : ℕ) (h : i ≤ j) :
    D.Carrier (D.stage i) ↪[L] D.Carrier (D.stage j) :=
  DirectedSystem.natLERec D.step i j h

instance : DirectedSystem (fun i => D.Carrier (D.stage i))
    (fun i j h => D.chain i j h) :=
  DirectedSystem.natLERec.directedSystem D.step

/-- The required at-most-countable union, formed from actual structures
and injective embeddings rather than from a consistent table axiom. -/
noncomputable abbrev Limit := FirstOrder.Language.DirectLimit (fun i => D.Carrier (D.stage i)) D.chain

noncomputable instance : L.Structure D.Limit := inferInstance

instance : Countable D.Limit := by
  let f : (Σ i : ℕ, D.Carrier (D.stage i)) → D.Limit :=
    Quotient.mk (DirectLimit.setoid D.chain)
  have hf : Function.Surjective f := by
    intro x
    exact ⟨x.out,Quotient.out_eq x⟩
  exact hf.countable

noncomputable def intoLimit (i : ℕ) : D.Carrier (D.stage i) ↪[L] D.Limit :=
  DirectLimit.of L ℕ (fun i => D.Carrier (D.stage i)) D.chain i

@[simp] theorem intoLimit_chain (i j : ℕ) (h : i ≤ j) (x : D.Carrier (D.stage i)) :
    D.intoLimit j (D.chain i j h x) = D.intoLimit i x :=
  DirectLimit.of_f

/-- Every finite tuple in the limit already lies in one actual finite stage. -/
theorem finite_embedding_factors (A : Type) [L.Structure A] [Finite A]
    (e : A ↪[L] D.Limit) :
    ∃ (i : ℕ) (f : A ↪[L] D.Carrier (D.stage i)), (D.intoLimit i).comp f = e := by
  classical
  obtain ⟨i,f,hf⟩ := DirectLimit.exists_quotient_mk'_sigma_mk'_eq
    (fun i => D.Carrier (D.stage i)) D.chain (fun a => e a)
  have hpoint : ∀ a, D.intoLimit i (f a) = e a := by
    intro a
    exact (congrFun hf a).symm
  let f' : A ↪[L] D.Carrier (D.stage i) := {
    toFun := f
    inj' := by
      intro a b h
      apply e.injective
      rw [← hpoint a,← hpoint b,h]
    map_fun' := by
      intro n F x
      apply (D.intoLimit i).injective
      rw [hpoint,e.map_fun,Embedding.map_fun]
      congr 1
      funext a
      exact (hpoint (x a)).symm
    map_rel' := by
      intro n R x
      rw [← (D.intoLimit i).map_rel]
      simpa only [Function.comp_def,hpoint] using e.map_rel R x }
  exact ⟨i,f',by ext a; exact hpoint a⟩

/-- Fairness of the finite rounds realizes every embedding-extension request. -/
theorem extension (r : D.Request) (e : D.Carrier r.source ↪[L] D.Limit) :
    ∃ g : D.Carrier r.target ↪[L] D.Limit, g.comp r.map = e := by
  obtain ⟨i,f,hf⟩ := D.finite_embedding_factors _ e
  obtain ⟨k,rfl⟩ := D.requests_surjective r
  let n := max i k
  have hi : i ≤ n := le_max_left _ _
  have hk : k < n+1 := Nat.lt_succ_of_le (le_max_right _ _)
  obtain ⟨g,hg⟩ := (D.next (D.stage n) n).realizes ⟨k,hk⟩ ((D.chain i n hi).comp f)
  let g' : D.Carrier (D.requests k).target ↪[L] D.Carrier (D.stage (n+1)) := g
  have hg' : g'.comp (D.requests k).map = (D.step n).comp ((D.chain i n hi).comp f) := hg
  refine ⟨(D.intoLimit (n+1)).comp g',?_⟩
  rw [Embedding.comp_assoc,hg']
  ext a
  change D.intoLimit (n+1) (D.step n (D.chain i n hi (f a))) = e a
  have hstep : D.chain n (n+1) (Nat.le_succ n) = D.step n := by
    ext x
    simp [chain,DirectedSystem.natLERec,Nat.leRecOn_succ,Nat.leRecOn_self]
  rw [← hstep,D.intoLimit_chain n (n+1) (Nat.le_succ n),D.intoLimit_chain i n hi]
  exact DFunLike.congr_fun hf a

/-- The actual finite structures represented by the chart catalogue. -/
def InAge (A : Type) [L.Structure A] : Prop :=
  ∃ i : D.Chart, Nonempty (A ≃[L] D.Carrier i)

/-- JEP and the extension property put every chart into the limit. -/
theorem chart_embeds (i : D.Chart) : Nonempty (D.Carrier i ↪[L] D.Limit) := by
  obtain ⟨q,⟨a⟩,⟨b⟩⟩ := D.joint (D.stage 0) i
  obtain ⟨g,_⟩ := D.extension ⟨D.stage 0,q,a⟩ (D.intoLimit 0)
  exact ⟨g.comp b⟩

/-- Unbounded actual finite charts force the constructed limit to be
infinite; the generic existence theorem itself also permits finite limits. -/
theorem infinite_of_unbounded
    (h : ∀ n : ℕ, ∃ i : D.Chart, Nonempty (Fin n ↪ D.Carrier i)) : Infinite D.Limit := by
  classical
  by_contra hn
  let : Finite D.Limit := not_infinite_iff_finite.mp hn
  let : Fintype D.Limit := Fintype.ofFinite _
  obtain ⟨i,⟨a⟩⟩ := h (Fintype.card D.Limit+1)
  have hh := Fintype.card_le_of_injective
    ((D.chart_embeds i).some ∘ a) ((D.chart_embeds i).some.injective.comp a.injective)
  simp at hh

/-- The union has exactly the prescribed finite age. -/
theorem finite_age (A : Type) [L.Structure A] [Finite A] :
    Nonempty (A ↪[L] D.Limit) ↔ D.InAge A := by
  constructor
  · rintro ⟨e⟩
    obtain ⟨i,f,_⟩ := D.finite_embedding_factors A e
    exact D.hereditary A (D.stage i) f
  · rintro ⟨i,⟨e⟩⟩
    exact ⟨(D.chart_embeds i).some.comp e.toEmbedding⟩

/-- A usual finite embedding-extension property, stated on arbitrary
actual finite structures rather than only the selected charts. -/
def ExtensionProperty (X : Type) [L.Structure X] : Prop :=
  ∀ (A B : Type) [L.Structure A] [L.Structure B] [Finite A] [Finite B],
    D.InAge B → ∀ (e : A ↪[L] X) (f : A ↪[L] B),
      ∃ g : B ↪[L] X, g.comp f = e

theorem extensionProperty : D.ExtensionProperty D.Limit := by
  intro A B _ _ _ _ hB e f
  obtain ⟨j,⟨b⟩⟩ := hB
  obtain ⟨i,⟨a⟩⟩ := D.hereditary A j (b.toEmbedding.comp f)
  let r : D.Request := ⟨i,j,(b.toEmbedding.comp f).comp a.symm.toEmbedding⟩
  obtain ⟨g,hg⟩ := D.extension r (e.comp a.symm.toEmbedding)
  refine ⟨g.comp b.toEmbedding,?_⟩
  ext x
  have h := DFunLike.congr_fun hg (a x)
  change g (b (f (a.symm (a x)))) = e (a.symm (a x)) at h
  change g (b (f x)) = e x
  simpa only [FirstOrder.Language.Equiv.symm_apply_apply] using h

/-- The chart class as a standard Mathlib class of bundled structures. -/
def ageClass : Set (Bundled.{0} L.Structure) := {A | D.InAge A}

/-- Isomorphic chart representatives are finite, including the empty case. -/
theorem inAge_finite (A : Type) [L.Structure A] (h : D.InAge A) : Finite A := by
  obtain ⟨i,⟨e⟩⟩ := h
  exact Finite.of_injective e e.injective

theorem age_eq [L.IsRelational] : L.age D.Limit = D.ageClass := by
  ext A
  constructor
  · rintro ⟨hfin,he⟩
    let : Finite A := hfin.finite
    exact (D.finite_age A).mp he
  · intro h
    let : Finite A := D.inAge_finite A h
    exact ⟨Structure.fg_iff_finite.mpr inferInstance,(D.finite_age A).mpr h⟩

section Homogeneous
variable [L.IsRelational]
variable {X Y : Type} [L.Structure X] [L.Structure Y]

/-- The finite extension property gives the actual one-point partial
isomorphism extension used by countable back-and-forth. -/
theorem isExtensionPair_of_extension
    (hX : L.age X = D.ageClass) (hY : D.ExtensionProperty Y) : L.IsExtensionPair X Y := by
  intro ⟨f,fFG⟩ x
  let S := f.dom ⊔ Substructure.closure L {x}
  have SFG : S.FG := fFG.sup (Substructure.fg_closure_singleton x)
  let : Finite f.dom := fFG.finite
  let : Finite S := SFG.finite
  have hS : D.InAge S := by
    change (⟨S,inferInstance⟩ : Bundled L.Structure) ∈ D.ageClass
    rw [← hX]
    exact ⟨(Substructure.fg_iff_structure_fg _).mp SFG,⟨S.subtype⟩⟩
  let old : f.dom ↪[L] Y := (Substructure.subtype f.cod).comp f.toEquiv.toEmbedding
  obtain ⟨g,hg⟩ := hY f.dom S hS old
    (Substructure.inclusion (le_sup_left : f.dom ≤ S))
  refine ⟨⟨⟨S,g.toHom.range,g.equivRange⟩,SFG⟩,?_,?_⟩
  · exact Substructure.subset_closure.trans
      (le_sup_right : Substructure.closure L {x} ≤ S) (Set.mem_singleton x)
  · refine ⟨le_sup_left,?_⟩
    ext a
    have hh := DFunLike.congr_fun hg a
    change g (Substructure.inclusion (le_sup_left : f.dom ≤ S) a) =
      (f.toEquiv a : Y)
    exact hh

/-- At-most-countable structures with the specified age and finite
extension property are ultrahomogeneous. -/
theorem homogeneous_of_extension [Countable X]
    (hAge : L.age X = D.ageClass) (hEP : D.ExtensionProperty X) :
    L.IsUltrahomogeneous X :=
  (isUltrahomogeneous_iff_IsExtensionPair Structure.cg_of_countable).mpr
    (D.isExtensionPair_of_extension hAge hEP)

/-- The internally constructed chain union is genuinely homogeneous. -/
theorem homogeneous : L.IsUltrahomogeneous D.Limit :=
  D.homogeneous_of_extension D.age_eq D.extensionProperty

/-- Existence is discharged by the construction above, rather than by
an external Fraïssé-limit premise. -/
theorem isFraisseLimit : IsFraisseLimit D.ageClass D.Limit :=
  ⟨D.homogeneous,D.age_eq⟩

/-- Countable back-and-forth uniqueness, allowing finite/empty limits. -/
theorem unique [Countable X]
    (hAge : L.age X = D.ageClass) (hEP : D.ExtensionProperty X) :
    Nonempty (D.Limit ≃[L] X) :=
  D.isFraisseLimit.nonempty_equiv ⟨D.homogeneous_of_extension hAge hEP,hAge⟩

end Homogeneous
end Data
end CCO.OwnerTransversal.CountableAge
