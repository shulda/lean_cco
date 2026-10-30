import CCO.FullPhaseLift.Boundary.FreeAmalgam
import CCO.FullPhaseLift.Canonical.FirstOrder
import Mathlib.Tactic.FinCases

/-! The genuine finite relational K₄³-free hypergraph class, in B048's
single normalized full-language representation. -/

universe u v
namespace CCO.FullPhaseLift.Boundary.HypergraphClass
open Canonical FreeAmalgam
noncomputable section

abbrev signature : Signature := ⟨1,fun _ => 3⟩

def tuple3 {V : Type u} (x y z : V) : Fin 3 → V :=
  Fin.cases x (Fin.cases y (fun _ => z))

theorem tuple3_eta {V : Type u} (xs : Fin 3 → V) :
    tuple3 (xs 0) (xs 1) (xs 2) = xs := by
  funext i
  fin_cases i <;> rfl

theorem tuple3_comp {V : Type u} {W : Type v} (f : V → W) (x y z : V) :
    f ∘ tuple3 x y z = tuple3 (f x) (f y) (f z) := by
  funext i
  fin_cases i <;> rfl

def table {V : Type u} (R : TripleRelation V) : BoolTable signature V := by
  classical
  exact fun _ xs => decide (R (xs 0) (xs 1) (xs 2))

def relation {V : Type u} (T : BoolTable signature V) : TripleRelation V :=
  fun x y z => T 0 (tuple3 x y z) = true

@[simp] theorem relation_table {V : Type u} (R : TripleRelation V) :
    relation (table R) = R := by
  classical
  funext x y z
  apply propext
  change decide (R x y z) = true ↔ R x y z
  exact decide_eq_true_iff

@[simp] theorem table_relation {V : Type u} (T : BoolTable signature V) :
    table (relation T) = T := by
  funext r xs
  fin_cases r
  simp only [table,relation,tuple3_eta,Bool.decide_coe]
  rfl

def Valid {V : Type u} (T : BoolTable signature V) : Prop :=
  NoRepeats (relation T) ∧ Symmetric (relation T) ∧ K4Free (relation T)

theorem embedding_relation {V : Type u} {W : Type v}
    {A : BoolTable signature V} {B : BoolTable signature W} (e : Embedding A B)
    (x y z : V) : relation B (e.point x) (e.point y) (e.point z) ↔ relation A x y z := by
  have h := embedding_read e 0 (tuple3 x y z)
  rw [tuple3_comp] at h
  exact congrArg (fun b : Bool => b = true) h |> Eq.to_iff

def relationEmbedding {V : Type u} {W : Type v}
    (RA : TripleRelation V) (RB : TripleRelation W) (f : V → W)
    (hf : Function.Injective f) (hr : ∀ x y z, RB (f x) (f y) (f z) ↔ RA x y z) :
    Embedding (table RA) (table RB) := by
  refine embeddingOf f hf ?_
  intro r xs
  fin_cases r
  simp only [table,Function.comp_apply]
  exact decide_eq_decide.mpr (hr _ _ _)

theorem Valid.of_embedding {V : Type u} {W : Type v}
    {A : BoolTable signature V} {B : BoolTable signature W} (e : Embedding A B)
    (hB : Valid B) : Valid A := by
  refine ⟨?_,?_,?_⟩
  · intro x y z h
    obtain ⟨hxy,hxz,hyz⟩ := hB.1 _ _ _ ((embedding_relation e x y z).mpr h)
    exact ⟨fun he => hxy (congrArg e.point he),fun he => hxz (congrArg e.point he),
      fun he => hyz (congrArg e.point he)⟩
  · constructor
    · intro x y z
      exact (embedding_relation e x y z).symm.trans
        ((hB.2.1.1 _ _ _).trans (embedding_relation e y x z))
    · intro x y z
      exact (embedding_relation e x y z).symm.trans
        ((hB.2.1.2 _ _ _).trans (embedding_relation e x z y))
  · intro f hf hc
    apply hB.2.2 (e.point ∘ f) (e.injective.comp hf)
    intro i j k hij hik hjk
    exact (embedding_relation e _ _ _).mpr (hc i j k hij hik hjk)

theorem empty_valid (V : Type u) : Valid (table (fun (_ _ _ : V) => False)) := by
  rw [Valid,relation_table]
  exact ⟨fun _ _ _ h => h.elim,⟨fun _ _ _ => Iff.rfl,fun _ _ _ => Iff.rfl⟩,
    empty_higher_allowed V⟩

theorem complete_three_valid : Valid (table (completeTriple (Fin 3))) := by
  rw [Valid,relation_table]
  refine ⟨fun _ _ _ h => h,?_,complete_three_allowed⟩
  constructor
  · intro x y z
    exact ⟨fun ⟨a,b,c⟩ => ⟨a.symm,c,b⟩,fun ⟨a,b,c⟩ => ⟨a.symm,c,b⟩⟩
  · intro x y z
    exact ⟨fun ⟨a,b,c⟩ => ⟨b,a,c.symm⟩,fun ⟨a,b,c⟩ => ⟨b,a,c.symm⟩⟩

/-- Actual strong amalgamation of the finite FULL class; all signed old
tuples are induced on both legs, and only displayed base points coincide. -/
theorem strong_amalgamate {A B C : Type u} [Finite A] [Finite B] [Finite C]
    (TA : BoolTable signature A) (TB : BoolTable signature B) (TC : BoolTable signature C)
    (hB : Valid TB) (hC : Valid TC) (s : Embedding TA TB) (t : Embedding TA TC) :
    ∃ (V : Type u) (_ : Finite V) (T : BoolTable signature V), Valid T ∧
      ∃ (l : Embedding TB T) (r : Embedding TC T),
        (∀ a, l.point (s.point a) = r.point (t.point a)) ∧
        ∀ b c, l.point b = r.point c → ∃ a, s.point a = b ∧ t.point a = c := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  letI : Fintype C := Fintype.ofFinite C
  let se : A ↪ B := ⟨s.point,s.injective⟩
  let te : A ↪ C := ⟨t.point,t.injective⟩
  let V := FreeAmalgam.Vertex se te
  letI : Finite V := by
    dsimp [V,FreeAmalgam.Vertex,CloneSAP.FiniteUnion.Union,CloneSAP.FiniteUnion.OffBase]
    infer_instance
  let R := FreeAmalgam.relation (relation TB) (relation TC) se te
  have hs : ∀ x y z, relation TB (se x) (se y) (se z) ↔ relation TA x y z :=
    embedding_relation s
  have ht : ∀ x y z, relation TC (te x) (te y) (te z) ↔ relation TA x y z :=
    embedding_relation t
  have hR : Valid (table R) := by
    rw [Valid,relation_table]
    exact ⟨FreeAmalgam.noRepeats _ _ se te hB.1 hC.1,
      FreeAmalgam.symmetric _ _ se te hB.2.1 hC.2.1,
      FreeAmalgam.k4Free (relation TA) _ _ se te hs ht hB.2.2 hC.2.2⟩
  let l : Embedding TB (table R) := by
    let raw := relationEmbedding (relation TB) R (FreeAmalgam.leftMap se te)
      (FreeAmalgam.leftMap se te).injective
      (FreeAmalgam.left_induced (relation TA) _ _ se te hs ht)
    refine embeddingOf (FreeAmalgam.leftMap se te) (FreeAmalgam.leftMap se te).injective ?_
    intro r xs
    have h := embedding_read raw r xs
    change table R r ((FreeAmalgam.leftMap se te) ∘ xs) = table (relation TB) r xs at h
    rw [table_relation] at h
    exact h
  let r : Embedding TC (table R) := by
    let raw := relationEmbedding (relation TC) R (FreeAmalgam.rightMap se te)
      (FreeAmalgam.rightMap se te).injective
      (FreeAmalgam.right_induced (relation TA) _ _ se te hs ht)
    refine embeddingOf (FreeAmalgam.rightMap se te) (FreeAmalgam.rightMap se te).injective ?_
    intro r xs
    have h := embedding_read raw r xs
    change table R r ((FreeAmalgam.rightMap se te) ∘ xs) = table (relation TC) r xs at h
    rw [table_relation] at h
    exact h
  refine ⟨V,inferInstance,table R,hR,l,r,?_,?_⟩
  · exact FreeAmalgam.commute se te
  · exact FreeAmalgam.strong_intersection se te

end
end CCO.FullPhaseLift.Boundary.HypergraphClass
