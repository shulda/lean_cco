import CCO.TerminalHiddenHN.InterpretationFunctions
import CCO.TerminalHiddenHN.FiniteOrderExtension
import CCO.UnaryFreshFrames.Age
import Mathlib.Tactic.Choose

/-! Literal real closure and cofinality for the structural interpretation.
Every hidden vertex is covered by an actual onto real-source term, and
the generated finite cover stays induced in the SAME ambient structure.
No SAP, NR2, infinite-cover, CCO or Ramsey premise is used here. -/

universe u v w r l k
namespace CCO.TerminalHiddenHN
open CCO.UnaryFreshFrames

variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable {U : Language.{max u l}} {V : Type k} {P : Structure U V}

namespace RealInterpretation
variable (D : RealInterpretation (G := G) S U P)

/-- A term ending in a real sort is the identity on its actual domain.
The intermediate input need not itself be declared real in advance. -/
theorem eval_real_identity {s t : U.Sorts} (q : Term U s t)
    {x : V} (hx : P.sort x = s) {i : ι} (ht : t = D.realSort i) :
    P.eval q x = x := by
  induction q generalizing i with
  | id => rfl
  | func F q ih =>
    have hf := D.primitive_real_identity F i ht
    have hs : U.input F = D.realSort i := by
      have hsort := P.func_sort F (P.eval q x) (P.eval_sort q hx)
      rw [hf] at hsort
      exact (P.eval_sort q hx).symm.trans (hsort.trans ht)
    exact (hf (P.eval q x)).trans (ih hs)

/-- The literal real vertices of the supplied ambient interpretation. -/
def realPoints : Set V := {x | ∃ i, P.sort x = D.realSort i}

/-- Unary closure creates no new real vertex, even from a set that
already contains orphan hidden points. -/
theorem closure_real_iff (A : Set V) {y : V} {i : ι}
    (hy : P.sort y = D.realSort i) : y ∈ P.closure A ↔ y ∈ A := by
  constructor
  · rintro ⟨x,hx,t,q,hq⟩
    have ht : t = D.realSort i :=
      (P.eval_sort q rfl).symm.trans ((congrArg P.sort hq).trans hy)
    have he : x = y := (D.eval_real_identity q rfl ht).symm.trans hq
    exact he ▸ hx
  · intro hy
    exact P.subset_closure A hy

theorem closure_inter_realPoints (A : Set V) :
    P.closure A ∩ D.realPoints = A ∩ D.realPoints := by
  ext y
  constructor
  · rintro ⟨hy,hr⟩
    obtain ⟨i,hi⟩ := hr
    exact ⟨(D.closure_real_iff A hi).mp hy,⟨i,hi⟩⟩
  · rintro ⟨hy,hr⟩
    exact ⟨P.subset_closure A hy,hr⟩

/-- The source real-root closure equation, including the empty set. -/
theorem closure_realPoints (A : Set V) (hA : A ⊆ D.realPoints) :
    P.closure A ∩ D.realPoints = A := by
  rw [D.closure_inter_realPoints A]
  exact Set.inter_eq_left.mpr hA

theorem closure_root_iff (A : Set V) (i : ι) (x : X i) :
    (D.root i x).val ∈ P.closure A ↔ (D.root i x).val ∈ A :=
  D.closure_real_iff A (D.root i x).property

theorem closureAt_root_realPart (i : ι) (x : X i) :
    P.closureAt (D.root i x).val ∩ D.realPoints = {(D.root i x).val} := by
  apply D.closure_realPoints
  intro y hy
  subst y
  exact ⟨i,(D.root i x).property⟩

/-- Every actual hidden point has one actual original real preimage.
No representative is required to be fresh, distinct or canonical. -/
theorem real_root_covers (b : V) :
    ∃ i, ∃ x : X i, b ∈ P.closureAt (D.root i x).val := by
  obtain ⟨i,q,hq⟩ := D.projection (P.sort b)
  obtain ⟨x,hx⟩ := hq ⟨b,rfl⟩
  refine ⟨i,x,?_⟩
  have hm := P.typedEval_mem_closureAt q (D.root i x)
  have he : (P.typedEval q (D.root i x)).val = b := congrArg Subtype.val hx
  rw [he] at hm
  exact hm

/-- A cofinal cover is a literal real-generated finite closed subset
of the original ambient, containing the entire old piece. -/
structure RealCofinalCover (B : P.Piece) where
  generators : Set V
  finite_generators : generators.Finite
  real_generators : generators ⊆ D.realPoints
  contains : B.points ⊆ P.closure generators
  finite_closure : (P.closure generators).Finite

namespace RealCofinalCover
variable {D} {B : P.Piece} (C : D.RealCofinalCover B)

def piece : P.Piece :=
  ⟨P.closure C.generators,C.finite_closure,P.closure_closed C.generators⟩

def inclusion : B.Embedding C.piece.points :=
  Structure.Piece.Embedding.inclusion C.contains

@[simp] theorem inclusion_point (x : B.points) : C.inclusion.point x = x.val := rfl

theorem real_part : C.piece.points ∩ D.realPoints = C.generators :=
  D.closure_realPoints C.generators C.real_generators

/-- In particular the old real part is retained among the generators. -/
theorem old_real_mem {x : V} (hx : x ∈ B.points) (hr : x ∈ D.realPoints) :
    x ∈ C.generators := by
  rw [← C.real_part]
  exact ⟨C.contains hx,hr⟩

/-- Every supplied old order extends on this SAME finite cover,
preserving and reflecting the exact literal inclusion. -/
theorem order_extension [oldOrder : LinearOrder B.points] :
    ∃ o : LinearOrder C.piece.points, ∀ x y : B.points,
      @LT.lt C.piece.points o.toLT
        ⟨x.val,C.contains x.property⟩ ⟨y.val,C.contains y.property⟩ ↔
          @LT.lt B.points oldOrder.toLT x y := by
  letI : Finite (P.closure C.generators) := C.finite_closure.to_subtype
  exact finite_subset_inclusion_order_extension (oldOrder := oldOrder) C.contains

end RealCofinalCover

/-- Construct the literal cofinal cover of EVERY actual finite hidden
piece, including pieces with no internal original real generators. -/
noncomputable def cofinalCover (H : HomogeneousSource S G) (B : P.Piece) :
    D.RealCofinalCover B := by
  classical
  choose i x hx using fun b : B.points => D.real_root_covers b.val
  let rep : B.points → V := fun b => (D.root (i b) (x b)).val
  let A : Set V := Set.range rep
  have hA : A.Finite := Set.finite_range rep
  refine ⟨A,hA,?_,?_,RealInterpretation.finite_closure S H D A hA⟩
  · rintro y ⟨b,rfl⟩
    exact ⟨i b,(D.root (i b) (x b)).property⟩
  · intro b hb
    let z : B.points := ⟨b,hb⟩
    have hsub : ({rep z} : Set V) ⊆ A := by
      intro y hy
      exact hy ▸ ⟨z,rfl⟩
    exact P.closure_mono hsub (hx z)

/-- Ordered cofinality is on the same chosen real-generated cover,
through the literal inclusion of the entire original piece. -/
theorem ordered_cofinal_cover (H : HomogeneousSource S G) (B : P.Piece)
    [oldOrder : LinearOrder B.points] :
    ∃ C : D.RealCofinalCover B, ∃ o : LinearOrder C.piece.points,
      ∀ x y : B.points,
        @LT.lt C.piece.points o.toLT
          ⟨x.val,C.contains x.property⟩ ⟨y.val,C.contains y.property⟩ ↔
            @LT.lt B.points oldOrder.toLT x y := by
  let C := D.cofinalCover H B
  obtain ⟨o,ho⟩ := C.order_extension
  exact ⟨C,o,ho⟩

/-- Standalone C08: exact real closure, literal finite induced
cofinality, and extension of every old order use only A02 and original
pair homogeneity. The constructed inclusion is Subtype.val. -/
theorem real_root_closure_cofinal (H : HomogeneousSource S G) :
    (∀ A : Set V, A ⊆ D.realPoints → P.closure A ∩ D.realPoints = A) ∧
      ∀ B : P.Piece, Nonempty (D.RealCofinalCover B) :=
  ⟨D.closure_realPoints,fun B => ⟨D.cofinalCover H B⟩⟩

end RealInterpretation
end CCO.TerminalHiddenHN
