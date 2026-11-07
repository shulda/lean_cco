import CCO.TerminalHiddenHN.RealRoots
import CCO.TerminalHiddenHN.OldTypeCodes
import CCO.TerminalHiddenHN.GenericCofinality
import CCO.TerminalHiddenHN.OrderedAge

/-! Readout orders live on the literal original real-generated closure.
The old induced map has a unique extension to that closure, obtained from
original homogeneity and the specified interpretation action. No SAP,
cover, CCO or hidden Ramsey assumption is used for these constructions. -/

universe u v w r l k
namespace CCO.TerminalHiddenHN.RealInterpretation
open CCO.UnaryFreshFrames
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : CCO.AtomicSource.{u,v,w} ι X}
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable {U : Language.{max u l}} {V : Type k} {P : Structure U V}
variable (D : RealInterpretation (G := G) S U P)

abbrev realClosure (A : CCO.FiniteInduced (X := X)) : Set V :=
  P.closure (D.realPoint '' A.vertices)

def closurePoint {A : CCO.FiniteInduced (X := X)} (a : A.vertices) : D.realClosure A :=
  ⟨D.realPoint a.val,P.subset_closure _ ⟨a.val,a.property,rfl⟩⟩

def realClosurePiece (H : CCO.HomogeneousSource S G) (A : CCO.FiniteInduced (X := X)) :
    P.Piece :=
  ⟨D.realClosure A,finite_closure S H D _ (A.finite_vertices.image D.realPoint),
    P.closure_closed _⟩

/-- There are no new real roots in the generated support. -/
theorem realClosure_real_iff (A : CCO.FiniteInduced (X := X)) (p : Sigma X) :
    D.realPoint p ∈ D.realClosure A ↔ p ∈ A.vertices := by
  rw [D.closure_real_iff _ (D.sort_realPoint p)]
  exact D.realPoint_injective.mem_set_image

/-- The only readout datum is an actual global linear order. -/
structure ReadoutOn (A : CCO.FiniteInduced (X := X)) where
  order : LinearOrder (D.realClosure A)

/-- Canonical closure maps retain the SAME original point map. -/
structure ClosureLift (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B) where
  embedding : (D.realClosurePiece H A).Embedding (D.realClosure B)
  root_eq : ∀ a : A.vertices, embedding.point (D.closurePoint a) =
    D.realPoint (e.toEmbedding a).val

private theorem embedding_eval (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)}
    (f : (D.realClosurePiece H A).Embedding (D.realClosure B))
    {s t : U.Sorts} (q : Term U s t) (x : D.realClosure A) :
    f.point ⟨P.eval q x.val,P.eval_mem_closed (P.closure_closed _) q x.property⟩ =
      P.eval q (f.point x) := by
  induction q with
  | id => rfl
  | func F q ih =>
    exact (f.func_eq F _).trans (congrArg (P.func F) ih)

/-- Any two induced closure maps with the same marked old roots coincide. -/
theorem closureLift_unique (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} {e : CCO.InducedEmbedding S A B}
    (f g : D.ClosureLift H e) : f = g := by
  have he : f.embedding = g.embedding := by
    cases f with | mk f hf =>
     cases g with | mk g hg =>
      have hp : f.point = g.point := by
        funext x
        obtain ⟨z,⟨a,ha,rfl⟩,t,q,hq⟩ := x.property
        have hx : x = ⟨P.eval q (D.realPoint a),
            P.eval_mem_closed (P.closure_closed _) q (D.closurePoint ⟨a,ha⟩).property⟩ :=
          Subtype.ext hq.symm
        rw [hx]
        exact (D.embedding_eval H f q (D.closurePoint ⟨a,ha⟩)).trans
          ((congrArg (P.eval q) ((hf ⟨a,ha⟩).trans (hg ⟨a,ha⟩).symm)).trans
            (D.embedding_eval H g q (D.closurePoint ⟨a,ha⟩)).symm)
      cases f; cases g; cases hp; rfl
  cases f; cases g; cases he; rfl

private theorem motion_mem_closure {A B : CCO.FiniteInduced (X := X)}
    (e : CCO.InducedEmbedding S A B) (g : G)
    (hg : ∀ a : A.vertices, g • a.val = (e.toEmbedding a).val)
    (x : D.realClosure A) : (D.motion g) • x.val ∈ D.realClosure B := by
  obtain ⟨z,⟨a,ha,rfl⟩,t,q,hq⟩ := x.property
  rw [← hq,P.aut_eval]
  have hr : (D.motion g) • D.realPoint a = D.realPoint (e.toEmbedding ⟨a,ha⟩).val :=
    (D.realPoint_smul g a).symm.trans (congrArg D.realPoint (hg ⟨a,ha⟩))
  rw [hr]
  exact P.eval_mem_closed (P.closure_closed _) q (D.closurePoint (e.toEmbedding ⟨a,ha⟩)).property

/-- Original finite homogeneity supplies the extension; choice is removed
by `closureLift_unique`, not by adding an extension-provider premise. -/
def closureLift (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B) :
    D.ClosureLift H e := by
  let g := Classical.choose (H.extends_partial_iso A B e)
  have hg := Classical.choose_spec (H.extends_partial_iso A B e)
  exact {
    embedding := {
      point x := (D.motion g) • x.val
      mem_point := D.motion_mem_closure e g hg
      injective := fun x y h => Subtype.ext (MulAction.injective (D.motion g) h)
      sort_eq x := P.aut_sort (D.motion g) x.val
      func_eq F x := P.aut_func (D.motion g) F x.val
      rel_iff R xs := P.aut_rel (D.motion g) R (Subtype.val ∘ xs) }
    root_eq := fun a => (D.realPoint_smul g a.val).symm.trans
      (congrArg D.realPoint (hg a)) }

def closureMap (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B) :
    D.realClosure A ↪ D.realClosure B where
  toFun x := ⟨(D.closureLift H e).embedding.point x,(D.closureLift H e).embedding.mem_point x⟩
  inj' x y h := (D.closureLift H e).embedding.injective (congrArg Subtype.val h)

@[simp] theorem closureMap_root (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B) (a : A.vertices) :
    D.closureMap H e (D.closurePoint a) = D.closurePoint (e.toEmbedding a) :=
  Subtype.ext ((D.closureLift H e).root_eq a)

/-- Comparison predicates retain arbitrary typed term pairs, including
same-root inputs. Both terms are evaluated on the literal old roots. -/
def termPoint {A : CCO.FiniteInduced (X := X)} {s t : U.Sorts}
    (q : Term U s t) (a : A.vertices) : D.realClosure A :=
  ⟨P.eval q (D.realPoint a.val),P.eval_mem_closed (P.closure_closed _) q (D.closurePoint a).property⟩

theorem closureMap_term (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B)
    {s t : U.Sorts} (q : Term U s t) (a : A.vertices) :
    D.closureMap H e (D.termPoint q a) = D.termPoint q (e.toEmbedding a) := by
  apply Subtype.ext
  exact (D.embedding_eval H (D.closureLift H e).embedding q (D.closurePoint a)).trans
    (congrArg (P.eval q) ((D.closureLift H e).root_eq a))

def TermComparison {A : CCO.FiniteInduced (X := X)} (a : D.ReadoutOn A)
    {s t j z : U.Sorts} (q : Term U s t) (p : Term U j z) (x y : A.vertices) : Prop :=
  @LT.lt _ a.order.toLT (D.termPoint q x) (D.termPoint p y)

structure ReadoutEmbedding (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (a : D.ReadoutOn A) (b : D.ReadoutOn B) where
  old : CCO.InducedEmbedding S A B
  lt_iff : ∀ x y, @LT.lt _ b.order.toLT (D.closureMap H old x) (D.closureMap H old y) ↔
    @LT.lt _ a.order.toLT x y

/-- Restriction along EVERY old embedding is the pullback of the exact
hidden order along its unique actual closure map. -/
def restrictReadout (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B) (b : D.ReadoutOn B) :
    D.ReadoutOn A := by
  letI : LinearOrder (D.realClosure B) := b.order
  exact ⟨LinearOrder.lift' (D.closureMap H e) (D.closureMap H e).injective⟩

def restrictReadoutEmbedding (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B) (b : D.ReadoutOn B) :
    D.ReadoutEmbedding H (D.restrictReadout H e b) b := ⟨e,fun _ _ => Iff.rfl⟩

theorem readout_comparison_iff (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (e : D.ReadoutEmbedding H a b) {s t j z : U.Sorts}
    (q : Term U s t) (p : Term U j z) (x y : A.vertices) :
    D.TermComparison b q p (e.old.toEmbedding x) (e.old.toEmbedding y) ↔
      D.TermComparison a q p x y := by
  change @LT.lt _ b.order.toLT _ _ ↔ _
  rw [← D.closureMap_term H e.old q x,← D.closureMap_term H e.old p y]
  exact e.lt_iff _ _

/-- Every source order extends along the SAME supplied original map. -/
theorem readout_reasonable (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B) (a : D.ReadoutOn A) :
    ∃ b : D.ReadoutOn B, D.restrictReadout H e b = a := by
  letI : Finite (D.realClosure B) := (D.realClosurePiece H B).finite.to_subtype
  letI : LinearOrder (D.realClosure A) := a.order
  obtain ⟨o,ho⟩ := CCO.TerminalHiddenHN.finite_linearOrder_extension (D.closureMap H e)
    (D.closureMap H e).injective
  refine ⟨⟨o⟩,?_⟩
  have he : (D.restrictReadout H e ⟨o⟩).order = a.order := by
    apply @LinearOrder.ext_lt (D.realClosure A) (D.restrictReadout H e ⟨o⟩).order a.order
    exact ho
  cases a
  exact congrArg ReadoutOn.mk he

/-- A finite closure has only finitely many actual order expansions. -/
theorem readout_precompact (H : CCO.HomogeneousSource S G) (A : CCO.FiniteInduced (X := X)) :
    Finite (D.ReadoutOn A) := by
  letI : Finite (D.realClosure A) := (D.realClosurePiece H A).finite.to_subtype
  apply Finite.of_injective (fun a : D.ReadoutOn A => fun x y => @LT.lt _ a.order.toLT x y)
  intro a b h
  cases a with | mk ao =>
    cases b with | mk bo =>
      congr 1
      apply LinearOrder.ext_lt
      intro x y
      exact iff_of_eq (congrFun (congrFun h x) y)


def oldEmbeddingId (A : CCO.FiniteInduced (X := X)) : CCO.InducedEmbedding S A A :=
  ⟨Function.Embedding.refl _,fun _ => rfl,fun _ _ => rfl⟩

def oldEmbeddingComp {A B C : CCO.FiniteInduced (X := X)}
    (g : CCO.InducedEmbedding S B C) (f : CCO.InducedEmbedding S A B) :
    CCO.InducedEmbedding S A C where
  toEmbedding := ⟨g.toEmbedding ∘ f.toEmbedding,g.toEmbedding.injective.comp f.toEmbedding.injective⟩
  preserves_sort x := (g.preserves_sort _).trans (f.preserves_sort x)
  preserves_colours x y := (f.preserves_colours x y).trans (g.preserves_colours _ _)

@[simp] theorem closureMap_id (H : CCO.HomogeneousSource S G)
    (A : CCO.FiniteInduced (X := X)) (x : D.realClosure A) :
    D.closureMap H (oldEmbeddingId A) x = x := by
  let f : D.ClosureLift H (oldEmbeddingId A) :=
    ⟨Structure.Piece.Embedding.identity _,fun _ => rfl⟩
  exact Subtype.ext (congrArg (fun h => h.embedding.point x)
    (D.closureLift_unique H (D.closureLift H _) f))

@[simp] theorem closureMap_comp (H : CCO.HomogeneousSource S G)
    {A B C : CCO.FiniteInduced (X := X)}
    (g : CCO.InducedEmbedding S B C) (f : CCO.InducedEmbedding S A B) (x : D.realClosure A) :
    D.closureMap H (oldEmbeddingComp g f) x =
      D.closureMap H g (D.closureMap H f x) := by
  let fg : D.ClosureLift H (oldEmbeddingComp g f) := {
    embedding := (D.closureLift H g).embedding.comp (D.closureLift H f).embedding
    root_eq := by
      intro a
      change (D.closureLift H g).embedding.point (D.closureMap H f (D.closurePoint a)) = _
      rw [D.closureMap_root]
      exact (D.closureLift H g).root_eq _ }
  exact Subtype.ext (congrArg (fun h => h.embedding.point x)
    (D.closureLift_unique H (D.closureLift H _) fg))

namespace ReadoutEmbedding
variable {D}

def id (H : CCO.HomogeneousSource S G) {A : CCO.FiniteInduced (X := X)} (a : D.ReadoutOn A) :
    D.ReadoutEmbedding H a a :=
  ⟨oldEmbeddingId A,by intro x y; rw [D.closureMap_id,D.closureMap_id]⟩

def comp (H : CCO.HomogeneousSource S G) {A B C : CCO.FiniteInduced (X := X)}
    {a : D.ReadoutOn A} {b : D.ReadoutOn B} {c : D.ReadoutOn C}
    (g : D.ReadoutEmbedding H b c) (f : D.ReadoutEmbedding H a b) :
    D.ReadoutEmbedding H a c :=
  ⟨oldEmbeddingComp g.old f.old,by
    intro x y
    rw [D.closureMap_comp,D.closureMap_comp]
    exact (g.lt_iff _ _).trans (f.lt_iff x y)⟩

@[ext] theorem ext (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    {f g : D.ReadoutEmbedding H a b} (h : f.old = g.old) : f = g := by
  cases f; cases g; cases h; rfl

end ReadoutEmbedding

/-- The underlying partial model retains every original cylinder and
function domain on the literal closure; only the order is added. -/
def readoutPartialModel (A : CCO.FiniteInduced (X := X)) :
    CCO.UnarySupport.Structure D.signature (D.realClosure A) :=
  D.partialModel.induce (D.realClosure A) ((D.codeModel_closed_iff _).mpr (P.closure_closed _))

def readoutModel {A : CCO.FiniteInduced (X := X)} (a : D.ReadoutOn A) :
    CCO.FullCode.Structure D.orderedLanguage (D.realClosure A) :=
  @CCO.TerminalHiddenHN.orderedStructure D.signature D.binary _ (D.readoutPartialModel A) a.order

theorem code_func_iff (F : U.Func) (x y : V) :
    y ∈ D.partialModel.func F x ↔ P.sort x = U.input F ∧ y = P.func F x := by
  classical
  letI := D.finiteSorts
  letI := D.finiteFuncs
  letI := D.finiteRels
  change y ∈ (if P.sort x = U.input F then {P.func F x} else ∅) ↔ _
  by_cases hs : P.sort x = U.input F <;> simp [hs]

/-- Literal inducedness includes reflection of the whole partial domain. -/
def closurePartialEmbedding (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B) :
    CCO.UnarySupport.Structure.Embedding (D.readoutPartialModel A) (D.readoutPartialModel B) where
  point := D.closureMap H e
  injective := (D.closureMap H e).injective
  sort_eq x := (D.closureLift H e).embedding.sort_eq x
  map_func F x y hy := by
    have hh := (D.code_func_iff F x.val y.val).mp hy
    apply (D.code_func_iff F _ _).mpr
    refine ⟨((D.closureLift H e).embedding.sort_eq x).trans hh.1,?_⟩
    have hm := (D.closureLift H e).embedding.func_eq F x
    have he : y = (D.realClosurePiece H A).func F x := Subtype.ext hh.2
    exact (congrArg (D.closureLift H e).embedding.point he).trans hm
  reflect_func F x y hy := by
    have hh := (D.code_func_iff F _ _).mp hy
    let z := (D.realClosurePiece H A).func F x
    refine ⟨z,(D.code_func_iff F x.val z.val).mpr ⟨?_,rfl⟩,?_⟩
    · exact ((D.closureLift H e).embedding.sort_eq x).symm.trans hh.1
    · apply Subtype.ext
      exact ((D.closureLift H e).embedding.func_eq F x).trans hh.2.symm
  map_rel R xs h := ((D.closureLift H e).embedding.rel_iff R xs).mpr h
  reflect_rel R xs h := ((D.closureLift H e).embedding.rel_iff R xs).mp h

namespace ReadoutEmbedding
variable {D}

/-- The ordered hidden extension uses exactly the old map's unique
closure extension and the same order comparisons. -/
def toHidden (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (e : D.ReadoutEmbedding H a b) :
    CCO.FullCode.Structure.Embedding (D.readoutModel a) (D.readoutModel b) := by
  letI : LinearOrder (D.realClosure A) := a.order
  letI : LinearOrder (D.realClosure B) := b.order
  exact CCO.TerminalHiddenHN.orderedEmbedding D.signature D.binary
    ⟨D.closurePartialEmbedding H e.old,e.lt_iff⟩

end ReadoutEmbedding


/-- Every named real point of the literal closure is one UNIQUE old
marked root. Erased or duplicate real roots are not introduced. -/
theorem realClosure_original (A : CCO.FiniteInduced (X := X))
    (x : D.realClosure A) {i : ι} (hi : P.sort x.val = D.realSort i) :
    ∃! a : A.vertices, D.closurePoint a = x := by
  obtain ⟨z,hz⟩ := D.realPoint_surjective_on_sort i x.val hi
  have hmem : (⟨i,z⟩ : Sigma X) ∈ A.vertices :=
    (D.realClosure_real_iff A ⟨i,z⟩).mp (hz.symm ▸ x.property)
  refine ⟨⟨⟨i,z⟩,hmem⟩,Subtype.ext hz,?_⟩
  intro b hb
  apply Subtype.ext
  exact D.realPoint_injective ((congrArg Subtype.val hb).trans hz.symm)

private theorem hidden_real_sort {A B : CCO.FiniteInduced (X := X)}
    {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (f : CCO.FullCode.Structure.Embedding (D.readoutModel a) (D.readoutModel b)) (x : A.vertices) :
    P.sort (f.point (D.closurePoint x)).val = D.realSort x.val.1 :=
  (f.sort_eq _).trans (D.sort_realPoint x.val)

def hiddenOldPoint {A B : CCO.FiniteInduced (X := X)}
    {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (f : CCO.FullCode.Structure.Embedding (D.readoutModel a) (D.readoutModel b)) (x : A.vertices) :
    B.vertices := Classical.choose (D.realClosure_original B _ (D.hidden_real_sort f x))

@[simp] theorem hiddenOldPoint_spec {A B : CCO.FiniteInduced (X := X)}
    {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (f : CCO.FullCode.Structure.Embedding (D.readoutModel a) (D.readoutModel b)) (x : A.vertices) :
    D.closurePoint (D.hiddenOldPoint f x) = f.point (D.closurePoint x) :=
  (Classical.choose_spec (D.realClosure_original B _ (D.hidden_real_sort f x))).1

theorem hiddenOldPoint_sort {A B : CCO.FiniteInduced (X := X)}
    {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (f : CCO.FullCode.Structure.Embedding (D.readoutModel a) (D.readoutModel b)) (x : A.vertices) :
    (D.hiddenOldPoint f x).val.1 = x.val.1 := by
  apply D.realSort.injective
  exact (D.sort_realPoint _).symm.trans
    ((congrArg (fun z : D.realClosure B => P.sort z.val) (D.hiddenOldPoint_spec f x)).trans
      (D.hidden_real_sort f x))

theorem hiddenOldPoint_injective {A B : CCO.FiniteInduced (X := X)}
    {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (f : CCO.FullCode.Structure.Embedding (D.readoutModel a) (D.readoutModel b)) :
    Function.Injective (D.hiddenOldPoint f) := by
  intro x y h
  have he := (D.hiddenOldPoint_spec f x).symm.trans
    ((congrArg D.closurePoint h).trans (D.hiddenOldPoint_spec f y))
  have hr := congrArg Subtype.val (f.injective he)
  exact Subtype.ext (D.realPoint_injective hr)

private theorem hiddenOld_rel_iff {A B : CCO.FiniteInduced (X := X)}
    {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (f : CCO.FullCode.Structure.Embedding (D.readoutModel a) (D.readoutModel b))
    (R : U.Rel) (xs : Fin (U.arity R) → A.vertices) :
    P.rel R (fun n => D.realPoint (D.hiddenOldPoint f (xs n)).val) ↔
      P.rel R (fun n => D.realPoint (xs n).val) := by
  letI : LinearOrder (D.realClosure A) := a.order
  letI : LinearOrder (D.realClosure B) := b.order
  let e := CCO.TerminalHiddenHN.orderedEmbeddingInverse D.signature D.binary f
  have he : (fun n => D.realPoint (D.hiddenOldPoint f (xs n)).val) =
      fun n => (f.point (D.closurePoint (xs n))).val := by
    funext n
    exact congrArg Subtype.val (D.hiddenOldPoint_spec f (xs n))
  rw [he]
  exact ⟨e.reflect_rel R (fun n => D.closurePoint (xs n)),
    e.map_rel R (fun n => D.closurePoint (xs n))⟩

private theorem taggedColour_of_binary_codes (p q p' q' : Sigma X)
    (hp : p'.1 = p.1) (hq : q'.1 = q.1)
    (hr : ∀ R : U.Rel,
      P.rel R (fun n => if n.val = 0 then D.realPoint p' else D.realPoint q') ↔
        P.rel R (fun n => if n.val = 0 then D.realPoint p else D.realPoint q)) :
    CCO.taggedColour S p q = CCO.taggedColour S p' q' := by
  rcases p with ⟨i,x⟩; rcases q with ⟨j,y⟩
  rcases p' with ⟨i',x'⟩; rcases q' with ⟨j',y'⟩
  change i' = i at hp
  change j' = j at hq
  subst i'; subst j'
  have hc : ∀ aa : S.Atom i j, S.colour x' y' = some aa ↔ S.colour x y = some aa := by
    intro aa
    exact (D.atom_iff aa x' y').symm.trans ((hr (D.atom aa)).trans (D.atom_iff aa x y))
  have hh : S.colour x y = S.colour x' y' := by
    cases hxy : S.colour x y with
    | some aa => exact ((hc aa).mpr hxy).symm
    | none =>
      cases hxy' : S.colour x' y' with
      | none => rfl
      | some aa =>
        have bad := (hc aa).mp hxy'
        rw [hxy] at bad
        cases bad
  exact congrArg (fun o => (⟨i,j,o⟩ : Σ i, Σ j, Option (S.Atom i j))) hh

def hiddenOldEmbedding {A B : CCO.FiniteInduced (X := X)}
    {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (f : CCO.FullCode.Structure.Embedding (D.readoutModel a) (D.readoutModel b)) :
    CCO.InducedEmbedding S A B where
  toEmbedding := ⟨D.hiddenOldPoint f,D.hiddenOldPoint_injective f⟩
  preserves_sort := D.hiddenOldPoint_sort f
  preserves_colours x y := by
    change CCO.taggedColour S x.val y.val =
      CCO.taggedColour S (D.hiddenOldPoint f x).val (D.hiddenOldPoint f y).val
    apply D.taggedColour_of_binary_codes _ _ _ _
      (D.hiddenOldPoint_sort f x) (D.hiddenOldPoint_sort f y)
    intro R
    simpa only [apply_ite] using D.hiddenOld_rel_iff f R (fun n => if n.val = 0 then x else y)


private theorem hidden_func_eq {A B : CCO.FiniteInduced (X := X)}
    {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (f : CCO.FullCode.Structure.Embedding (D.readoutModel a) (D.readoutModel b))
    (F : U.Func) (x : D.realClosure A) :
    (f.point ⟨P.func F x.val,(P.closure_closed _) F x.val x.property⟩).val =
      P.func F (f.point x).val := by
  classical
  by_cases hs : P.sort x.val = U.input F
  · have hmem := (D.code_func_iff F x.val (P.func F x.val)).mpr ⟨hs,rfl⟩
    exact (D.code_func_iff F _ _).mp (f.map_func F x
      ⟨P.func F x.val,(P.closure_closed _) F x.val x.property⟩ hmem) |>.2
  · have ht : P.sort (f.point x).val ≠ U.input F := by
      intro he; exact hs ((f.sort_eq x).symm.trans he)
    have hh : (⟨P.func F x.val,(P.closure_closed _) F x.val x.property⟩ : D.realClosure A) = x :=
      Subtype.ext (P.func_offsort F x.val hs)
    rw [hh,P.func_offsort F _ ht]

private def hiddenClosureLift (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (f : CCO.FullCode.Structure.Embedding (D.readoutModel a) (D.readoutModel b)) :
    D.ClosureLift H (D.hiddenOldEmbedding f) := by
  letI : LinearOrder (D.realClosure A) := a.order
  letI : LinearOrder (D.realClosure B) := b.order
  let e := CCO.TerminalHiddenHN.orderedEmbeddingInverse D.signature D.binary f
  exact {
    embedding := {
      point x := (f.point x).val
      mem_point x := (f.point x).property
      injective := fun x y h => f.injective (Subtype.ext h)
      sort_eq := f.sort_eq
      func_eq := D.hidden_func_eq f
      rel_iff R xs := ⟨e.reflect_rel R xs,e.map_rel R xs⟩ }
    root_eq x := (congrArg Subtype.val (D.hiddenOldPoint_spec f x)).symm }

theorem hidden_point_eq_closureMap (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (f : CCO.FullCode.Structure.Embedding (D.readoutModel a) (D.readoutModel b)) (x : D.realClosure A) :
    f.point x = D.closureMap H (D.hiddenOldEmbedding f) x :=
  Subtype.ext (congrArg (fun h => h.embedding.point x)
    (D.closureLift_unique H (D.hiddenClosureLift H f) (D.closureLift H _)))

def readoutEmbedding_of_hidden (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (f : CCO.FullCode.Structure.Embedding (D.readoutModel a) (D.readoutModel b)) :
    D.ReadoutEmbedding H a b := by
  letI : LinearOrder (D.realClosure A) := a.order
  letI : LinearOrder (D.realClosure B) := b.order
  let e := CCO.TerminalHiddenHN.orderedEmbeddingInverse D.signature D.binary f
  refine ⟨D.hiddenOldEmbedding f,?_⟩
  intro x y
  rw [← D.hidden_point_eq_closureMap H f x,← D.hidden_point_eq_closureMap H f y]
  exact e.order_iff x y

@[ext] theorem oldEmbedding_ext {A B : CCO.FiniteInduced (X := X)}
    {e f : CCO.InducedEmbedding S A B} (h : ∀ x, e.toEmbedding x = f.toEmbedding x) : e = f := by
  have he : e.toEmbedding = f.toEmbedding := Function.Embedding.ext h
  cases e; cases f; cases he; rfl

/-- Marked hidden extensions and readout embeddings are bijective on the
SAME point maps, without choosing a different actual real presentation. -/
def readoutHiddenEquiv (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (a : D.ReadoutOn A) (b : D.ReadoutOn B) :
    D.ReadoutEmbedding H a b ≃
      CCO.FullCode.Structure.Embedding (D.readoutModel a) (D.readoutModel b) where
  toFun e := e.toHidden H
  invFun := D.readoutEmbedding_of_hidden H
  left_inv e := by
    apply ReadoutEmbedding.ext
    apply oldEmbedding_ext
    intro x
    apply Subtype.ext
    apply D.realPoint_injective
    exact (congrArg Subtype.val (D.hiddenOldPoint_spec (e.toHidden H) x)).trans
      (congrArg Subtype.val (D.closureMap_root H e.old x))
  right_inv f := by
    apply CCO.FullCode.Structure.Embedding.ext
    intro x
    exact (D.hidden_point_eq_closureMap H f x).symm

theorem readout_toHidden_comp (H : CCO.HomogeneousSource S G)
    {A B C : CCO.FiniteInduced (X := X)}
    {a : D.ReadoutOn A} {b : D.ReadoutOn B} {c : D.ReadoutOn C}
    (g : D.ReadoutEmbedding H b c) (f : D.ReadoutEmbedding H a b) :
    (g.comp H f).toHidden H = (g.toHidden H).comp (f.toHidden H) := by
  apply CCO.FullCode.Structure.Embedding.ext
  exact D.closureMap_comp H g.old f.old

end
end CCO.TerminalHiddenHN.RealInterpretation
