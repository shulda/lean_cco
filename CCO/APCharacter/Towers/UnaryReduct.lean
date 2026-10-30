import CCO.APCharacter.Age.Category
import CCO.APCharacter.Towers.UnaryComposition
import CCO.APCharacter.SourceAge.BackAndForth
import Mathlib.Data.Finite.Sigma

/-! A literal unary refinement forgets to the original finite age by
its actual point/sort/colour projections. No new binary-name refinement
is hidden in the forgetful functor. -/
universe u v w
namespace CCO.APCharacter.Towers
open CategoryTheory OwnerTransversal.CountableColour
variable {ι κ : Type u} {X : ι → Type v} {Y : κ → Type v}
variable (S : AtomicSource.{u,v,w} ι X) (T : AtomicSource.{u,v,w} κ Y)

structure UnaryReduct where
  parent : κ → ι
  point : ∀ k, Y k → X (parent k)
  atom : ∀ k l, T.Atom k l → S.Atom (parent k) (parent l)
  atom_injective : ∀ k l, Function.Injective (atom k l)
  colour : ∀ k l (x : Y k) (y : Y l),
    S.colour (point k x) (point l y) = Option.map (atom k l) (T.colour x y)
  bijective : Function.Bijective (fun p : Sigma Y => (⟨parent p.1,point p.1 p.2⟩ : Sigma X))

namespace UnaryReduct
noncomputable section
variable {S T} (P : UnaryReduct S T)
def project (p : Sigma Y) : Sigma X := ⟨P.parent p.1,P.point p.1 p.2⟩

def ownerMap (b : Age.OwnerCode T) : Age.OwnerCode S :=
  Age.ownerEquiv S (P.parent ((Age.ownerEquiv T).symm b).1,0)

def colourMap (c : Age.ColourCode T) : Age.ColourCode S := by
  let x := (Age.colourEquiv T).symm c
  exact Age.colourEquiv S ⟨P.parent x.1,P.parent x.2.1,
    Option.map (P.atom x.1 x.2.1) x.2.2⟩

def mapTable {V : Type} (F : Age.Table T V) : Age.Table S V where
  owner x := P.ownerMap (F.owner x)
  colour x y := P.colourMap (F.colour x y)

theorem map_actual {V : Type} (point : V → Sigma Y) (bits : V → Bit) :
    P.mapTable (Age.table T point bits) =
      Age.table S (P.project ∘ point) (fun _ => 0) := by
  apply congrArg₂ Table.mk
  · funext x
    change Age.ownerEquiv S (P.parent ((Age.ownerEquiv T).symm
      (Age.ownerEquiv T ((point x).1,bits x))).1,0) = _
    rw [Equiv.symm_apply_apply]
    rfl
  · funext x y
    change P.colourMap (Age.colourEquiv T (taggedColour T (point x) (point y))) = _
    unfold colourMap
    dsimp only
    rw [Equiv.symm_apply_apply]
    apply congrArg (Age.colourEquiv S)
    change (⟨P.parent (point x).1,P.parent (point y).1,
      Option.map (P.atom _ _) (T.colour (point x).2 (point y).2)⟩ : Age.Colour S) = _
    rw [← P.colour]
    rfl

def object (C : Age.Chart T (Age.zeroMask T)) : Age.Chart S (Age.zeroMask S) where
  size := C.size
  table := P.mapTable C.table
  realized := by
    obtain ⟨p,b,hp,hl,he⟩ := C.realized
    rw [he]
    refine ⟨P.project ∘ p,(fun _ => 0),P.bijective.1.comp hp,
      ⟨fun _ => rfl,fun _ _ => ⟨rfl,rfl⟩⟩,?_⟩
    exact P.map_actual p b

def forget : Age.Chart T (Age.zeroMask T) ⥤ Age.Chart S (Age.zeroMask S) where
  obj := P.object
  map {C D} f := by
    letI := C.structure
    letI := D.structure
    have hn := C.table.embedding_preserves D.table f
    exact (P.object C).table.embedding (P.object D).table f.toEmbedding
      (fun x => congrArg P.ownerMap (hn.1 x))
      (fun x y => congrArg P.colourMap (hn.2 x y))
  map_id := by intro C; rfl
  map_comp := by intros; rfl

/-- On any fixed finite carrier only finitely many complete name tables
exist. This gives actual finite expansion fibres without global orbit
or source-cardinality assumptions. -/
theorem finite_size (M : MaskData T) (n : ℕ) :
    Finite {C : Age.Chart T M // C.size = n} := by
  let target := Σ i : {k : ℕ // k = n}, Age.Table T (Fin i.val)
  let code : {C : Age.Chart T M // C.size = n} → target :=
    fun C => ⟨⟨C.val.size,C.property⟩,C.val.table⟩
  apply Finite.of_injective code
  rintro ⟨⟨i,A,ha⟩,hi⟩ ⟨⟨j,B,hb⟩,hj⟩ h
  cases h
  rfl

theorem precompact : Precompact P.forget := by
  intro C
  letI := finite_size (Age.zeroMask T) C.size
  let code : {D : Age.Chart T (Age.zeroMask T) // P.forget.obj D = C} →
      {D : Age.Chart T (Age.zeroMask T) // D.size = C.size} :=
    fun D => ⟨D.val,congrArg Age.Chart.size D.property⟩
  apply Finite.of_injective code
  intro D E h
  exact Subtype.ext (congrArg (fun x : {D : Age.Chart T (Age.zeroMask T) // D.size = C.size} => x.val) h)

/-- The original table used by the actual source extension theorem. -/
def originalTable : Table ι (Age.Colour S) (Sigma X) where
  owner := Sigma.fst
  colour := taggedColour S

def projectedTable : Table ι (Age.Colour S) (Sigma Y) where
  owner p := (P.project p).1
  colour p q := taggedColour S (P.project p) (P.project q)

private theorem zero_table {S : AtomicSource.{u,v,w} ι X}
    (C : Age.Chart S (Age.zeroMask S)) :
    C.table = Age.table S C.point (fun _ => 0) := by
  have h : C.bits = (fun _ => 0) := funext C.legal.1
  exact C.table_eq.trans (congrArg (Age.table S C.point) h)

private theorem chart_ext {M : MaskData S} {A B : Age.Chart S M}
    (size : A.size = B.size) (table : HEq A.table B.table) : A = B := by
  cases A
  cases B
  cases size
  cases eq_of_heq table
  rfl

private theorem embedding_heq {L : FirstOrder.Language} {V W : Type}
    {A : L.Structure V} {B C : L.Structure W} (h : B = C)
    (f : @FirstOrder.Language.Embedding L V W A B)
    (g : @FirstOrder.Language.Embedding L V W A C)
    (hf : ∀ x, f.toFun x = g.toFun x) : HEq f g := by
  cases h
  apply heq_of_eq
  apply FirstOrder.Language.Embedding.ext
  exact hf

/-- The actual old finite extension property gives reasonableness for the
concrete finite-age forgetful functor, retaining the SAME prescribed map.
The SourceAge forth theorem supplies this premise for the actual split. -/
theorem reasonable_of_extension
    (extension : SourceAge.FiniteExtension ((originalTable (S := S))) P.projectedTable) :
    Reasonable P.forget := by
  intro C B f
  change @FirstOrder.Language.Embedding (Age.Language S) (Fin C.size) (Fin B.size)
    (P.object C).structure B.structure at f
  letI : (Age.Language S).Structure (Fin C.size) := (P.object C).structure
  letI : (Age.Language S).Structure (Fin B.size) := B.structure
  letI : (Age.Language T).Structure (Fin C.size) := C.structure
  have hf := (P.object C).table.embedding_preserves B.table f
  have hC : (P.object C).table = Age.table S (P.project ∘ C.point) (fun _ => 0) := by
    change P.mapTable C.table = _
    rw [zero_table C,P.map_actual]
  have ho : ∀ x, (P.project (C.point x)).1 = (B.point (f.toFun x)).1 := by
    intro x
    have he := (congrArg (fun U : Age.Table S (Fin B.size) => U.owner (f.toFun x)) (zero_table B)).symm.trans
      ((hf.1 x).trans (congrArg (fun U : Age.Table S (Fin C.size) => U.owner x) hC))
    exact (congrArg Prod.fst ((Age.ownerEquiv S).injective he)).symm
  have hc : ∀ x y, taggedColour S (P.project (C.point x)) (P.project (C.point y)) =
      taggedColour S (B.point (f.toFun x)) (B.point (f.toFun y)) := by
    intro x y
    have he := (congrArg (fun U : Age.Table S (Fin B.size) => U.colour (f.toFun x) (f.toFun y)) (zero_table B)).symm.trans
      ((hf.2 x y).trans (congrArg (fun U : Age.Table S (Fin C.size) => U.colour x y) hC))
    exact ((Age.colourEquiv S).injective he).symm
  obtain ⟨r,hrOwner,hrColour,hr⟩ := extension C.size B.size f.toEmbedding
    ⟨B.point,B.point_injective⟩ ⟨C.point,C.point_injective⟩ ⟨ho,hc⟩
  let D : Age.Chart T (Age.zeroMask T) := {
    size := B.size
    table := Age.table T r (fun _ => 0)
    realized := ⟨r,(fun _ => 0),r.injective,
      ⟨fun _ => rfl,fun _ _ => ⟨rfl,rfl⟩⟩,rfl⟩ }
  have hdTable : (P.object D).table = B.table := by
    change P.mapTable (Age.table T r (fun _ => 0)) = B.table
    rw [P.map_actual,zero_table B]
    apply congrArg₂ Table.mk
    · funext x
      exact congrArg (fun i => Age.ownerEquiv S (i,0)) (hrOwner x)
    · funext x y
      exact congrArg (Age.colourEquiv S) (hrColour x y)
  have hd : P.object D = B := chart_ext rfl (HEq.rfl.trans (heq_of_eq hdTable))
  letI : (Age.Language T).Structure (Fin B.size) := D.structure
  let g : C ⟶ D := C.table.embedding D.table f.toEmbedding
    (fun x => by
      have hz := congrArg (fun p : Sigma Y => Age.ownerEquiv T (p.1,0)) (hr x)
      exact hz.trans (congrArg (fun U : Age.Table T (Fin C.size) => U.owner x) (zero_table C)).symm)
    (fun x y => by
      have hz := congrArg₂ (fun p q : Sigma Y => Age.colourEquiv T (taggedColour T p q)) (hr x) (hr y)
      exact hz.trans (congrArg (fun U : Age.Table T (Fin C.size) => U.colour x y) (zero_table C)).symm)
  refine ⟨D,g,hd,?_⟩
  apply embedding_heq (congrArg Table.toStructure hdTable)
  intro x
  rfl

/-- The empty source turns same-map reasonableness into reduct surjectivity;
no source point or infinite-age hypothesis is needed. -/
theorem reductSurjective_of_extension
    (extension : SourceAge.FiniteExtension (originalTable (S := S)) P.projectedTable) :
    ReductSurjective P.forget := by
  intro B
  let E := Age.emptyChart T (Age.zeroMask T)
  letI := (P.object E).structure
  letI : (Age.Language S).Structure (Fin B.size) := B.structure
  let f : P.object E ⟶ B := (P.object E).table.embedding B.table
    ⟨Fin.elim0,fun x => Fin.elim0 x⟩ (fun x => Fin.elim0 x) (fun x => Fin.elim0 x)
  obtain ⟨D,g,hd,_⟩ := P.reasonable_of_extension extension E B f
  exact ⟨D,hd⟩

/-- All three actual expansion properties are bundled with the concrete
forgetful functor; nothing is supplied by a principal completion callback. -/
def transition_of_extension
    (extension : SourceAge.FiniteExtension (originalTable (S := S)) P.projectedTable) :
    UnaryTransition
      ⟨Age.Chart S (Age.zeroMask S),Age.chartCategory S (Age.zeroMask S)⟩
      ⟨Age.Chart T (Age.zeroMask T),Age.chartCategory T (Age.zeroMask T)⟩ where
  forget := P.forget
  reasonable := P.reasonable_of_extension extension
  reductSurjective := P.reductSurjective_of_extension extension
  precompact := P.precompact

end
end UnaryReduct
end CCO.APCharacter.Towers
