import CCO.APCharacter.Towers.UnaryReduct

/-! Actual finite unary lifts may move the old points while retaining
their complete old names. Reasonableness lifts the SAME supplied old
embedding with the prescribed source lift; no canonical target lift is
silently imposed. -/

universe u v w
namespace CCO.TerminalHiddenHN.UnaryLift
open CategoryTheory CCO.APCharacter CCO.APCharacter.Towers
open CCO.OwnerTransversal.CountableColour
noncomputable section
variable {ι κ : Type u} {X : ι → Type v} {Y : κ → Type v}
variable {S : AtomicSource.{u,v,w} ι X} {T : AtomicSource.{u,v,w} κ Y}
variable (P : UnaryReduct S T)

structure Lift (A : FiniteInduced (X := X)) where
  point : A.vertices → Sigma Y
  injective : Function.Injective point
  sort_eq : ∀ x, (P.project (point x)).1 = x.val.1
  colour_eq : ∀ x y, taggedColour S (P.project (point x)) (P.project (point y)) =
    taggedColour S x.val y.val

namespace Lift
variable {P} {A : FiniteInduced (X := X)}

def object (L : Lift P A) : FiniteInduced (X := Y) := by
  letI := A.finite_vertices.to_subtype
  exact ⟨Set.range L.point,Set.finite_range _⟩

def toObject (L : Lift P A) : A.vertices ≃ L.object.vertices :=
  Equiv.ofInjective L.point L.injective

@[simp] theorem toObject_val (L : Lift P A) (x : A.vertices) :
    (L.toObject x).val = L.point x := rfl

@[simp] theorem point_toObject_symm (L : Lift P A) (x : L.object.vertices) :
    L.point (L.toObject.symm x) = x.val :=
  congrArg Subtype.val (L.toObject.apply_symm_apply x)

end Lift

def canonicalLift (A : FiniteInduced (X := X)) : Lift P A := by
  let e : Sigma Y ≃ Sigma X := Equiv.ofBijective P.project P.bijective
  exact {
    point := fun x => e.symm x.val
    injective := e.symm.injective.comp Subtype.val_injective
    sort_eq := fun x => congrArg Sigma.fst (e.apply_symm_apply x.val)
    colour_eq := fun x y => congrArg₂ (taggedColour S)
      (e.apply_symm_apply x.val) (e.apply_symm_apply y.val) }

/-- Complete new sort names and complete projected old colour determine
the complete new colour, by the actual atom-map injectivity. -/
theorem tagged_of_projected_and_sorts {p q r s : Sigma Y}
    (hp : p.1 = r.1) (hq : q.1 = s.1)
    (hc : taggedColour S (P.project p) (P.project q) =
      taggedColour S (P.project r) (P.project s)) :
    taggedColour T p q = taggedColour T r s := by
  rcases p with ⟨i,p⟩
  rcases q with ⟨j,q⟩
  rcases r with ⟨k,r⟩
  rcases s with ⟨l,s⟩
  dsimp only at hp hq
  subst k
  subst l
  apply congrArg (fun c => (⟨i,j,c⟩ : Age.Colour T))
  apply Option.map_injective (P.atom_injective i j)
  have hc' : S.colour (P.point i p) (P.point j q) =
      S.colour (P.point i r) (P.point j s) := by
    change (⟨P.parent i,P.parent j,S.colour (P.point i p) (P.point j q)⟩ : Age.Colour S) =
      ⟨P.parent i,P.parent j,S.colour (P.point i r) (P.point j s)⟩ at hc
    simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hc
  rw [← P.colour,← P.colour]
  exact hc'

variable {P} {A B : FiniteInduced (X := X)}

/-- The map is the supplied old embedding, conjugated by the actual
source/target image equivalences. Its old colour equality and new sort
equality reflect ALL actual new binary names. -/
def embedding_of_sorts (L : Lift P A) (M : Lift P B)
    (e : InducedEmbedding S A B)
    (hs : ∀ x, (M.point (e.toEmbedding x)).1 = (L.point x).1) :
    InducedEmbedding T L.object M.object where
  toEmbedding := L.toObject.symm.toEmbedding.trans (e.toEmbedding.trans M.toObject.toEmbedding)
  preserves_sort x := by
    change (M.point (e.toEmbedding (L.toObject.symm x))).1 = x.val.1
    rw [hs,L.point_toObject_symm]
  preserves_colours x y := by
    change taggedColour T x.val y.val =
      taggedColour T (M.point (e.toEmbedding (L.toObject.symm x)))
        (M.point (e.toEmbedding (L.toObject.symm y)))
    rw [← L.point_toObject_symm x,← L.point_toObject_symm y]
    apply tagged_of_projected_and_sorts P (hs _).symm (hs _).symm
    exact (L.colour_eq _ _).trans
      ((e.preserves_colours _ _).trans (M.colour_eq _ _).symm)

@[simp] theorem embedding_of_sorts_toObject (L : Lift P A) (M : Lift P B)
    (e : InducedEmbedding S A B)
    (hs : ∀ x, (M.point (e.toEmbedding x)).1 = (L.point x).1) (x : A.vertices) :
    (embedding_of_sorts L M e hs).toEmbedding (L.toObject x) = M.toObject (e.toEmbedding x) := by
  change M.toObject (e.toEmbedding (L.toObject.symm (L.toObject x))) = _
  rw [Equiv.symm_apply_apply]

private theorem zero_table {U : AtomicSource.{u,v,w} ι X}
    (C : Age.Chart U (Age.zeroMask U)) :
    C.table = Age.table U C.point (fun _ => 0) :=
  C.table_eq.trans (congrArg (Age.table U C.point) (funext C.legal.1))

private theorem chart_eq_owner {U : AtomicSource.{u,v,w} ι X}
    {C D : Age.Chart U (Age.zeroMask U)} (h : C = D) (x : Fin D.size) :
    C.table.owner (Fin.cast (congrArg Age.Chart.size h).symm x) = D.table.owner x := by
  cases h
  rfl

private theorem chart_eq_colour {U : AtomicSource.{u,v,w} ι X}
    {C D : Age.Chart U (Age.zeroMask U)} (h : C = D) (x y : Fin D.size) :
    C.table.colour (Fin.cast (congrArg Age.Chart.size h).symm x)
      (Fin.cast (congrArg Age.Chart.size h).symm y) = D.table.colour x y := by
  cases h
  rfl

private theorem forget_map_apply (P : UnaryReduct S T)
    {C D : Age.Chart T (Age.zeroMask T)} {E : Age.Chart S (Age.zeroMask S)}
    (g : C ⟶ D) (f : P.object C ⟶ E) (h : P.object D = E)
    (hg : HEq (P.forget.map g) f) (x : Fin C.size) :
    g.toFun x = Fin.cast (congrArg Age.Chart.size h).symm (f.toFun x) := by
  cases h
  have he : P.forget.map g = f := eq_of_heq hg
  exact congrArg (fun k : P.object C ⟶ P.object D => k.toFun x) he

/-- Reasonableness of the ACTUAL chart forgetful functor lifts the
prescribed finite old embedding with the prescribed source lift. -/
theorem lift_reasonable (hP : Reasonable P.forget)
    (L : Lift P A) (e : InducedEmbedding S A B) :
    ∃ M : Lift P B, ∃ g : InducedEmbedding T L.object M.object,
      ∀ x, g.toEmbedding (L.toObject x) = M.toObject (e.toEmbedding x) := by
  classical
  letI : Finite A.vertices := A.finite_vertices.to_subtype
  letI : Finite B.vertices := B.finite_vertices.to_subtype
  letI : Fintype A.vertices := Fintype.ofFinite _
  letI : Fintype B.vertices := Fintype.ofFinite _
  let a := Fintype.equivFin A.vertices
  let b := Fintype.equivFin B.vertices
  let p : Fin (Fintype.card A.vertices) → Sigma Y := fun i => L.point (a.symm i)
  let q : Fin (Fintype.card B.vertices) → Sigma X := fun i => (b.symm i).val
  let C : Age.Chart T (Age.zeroMask T) := {
    size := Fintype.card A.vertices
    table := Age.table T p (fun _ => 0)
    realized := ⟨p,(fun _ => 0),L.injective.comp a.symm.injective,
      ⟨fun _ => rfl,fun _ _ => ⟨rfl,rfl⟩⟩,rfl⟩ }
  let D : Age.Chart S (Age.zeroMask S) := {
    size := Fintype.card B.vertices
    table := Age.table S q (fun _ => 0)
    realized := ⟨q,(fun _ => 0),Subtype.val_injective.comp b.symm.injective,
      ⟨fun _ => rfl,fun _ _ => ⟨rfl,rfl⟩⟩,rfl⟩ }
  let j : Fin C.size ↪ Fin D.size :=
    a.symm.toEmbedding.trans (e.toEmbedding.trans b.toEmbedding)
  have hqj (i : Fin C.size) : q (j i) = (e.toEmbedding (a.symm i)).val := by
    change (b.symm (b (e.toEmbedding (a.symm i)))).val = _
    rw [Equiv.symm_apply_apply]
  have hC : (P.object C).table = Age.table S (P.project ∘ p) (fun _ => 0) :=
    P.map_actual p (fun _ => 0)
  let f : P.object C ⟶ D := (P.object C).table.embedding D.table j (by
    intro i
    rw [hC]
    change Age.ownerEquiv S ((q (j i)).1,0) = Age.ownerEquiv S ((P.project (p i)).1,0)
    apply congrArg (fun k => Age.ownerEquiv S (k,0))
    exact (congrArg Sigma.fst (hqj i)).trans
      ((e.preserves_sort _).trans (L.sort_eq _).symm)) (by
    intro i k
    rw [hC]
    change Age.colourEquiv S (taggedColour S (q (j i)) (q (j k))) =
      Age.colourEquiv S (taggedColour S (P.project (p i)) (P.project (p k)))
    apply congrArg (Age.colourEquiv S)
    exact (congrArg₂ (taggedColour S) (hqj i) (hqj k)).trans
      ((L.colour_eq _ _).trans (e.preserves_colours _ _)).symm)
  obtain ⟨E,g,hE,hg⟩ := hP C D f
  let hsize : E.size = D.size := congrArg Age.Chart.size hE
  let castIndex : Fin D.size → Fin E.size := Fin.cast hsize.symm
  have hcast : Function.Injective castIndex := by
    intro x y hxy
    exact Fin.ext (congrArg (fun z : Fin E.size => z.val) hxy)
  let point : B.vertices → Sigma Y := fun x => E.point (castIndex (b x))
  have howner (i : Fin D.size) : (P.project (E.point (castIndex i))).1 = (q i).1 := by
    have h := chart_eq_owner hE i
    change (P.mapTable E.table).owner (castIndex i) = (Age.table S q (fun _ => 0)).owner i at h
    rw [zero_table E,P.map_actual] at h
    exact congrArg Prod.fst ((Age.ownerEquiv S).injective h)
  have hcolour (i k : Fin D.size) :
      taggedColour S (P.project (E.point (castIndex i))) (P.project (E.point (castIndex k))) =
        taggedColour S (q i) (q k) := by
    have h := chart_eq_colour hE i k
    change (P.mapTable E.table).colour (castIndex i) (castIndex k) =
      (Age.table S q (fun _ => 0)).colour i k at h
    rw [zero_table E,P.map_actual] at h
    exact (Age.colourEquiv S).injective h
  let M : Lift P B := {
    point := point
    injective := E.point_injective.comp (hcast.comp b.injective)
    sort_eq := fun x => by
      have h := howner (b x)
      simpa only [q,Equiv.symm_apply_apply] using h
    colour_eq := fun x y => by
      have h := hcolour (b x) (b y)
      simpa only [q,Equiv.symm_apply_apply] using h }
  have hs : ∀ x, (M.point (e.toEmbedding x)).1 = (L.point x).1 := by
    intro x
    have h := (C.table.embedding_preserves E.table g).1 (a x)
    have hz := congrArg (fun U : Age.Table T (Fin E.size) => U.owner (g.toFun (a x)))
      (zero_table E)
    have hread := hz.symm.trans h
    have hsort := congrArg Prod.fst ((Age.ownerEquiv T).injective hread)
    have hmap := forget_map_apply P g f hE hg (a x)
    have hfa : f.toFun (a x) = b (e.toEmbedding x) := by
      change b (e.toEmbedding (a.symm (a x))) = _
      rw [Equiv.symm_apply_apply]
    rw [hfa] at hmap
    change g.toFun (a x) = castIndex (b (e.toEmbedding x)) at hmap
    rw [hmap] at hsort
    simpa only [C,p,Equiv.symm_apply_apply] using hsort
  exact ⟨M,embedding_of_sorts L M e hs,embedding_of_sorts_toObject L M e hs⟩

end
end CCO.TerminalHiddenHN.UnaryLift
