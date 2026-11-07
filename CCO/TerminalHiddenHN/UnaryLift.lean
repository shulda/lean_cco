import CCO.TerminalHiddenHN.RealExpansion
import CCO.TerminalHiddenHN.UnaryLiftBases
import Mathlib.Basic.Finite.Sum

/-! Retain the actual terminal unary names when viewing a finite
relational Ramsey expansion over its original unary reduct. Legal
predicate tables identify different realizations of the same expansion.
Reasonableness lifts the SAME supplied old map through the actual chart
forgetful functor; Ramsey uses the unchanged terminal embedding sets. -/

universe u v w l k
namespace CCO.TerminalHiddenHN.UnaryLift
open CCO.APCharacter CCO.APCharacter.Towers
noncomputable section
variable {ι κ : Type u} {X : ι → Type v} {Y : κ → Type v}
variable {S : AtomicSource.{u,v,w} ι X} {T : AtomicSource.{u,v,w} κ Y}
variable (P : UnaryReduct S T) (E : RealExpansionData.{u,v,w,l,k} T)

structure Tables (A : FiniteInduced (X := X)) where
  unary : (κ ⊕ E.Unary) → A.vertices → Prop
  binary : ULift.{u} E.Binary → A.vertices → A.vertices → Prop

@[ext] theorem Tables.ext {A : FiniteInduced (X := X)} {a b : Tables E A}
    (hu : ∀ R x, a.unary R x ↔ b.unary R x)
    (hb : ∀ R x y, a.binary R x y ↔ b.binary R x y) : a = b := by
  cases a with
  | mk au ab =>
    cases b with
    | mk bu bb =>
      have hU : au = bu := funext fun R => funext fun x => propext (hu R x)
      have hB : ab = bb := funext fun R => funext fun x => funext fun y => propext (hb R x y)
      cases hU
      cases hB
      rfl

abbrev tablesOf {A : FiniteInduced (X := X)} (L : Lift P A)
    (a : E.Expansion L.object) : Tables E A where
  unary R x := match R with
    | .inl s => (L.point x).1 = s
    | .inr R => E.unary a R (L.toObject x)
  binary R x y := E.binary a R.down (L.toObject x) (L.toObject y)

def Legal {A : FiniteInduced (X := X)} (t : Tables E A) : Prop :=
  ∃ L : Lift P A, ∃ a : E.Expansion L.object, t = tablesOf P E L a

abbrev Expansion (A : FiniteInduced (X := X)) := {t : Tables E A // Legal P E t}

abbrev fromLift {A : FiniteInduced (X := X)} (L : Lift P A)
    (a : E.Expansion L.object) : Expansion P E A :=
  ⟨tablesOf P E L a,⟨L,a,rfl⟩⟩

abbrev Lift.restrict {A B : FiniteInduced (X := X)} (L : Lift P B)
    (f : InducedEmbedding S A B) : Lift P A where
  point x := L.point (f.toEmbedding x)
  injective := L.injective.comp f.toEmbedding.injective
  sort_eq x := (L.sort_eq _).trans (f.preserves_sort x)
  colour_eq x y := (L.colour_eq _ _).trans (f.preserves_colours x y).symm

def restrictionMap {A B : FiniteInduced (X := X)} (L : Lift P B)
    (f : InducedEmbedding S A B) :
    InducedEmbedding T (L.restrict P f).object L.object :=
  embedding_of_sorts (L.restrict P f) L f (fun _ => rfl)

abbrev restrictTables {A B : FiniteInduced (X := X)} (f : InducedEmbedding S A B)
    (t : Tables E B) : Tables E A where
  unary R x := t.unary R (f.toEmbedding x)
  binary R x y := t.binary R (f.toEmbedding x) (f.toEmbedding y)

theorem restrictTables_legal {A B : FiniteInduced (X := X)}
    (f : InducedEmbedding S A B) {t : Tables E B} (ht : Legal P E t) :
    Legal P E (restrictTables E f t) := by
  obtain ⟨L,b,rfl⟩ := ht
  refine ⟨L.restrict P f,E.restrict (restrictionMap P L f) b,?_⟩
  apply Tables.ext
  · intro R x
    cases R with
    | inl s => exact Iff.rfl
    | inr R =>
      simpa only [restrictionMap,embedding_of_sorts_toObject] using
        (E.restrict_unary (restrictionMap P L f) b R ((L.restrict P f).toObject x)).symm
  · intro R x y
    simpa only [restrictionMap,embedding_of_sorts_toObject] using
      (E.restrict_binary (restrictionMap P L f) b R.down
        ((L.restrict P f).toObject x) ((L.restrict P f).toObject y)).symm

def restrictExpansion {A B : FiniteInduced (X := X)} (f : InducedEmbedding S A B)
    (b : Expansion P E B) : Expansion P E A :=
  ⟨restrictTables E f b.val,restrictTables_legal P E f b.property⟩

abbrev data : RealExpansionData.{u,v,w,max u l,max u v l} S where
  Unary := κ ⊕ E.Unary
  Binary := ULift.{u} E.Binary
  finiteUnary := by
    letI := T.finiteSort
    letI := E.finiteUnary
    infer_instance
  finiteBinary := by
    letI := E.finiteBinary
    infer_instance
  unarySort := Sum.elim P.parent (fun R => P.parent (E.unarySort R))
  leftSort R := P.parent (E.leftSort R.down)
  rightSort R := P.parent (E.rightSort R.down)
  Expansion := Expansion P E
  nonempty A := by
    let L := canonicalLift P A
    exact ⟨fromLift P E L (Classical.choice (E.nonempty L.object))⟩
  unary a := a.val.unary
  binary a := a.val.binary
  unary_sorted := by
    rintro A ⟨t,L,a,rfl⟩ R x hx
    cases R with
    | inl s => exact (L.sort_eq x).symm.trans (congrArg P.parent hx)
    | inr R =>
      exact (L.sort_eq x).symm.trans
        (congrArg P.parent (E.unary_sorted a R (L.toObject x) hx))
  binary_sorted := by
    rintro A ⟨t,L,a,rfl⟩ R x y hxy
    obtain ⟨hx,hy⟩ := E.binary_sorted a R.down (L.toObject x) (L.toObject y) hxy
    exact ⟨(L.sort_eq x).symm.trans (congrArg P.parent hx),
      (L.sort_eq y).symm.trans (congrArg P.parent hy)⟩
  faithful a b hu hb := Subtype.ext (Tables.ext E hu hb)
  restrict := restrictExpansion P E
  restrict_unary _ _ _ _ := Iff.rfl
  restrict_binary _ _ _ _ _ := Iff.rfl

/-- Projecting actual terminal pair names retains the complete old
name, including equality and repeated-sort information. -/
def projectColour (c : Age.Colour T) : Age.Colour S :=
  ⟨P.parent c.1,P.parent c.2.1,Option.map (P.atom _ _) c.2.2⟩

theorem projectColour_tagged (p q : Sigma Y) :
    projectColour P (taggedColour T p q) = taggedColour S (P.project p) (P.project q) := by
  change (⟨P.parent p.1,P.parent q.1,Option.map (P.atom _ _) (T.colour p.2 q.2)⟩ :
    Age.Colour S) = _
  rw [← P.colour]
  rfl

def toOldEmbedding {A B : FiniteInduced (X := X)} (L : Lift P A) (M : Lift P B)
    {a : E.Expansion L.object} {b : E.Expansion M.object} (f : E.Embedding a b) :
    (data P E).Embedding (fromLift P E L a) (fromLift P E M b) where
  old := {
    toEmbedding := L.toObject.toEmbedding.trans (f.old.toEmbedding.trans M.toObject.symm.toEmbedding)
    preserves_sort := by
      intro x
      let y := M.toObject.symm (f.old.toEmbedding (L.toObject x))
      have hs : (M.point y).1 = (L.point x).1 := by
        rw [M.point_toObject_symm]
        exact f.old.preserves_sort (L.toObject x)
      exact (M.sort_eq y).symm.trans ((congrArg P.parent hs).trans (L.sort_eq x))
    preserves_colours := by
      intro x y
      have hf := congrArg (projectColour P) (f.old.preserves_colours (L.toObject x) (L.toObject y))
      rw [projectColour_tagged,projectColour_tagged] at hf
      exact (L.colour_eq x y).symm.trans (hf.trans (by
        rw [← M.point_toObject_symm (f.old.toEmbedding (L.toObject x)),
          ← M.point_toObject_symm (f.old.toEmbedding (L.toObject y))]
        exact M.colour_eq _ _)) }
  unary_iff R x := by
    cases R with
    | inl s =>
      change (M.point (M.toObject.symm (f.old.toEmbedding (L.toObject x)))).1 = s ↔ _
      rw [M.point_toObject_symm,f.old.preserves_sort]
      exact Iff.rfl
    | inr R =>
      change E.unary b R (M.toObject (M.toObject.symm (f.old.toEmbedding (L.toObject x)))) ↔ _
      rw [Equiv.apply_symm_apply]
      exact f.unary_iff R (L.toObject x)
  binary_iff R x y := by
    change E.binary b R.down
      (M.toObject (M.toObject.symm (f.old.toEmbedding (L.toObject x))))
      (M.toObject (M.toObject.symm (f.old.toEmbedding (L.toObject y)))) ↔ _
    rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]
    exact f.binary_iff R.down (L.toObject x) (L.toObject y)

theorem terminal_sorts {A B : FiniteInduced (X := X)} (L : Lift P A) (M : Lift P B)
    {a : E.Expansion L.object} {b : E.Expansion M.object}
    (f : (data P E).Embedding (fromLift P E L a) (fromLift P E M b)) (x : A.vertices) :
    (M.point (f.old.toEmbedding x)).1 = (L.point x).1 := by
  have h := f.unary_iff (.inl (L.point x).1) x
  change (M.point (f.old.toEmbedding x)).1 = (L.point x).1 ↔
    (L.point x).1 = (L.point x).1 at h
  exact h.mpr rfl

def toTerminalEmbedding {A B : FiniteInduced (X := X)} (L : Lift P A) (M : Lift P B)
    {a : E.Expansion L.object} {b : E.Expansion M.object}
    (f : (data P E).Embedding (fromLift P E L a) (fromLift P E M b)) : E.Embedding a b where
  old := embedding_of_sorts L M f.old (terminal_sorts P E L M f)
  unary_iff R x := by
    obtain ⟨y,rfl⟩ := L.toObject.surjective x
    rw [embedding_of_sorts_toObject]
    exact f.unary_iff (.inr R) y
  binary_iff R x y := by
    obtain ⟨x,rfl⟩ := L.toObject.surjective x
    obtain ⟨y,rfl⟩ := L.toObject.surjective y
    rw [embedding_of_sorts_toObject,embedding_of_sorts_toObject]
    exact f.binary_iff ⟨R⟩ x y

@[simp] theorem toOld_toTerminal {A B : FiniteInduced (X := X)}
    (L : Lift P A) (M : Lift P B) {a : E.Expansion L.object} {b : E.Expansion M.object}
    (f : (data P E).Embedding (fromLift P E L a) (fromLift P E M b)) :
    toOldEmbedding P E L M (toTerminalEmbedding P E L M f) = f := by
  apply RealExpansionData.Embedding.ext
  intro x
  change M.toObject.symm
    (M.toObject (f.old.toEmbedding (L.toObject.symm (L.toObject x)))) = _
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]

@[simp] theorem toTerminal_toOld {A B : FiniteInduced (X := X)}
    (L : Lift P A) (M : Lift P B) {a : E.Expansion L.object} {b : E.Expansion M.object}
    (f : E.Embedding a b) :
    toTerminalEmbedding P E L M (toOldEmbedding P E L M f) = f := by
  apply RealExpansionData.Embedding.ext
  intro x
  change M.toObject
    (M.toObject.symm (f.old.toEmbedding (L.toObject (L.toObject.symm x)))) = _
  rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]

/-- Retaining the terminal unary labels gives exactly the SAME full
expanded embedding set, with literal inverse maps on vertices. -/
def embeddingEquiv {A B : FiniteInduced (X := X)} (L : Lift P A) (M : Lift P B)
    (a : E.Expansion L.object) (b : E.Expansion M.object) :
    E.Embedding a b ≃ (data P E).Embedding (fromLift P E L a) (fromLift P E M b) where
  toFun := toOldEmbedding P E L M
  invFun := toTerminalEmbedding P E L M
  left_inv := toTerminal_toOld P E L M
  right_inv := toOld_toTerminal P E L M

theorem toOld_comp {A B C : FiniteInduced (X := X)} (L : Lift P A) (M : Lift P B)
    (N : Lift P C) {a : E.Expansion L.object} {b : E.Expansion M.object}
    {c : E.Expansion N.object} (g : E.Embedding b c) (f : E.Embedding a b) :
    toOldEmbedding P E L N (g.comp f) =
      (toOldEmbedding P E M N g).comp (toOldEmbedding P E L M f) := by
  apply RealExpansionData.Embedding.ext
  intro x
  change N.toObject.symm (g.old.toEmbedding (f.old.toEmbedding (L.toObject x))) =
    N.toObject.symm (g.old.toEmbedding
      (M.toObject (M.toObject.symm (f.old.toEmbedding (L.toObject x)))))
  rw [Equiv.apply_symm_apply]

theorem reasonable (hP : Reasonable P.forget) (hE : E.Reasonable) :
    (data P E).Reasonable := by
  intro A B f a
  rcases a with ⟨t,L,a,rfl⟩
  obtain ⟨M,g,hg⟩ := lift_reasonable hP L f
  obtain ⟨b,hb⟩ := hE L.object M.object g a
  refine ⟨fromLift P E M b,?_⟩
  apply Subtype.ext
  apply Tables.ext
  · intro R x
    cases R with
    | inl s =>
      change (M.point (f.toEmbedding x)).1 = s ↔ (L.point x).1 = s
      have hs := g.preserves_sort (L.toObject x)
      rw [hg] at hs
      exact Iff.of_eq (congrArg (fun k => k = s) hs)
    | inr R =>
      change E.unary b R (M.toObject (f.toEmbedding x)) ↔ E.unary a R (L.toObject x)
      have he := E.restrict_unary g b R (L.toObject x)
      rw [hb,hg] at he
      exact he.symm
  · intro R x y
    change E.binary b R.down (M.toObject (f.toEmbedding x)) (M.toObject (f.toEmbedding y)) ↔
      E.binary a R.down (L.toObject x) (L.toObject y)
    have he := E.restrict_binary g b R.down (L.toObject x) (L.toObject y)
    rw [hb,hg,hg] at he
    exact he.symm

def projectedObject (B : FiniteInduced (X := Y)) : FiniteInduced (X := X) :=
  ⟨P.project '' B.vertices,B.finite_vertices.image P.project⟩

theorem canonicalLift_project (A : FiniteInduced (X := X)) (x : A.vertices) :
    P.project ((canonicalLift P A).point x) = x.val :=
  (Equiv.ofBijective P.project P.bijective).apply_symm_apply x.val

theorem projected_point_mem (B : FiniteInduced (X := Y))
    (x : (projectedObject P B).vertices) :
    (canonicalLift P (projectedObject P B)).point x ∈ B.vertices := by
  obtain ⟨y,hy,hxy⟩ := x.property
  have he : (canonicalLift P (projectedObject P B)).point x = y :=
    P.bijective.1 ((canonicalLift_project P _ x).trans hxy.symm)
  exact he.symm ▸ hy

def projectedEmbedding (B : FiniteInduced (X := Y)) :
    InducedEmbedding T (canonicalLift P (projectedObject P B)).object B where
  toEmbedding := {
    toFun x := ⟨x.val,by
      obtain ⟨y,hy⟩ := x.property
      exact hy ▸ projected_point_mem P B y⟩
    inj' := fun _ _ h => Subtype.ext (congrArg (fun y : B.vertices => y.val) h) }
  preserves_sort _ := rfl
  preserves_colours _ _ := rfl

def projectedInverse (B : FiniteInduced (X := Y)) :
    InducedEmbedding T B (canonicalLift P (projectedObject P B)).object where
  toEmbedding := {
    toFun x := ⟨x.val,by
      let y : (projectedObject P B).vertices := ⟨P.project x.val,⟨x.val,x.property,rfl⟩⟩
      exact ⟨y,P.bijective.1 (canonicalLift_project P _ y)⟩⟩
    inj' := fun _ _ h => Subtype.ext (congrArg
      (fun y : (canonicalLift P (projectedObject P B)).object.vertices => y.val) h) }
  preserves_sort _ := rfl
  preserves_colours _ _ := rfl

def projectedExpandedInverse (B : FiniteInduced (X := Y)) (b : E.Expansion B) :
    E.Embedding b (E.restrict (projectedEmbedding P B) b) where
  old := projectedInverse P B
  unary_iff R x := E.restrict_unary (projectedEmbedding P B) b R
    ((projectedInverse P B).toEmbedding x)
  binary_iff R x y := E.restrict_binary (projectedEmbedding P B) b R
    ((projectedInverse P B).toEmbedding x) ((projectedInverse P B).toEmbedding y)

/-- The final class has exactly the terminal expanded embedding sets.
Only its finite unary labels are retained while changing the old reduct. -/
theorem ramsey (hE : E.Ramsey) : (data P E).Ramsey := by
  intro A B a b n hn
  rcases a with ⟨ta,L,a,rfl⟩
  rcases b with ⟨tb,M,b,rfl⟩
  obtain ⟨C,c,hC⟩ := hE L.object M.object a b n hn
  let D := projectedObject P C
  let N := canonicalLift P D
  let d := E.restrict (projectedEmbedding P C) c
  let inv := projectedExpandedInverse P E C c
  refine ⟨D,fromLift P E N d,?_⟩
  intro colour
  let colourT : E.Embedding a c → Fin n := fun f =>
    colour (toOldEmbedding P E L N (inv.comp f))
  obtain ⟨g,hg⟩ := hC colourT
  refine ⟨toOldEmbedding P E M N (inv.comp g),?_⟩
  intro f₁ f₂
  have he (f : (data P E).Embedding (fromLift P E L a) (fromLift P E M b)) :
      toOldEmbedding P E L N (inv.comp (g.comp (toTerminalEmbedding P E L M f))) =
        (toOldEmbedding P E M N (inv.comp g)).comp f := by
    have ha : inv.comp (g.comp (toTerminalEmbedding P E L M f)) =
        (inv.comp g).comp (toTerminalEmbedding P E L M f) := by
      apply RealExpansionData.Embedding.ext
      intro x
      rfl
    rw [ha,toOld_comp,toOld_toTerminal]
  have hm := hg (toTerminalEmbedding P E L M f₁) (toTerminalEmbedding P E L M f₂)
  change colour (toOldEmbedding P E L N (inv.comp (g.comp (toTerminalEmbedding P E L M f₁)))) =
    colour (toOldEmbedding P E L N (inv.comp (g.comp (toTerminalEmbedding P E L M f₂)))) at hm
  exact (congrArg colour (he f₁)).symm.trans (hm.trans (congrArg colour (he f₂)))

/-- A concrete finite unary refinement followed by a genuine finite
relational Ramsey expansion gives the required expansion of the original
age. This is not composition of two abstract Ramsey-class callbacks. -/
theorem hasFiniteRelationalRamseyExpansion_of_unaryReduct
    (hP : Reasonable P.forget)
    (hT : HasFiniteRelationalRamseyExpansion.{u,v,w,l,k} T) :
    HasFiniteRelationalRamseyExpansion.{u,v,w,max u l,max u v l} S := by
  obtain ⟨E,hReason,hRamsey⟩ := hT
  exact ⟨data P E,reasonable P E hP hReason,ramsey P E hRamsey⟩

/-- The actual selected finite-cover elimination returns precisely this
transition and forgetful equality; no separate lifting provider is needed. -/
theorem hasFiniteRelationalRamseyExpansion_of_unaryTransition
    (F : UnaryTransition
      ⟨Age.Chart S (Age.zeroMask S),Age.chartCategory S (Age.zeroMask S)⟩
      ⟨Age.Chart T (Age.zeroMask T),Age.chartCategory T (Age.zeroMask T)⟩)
    (hF : F.forget = P.forget)
    (hT : HasFiniteRelationalRamseyExpansion.{u,v,w,l,k} T) :
    HasFiniteRelationalRamseyExpansion.{u,v,w,max u l,max u v l} S := by
  apply hasFiniteRelationalRamseyExpansion_of_unaryReduct P ?_ hT
  rw [← hF]
  exact F.reasonable

end
end CCO.TerminalHiddenHN.UnaryLift
