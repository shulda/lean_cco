import CCO.ResetOrder.Unary.StoredPatterns

/-! Actual full ambient two-colour Ramsey proof. The old host precedes every
competitor; no Ramsey property of either intermediate class is assumed. -/
universe u v
namespace CCO.ResetOrder.Unary
open CCO.UnarySupport
variable {L : Signature.{u}} {P : Fibres.{u,v} L} {X : ExtraLanguage L}

abbrev TaskAge (P : Fibres.{u,v} L) := TaskObject P → Prop

def TaskEP (U1 : TaskAge P) (U0 : Age.{u,v} L) : Prop :=
  ∀ A, U1 A → ∃B, U0 B ∧ ∀o : FibreOrder P B,
    U1 ⟨B,o⟩ → Nonempty (TaskHom A ⟨B,o⟩)

structure ResetTemplate (R : FullAge P X) where
  object : FullObject P X
  mem : R object
  left : object.task.old.Carrier
  right : object.task.old.Carrier
  comparison : object.task.order.lt left right
  reset : P.reset object.task.old left right
  generated : object.unary.closure {left,right} = Set.univ
  realizes : ∀A, R A → ∀x y, A.task.order.lt x y → P.reset A.task.old x y →
    Nonempty (PointedRealization object left right A x y)

def CompleteResetEdgeType (R : FullAge P X) : Prop :=
  ∀A, R A → ∀x y, A.task.order.lt x y → P.reset A.task.old x y →
    Nonempty (ResetTemplate R)

/-- Colour ALL complete pointed template embeddings, obtaining one global
sign on BOTH edges of EVERY stored midpoint path. -/
theorem template_global_sign {R : FullAge P X} (T : ResetTemplate R)
    {D C : FullObject P X} (hD : R D) (arrow : FullArrow T.object D C 2)
    (competitor : FibreOrder P C.task.old) :
    ∃g : FullHom D C,
      (∀x y, D.task.order.lt x y → P.reset D.task.old x y →
        competitor.lt (g.point x) (g.point y)) ∨
      (∀x y, D.task.order.lt x y → P.reset D.task.old x y →
        competitor.lt (g.point y) (g.point x)) := by
  classical
  let color : FullHom T.object C → Fin 2 := fun e =>
    if competitor.lt (e.point T.left) (e.point T.right) then 0 else 1
  obtain ⟨g,shade,hmono⟩ := arrow color
  refine ⟨g,?_⟩
  by_cases hs : shade = 0
  · left
    intro x y hxy hreset
    obtain ⟨e⟩ := T.realizes D hD x y hxy hreset
    have hm := hmono e.embedding
    have heleft : (fullCompose g e.embedding).point T.left = g.point x :=
      congrArg g.point e.embedding_left
    have heright : (fullCompose g e.embedding).point T.right = g.point y :=
      congrArg g.point e.embedding_right
    rw [hs] at hm
    change (if competitor.lt _ _ then (0 : Fin 2) else 1) = 0 at hm
    rw [heleft,heright] at hm
    by_contra hn
    simp only [hn,ite_false] at hm
    exact (by decide : (1 : Fin 2) ≠ 0) hm
  · right
    intro x y hxy hreset
    obtain ⟨e⟩ := T.realizes D hD x y hxy hreset
    have hm := hmono e.embedding
    have heleft : (fullCompose g e.embedding).point T.left = g.point x :=
      congrArg g.point e.embedding_left
    have heright : (fullCompose g e.embedding).point T.right = g.point y :=
      congrArg g.point e.embedding_right
    have hn : ¬ competitor.lt (g.point x) (g.point y) := by
      intro hp
      apply hs
      change (if competitor.lt _ _ then (0 : Fin 2) else 1) = shade at hm
      simp only [heleft,heright,hp,ite_true] at hm
      exact hm.symm
    have hfibre : P.same C.task.old (g.point x) (g.point y) :=
      (P.same_natural g.task.old x y).2 (P.reset_same D.task.old x y hreset)
    have hne : g.point x ≠ g.point y :=
      fun h => P.reset_ne D.task.old x y hreset (g.task.old.injective h)
    exact (competitor.total hfibre hne).resolve_left hn

/-- Actual reset EP: both source patterns, their paths, full-template colour
pullback and final source embeddings are constructed, not supplied providers. -/
theorem reset_expansion_property {R : FullAge P X} {U1 : TaskAge P} {U0 : Age.{u,v} L}
    (full_reduct : ∀F, R F → U1 F.task)
    (lower_reduct : ∀A, U1 A → U0 A.old)
    (lift : ∀A, U1 A → ∃F, R F ∧ Nonempty (TaskHom A F.task))
    (reversal : ∀A, U1 A → U1 (reverse A))
    (jep : FullJEP R) (ramsey : FullRamsey R)
    (schema : MidpointSchema R) (edgeType : CompleteResetEdgeType R) : TaskEP U1 U0 := by
  classical
  intro A hA
  by_cases no_comparison : ∀x y, ¬ A.order.lt x y
  · refine ⟨A.old,lower_reduct A hA,?_⟩
    intro o _
    exact ⟨taskHomOfPreserves (identity A.old.data)
      (fun x y h => False.elim (no_comparison x y h))⟩
  · obtain ⟨x,hx⟩ := Classical.not_forall.mp no_comparison
    obtain ⟨y,hy⟩ := Classical.not_forall.mp hx
    have hxy := Classical.not_not.mp hy
    obtain ⟨Fp,hFp,⟨ip⟩⟩ := lift A hA
    obtain ⟨Fm,hFm,⟨im⟩⟩ := lift (reverse A) (reversal A hA)
    obtain ⟨Dp,hDp,⟨sp⟩⟩ := store_all_original_comparisons schema A Fp hFp ip
    obtain ⟨Dm,hDm,⟨sm⟩⟩ := store_all_original_comparisons schema (reverse A) Fm hFm im
    obtain ⟨z,hl,_,hml,_⟩ := sp.midpoint x y hxy
    obtain ⟨T⟩ := edgeType Dp hDp _ z hl hml
    obtain ⟨D,hD,⟨jp⟩,⟨jm⟩⟩ := jep Dp Dm hDp hDm
    let positive := sp.map jp
    let negative := sm.map jm
    obtain ⟨C,hC,hArrow⟩ := ramsey T.object D T.mem hD 2 (by decide)
    refine ⟨C.task.old,lower_reduct C.task (full_reduct C hC),?_⟩
    intro o _
    obtain ⟨g,hpos | hneg⟩ := template_global_sign T hD hArrow o
    · refine ⟨taskHomOfPreserves (compose g.task.old positive.copy.old) ?_⟩
      intro a b hab
      obtain ⟨m,hl,hr,hml,hmr⟩ := positive.midpoint a b hab
      exact o.trans (hpos _ _ hl hml) (hpos _ _ hr hmr)
    · refine ⟨taskHomOfPreserves (compose g.task.old negative.copy.old) ?_⟩
      intro a b hab
      have hba : (reverse A).order.lt b a := hab
      obtain ⟨m,hl,hr,hml,hmr⟩ := negative.midpoint b a hba
      exact o.trans (hneg _ _ hr hmr) (hneg _ _ hl hml)

theorem task_copy_preserves_codes (codes : TaskCodes P) {A B : TaskObject P}
    (f : TaskHom A B) {n : ℕ} (R : codes.Symbol n) xs :
    codes.value B R (f.old.point ∘ xs) ↔ codes.value A R xs := codes.natural f R xs

end CCO.ResetOrder.Unary
