import CCO.ResetOrder.Unary.PointedTemplate

/-! C39--C44: ORDERED SAP over the WHOLE actual generated pair closure. -/
universe u v
namespace CCO.ResetOrder.Unary
open CCO.ResetOrder.Unary.Primitive
variable {L : Signature.{u}} {P : Fibres.{u,v} L} {X : ExtraLanguage L}

structure PlainPairWitness (A : FullObject P X) (u v : A.task.old.Carrier) where
  host : FullObject P X
  left : host.task.old.Carrier
  right : host.task.old.Carrier
  midpoint : host.task.old.Carrier
  iso : Iso (pairClosure A u v).unary (pairClosure host left right).unary
  root_left : iso.hom.point (pairLeft A u v) = pairLeft host left right
  root_right : iso.hom.point (pairRight A u v) = pairRight host left right
  outside : midpoint ∉ pairSet host left right
  reset_left : P.reset host.task.old left midpoint
  reset_right : P.reset host.task.old midpoint right

def PlainPairWitness.base {A : FullObject P X} {u v : A.task.old.Carrier}
    (w : PlainPairWitness A u v) : Hom (pairClosure A u v).unary w.host.unary :=
  compose (pairInclusion w.host w.left w.right).unary w.iso.hom

@[simp] theorem PlainPairWitness.base_left {A : FullObject P X} {u v : A.task.old.Carrier}
    (w : PlainPairWitness A u v) : w.base.point (pairLeft A u v) = w.left :=
  congrArg Subtype.val w.root_left

@[simp] theorem PlainPairWitness.base_right {A : FullObject P X} {u v : A.task.old.Carrier}
    (w : PlainPairWitness A u v) : w.base.point (pairRight A u v) = w.right :=
  congrArg Subtype.val w.root_right

theorem PlainPairWitness.outside_base {A : FullObject P X} {u v : A.task.old.Carrier}
    (w : PlainPairWitness A u v) : w.midpoint ∉ Set.range w.base.point := by
  rintro ⟨p,hp⟩
  exact w.outside (hp ▸ (w.iso.hom.point p).property)

def HasAllowedOrder (R : FullAge P X) (A : FullObject P X) : Prop :=
  ∃o : FibreOrder P A.task.old, R (reorder A o)

/-- Only PERMITTED unexpanded witnesses are required to admit the prescribed
ordered lift over the WHOLE inherited base. No SAP conclusion is assumed here. -/
def FreePairOrderExtension (R : FullAge P X) : Prop :=
  ∀ A, R A → ∀u v, A.task.order.lt u v → ∀w : PlainPairWitness A u v,
    HasAllowedOrder R w.host →
    ∃o : FibreOrder P w.host.task.old, R (reorder w.host o) ∧
      (∀p q, (pairClosure A u v).task.order.lt p q → o.lt (w.base.point p) (w.base.point q)) ∧
      o.lt w.left w.midpoint ∧ o.lt w.midpoint w.right

def MidpointSchema (R : FullAge P X) : Prop :=
  ∀A, R A → ∀u v, A.task.order.lt u v →
    ∃B, R B ∧ ∃i : FullHom A B, ∃z,
      z ∉ Set.range i.point ∧ B.task.order.lt (i.point u) z ∧
      B.task.order.lt z (i.point v) ∧ P.reset B.task.old (i.point u) z ∧
      P.reset B.task.old z (i.point v)

theorem fresh_midpoint_from_ordered_sap {R : FullAge P X}
    (hered : FullHereditary R) (sap : FullSAP R)
    (witness : ∀A, R A → ∀u v, A.task.order.lt u v →
      ∃w : PlainPairWitness A u v, HasAllowedOrder R w.host)
    (free : FreePairOrderExtension R) : MidpointSchema R := by
  intro A hA u v huv
  obtain ⟨w,hw⟩ := witness A hA u v huv
  obtain ⟨o,hT,hbase,hl,hr⟩ := free A hA u v huv w hw
  let T := reorder w.host o
  let j : FullHom (pairClosure A u v) T := fullHomOfUnaryPreserves w.base hbase
  have hP : R (pairClosure A u v) := hered hA ⟨pairInclusion A u v⟩
  obtain ⟨C,hC,f,g,hcomm,hstrong⟩ := sap (pairClosure A u v) A T hP hA hT
    (pairInclusion A u v) j
  have hleft : f.point u = g.point w.left := by
    have h := hcomm (pairLeft A u v)
    change f.point u = g.point (w.base.point (pairLeft A u v)) at h
    rw [w.base_left] at h
    exact h
  have hright : f.point v = g.point w.right := by
    have h := hcomm (pairRight A u v)
    change f.point v = g.point (w.base.point (pairRight A u v)) at h
    rw [w.base_right] at h
    exact h
  refine ⟨C,hC,f,g.point w.midpoint,?_,?_,?_,?_,?_⟩
  · rintro ⟨a,ha⟩
    obtain ⟨p,_,hp⟩ := hstrong a w.midpoint ha
    exact w.outside_base ⟨p,hp⟩
  · rw [hleft]
    exact (g.task.order_iff _ _).2 hl
  · rw [hright]
    exact (g.task.order_iff _ _).2 hr
  · rw [hleft]
    exact (P.reset_natural g.task.old _ _).2 w.reset_left
  · rw [hright]
    exact (P.reset_natural g.task.old _ _).2 w.reset_right

end CCO.ResetOrder.Unary
