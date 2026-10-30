import CCO.ResetOrder.Unary.Task

universe u v
namespace CCO.ResetOrder.Unary
open CCO.UnarySupport
variable {L : Signature.{u}} {P : Fibres.{u,v} L} {X : ExtraLanguage L}

abbrev FullAge (P : Fibres.{u,v} L) (X : ExtraLanguage L) := FullObject P X → Prop

def FullHereditary (R : FullAge P X) : Prop := ∀ {A B}, R A → Nonempty (FullHom B A) → R B

def FullArrow (A B C : FullObject P X) (k : ℕ) : Prop :=
  ∀ color : FullHom A C → Fin k, ∃ g : FullHom B C, ∃shade : Fin k,
    ∀f : FullHom A B, color (fullCompose g f) = shade

def FullRamsey (R : FullAge P X) : Prop :=
  ∀ A B, R A → R B → ∀k, 0 < k → ∃C, R C ∧ FullArrow A B C k

def FullJEP (R : FullAge P X) : Prop :=
  ∀ A B, R A → R B → ∃C, R C ∧ Nonempty (FullHom A C) ∧ Nonempty (FullHom B C)

def FullSAP (R : FullAge P X) : Prop :=
  ∀ E A B, R E → R A → R B → ∀(i : FullHom E A) (j : FullHom E B),
    ∃C, R C ∧ ∃(f : FullHom A C) (g : FullHom B C),
      (∀p, f.point (i.point p) = g.point (j.point p)) ∧
      ∀a b, f.point a = g.point b → ∃p, i.point p = a ∧ j.point p = b

/-- WHOLE closure under the actual OLD AND EXTRA full-ambient functions. -/
def pairSet (A : FullObject P X) (p q : A.task.old.Carrier) : Set A.task.old.Carrier :=
  A.unary.closure {p,q}

def pairClosure (A : FullObject P X) (p q : A.task.old.Carrier) : FullObject P X :=
  fullInduce A (pairSet A p q) (A.unary.isClosed_closure {p,q})

def pairLeft (A : FullObject P X) (p q : A.task.old.Carrier) : (pairClosure A p q).task.old.Carrier :=
  ⟨p,A.unary.subset_closure _ (by simp)⟩

def pairRight (A : FullObject P X) (p q : A.task.old.Carrier) : (pairClosure A p q).task.old.Carrier :=
  ⟨q,A.unary.subset_closure _ (by simp)⟩

def pairInclusion (A : FullObject P X) (p q : A.task.old.Carrier) : FullHom (pairClosure A p q) A :=
  fullInclusion A _ _

structure FullIso (A B : FullObject P X) where
  hom : FullHom A B
  surjective : Function.Surjective hom.point

/-- The COMPLETE expanded generated type with both marked roots. -/
structure PointedRealization (H : FullObject P X) (p q : H.task.old.Carrier)
    (A : FullObject P X) (x y : A.task.old.Carrier) where
  iso : FullIso H (pairClosure A x y)
  left : iso.hom.point p = pairLeft A x y
  right : iso.hom.point q = pairRight A x y

def PointedRealization.embedding {H : FullObject P X} {p q : H.task.old.Carrier}
    {A : FullObject P X} {x y : A.task.old.Carrier} (e : PointedRealization H p q A x y) : FullHom H A :=
  fullCompose (pairInclusion A x y) e.iso.hom

@[simp] theorem PointedRealization.embedding_left {H : FullObject P X}
    {p q : H.task.old.Carrier} {A : FullObject P X} {x y : A.task.old.Carrier}
    (e : PointedRealization H p q A x y) : e.embedding.point p = x := congrArg Subtype.val e.left

@[simp] theorem PointedRealization.embedding_right {H : FullObject P X}
    {p q : H.task.old.Carrier} {A : FullObject P X} {x y : A.task.old.Carrier}
    (e : PointedRealization H p q A x y) : e.embedding.point q = y := congrArg Subtype.val e.right

theorem embedding_determined_by_roots {H A : FullObject P X}
    {p q : H.task.old.Carrier} (generated : H.unary.closure {p,q} = Set.univ)
    {f g : FullHom H A} (hp : f.point p = g.point p) (hq : f.point q = g.point q) : f = g := by
  apply fullHom_ext
  intro x
  have hx : x ∈ H.unary.closure {p,q} := generated.symm ▸ Set.mem_univ x
  obtain ⟨r,hr,hrx⟩ := hx
  have hroot : f.point r = g.point r := by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact hp
    · exact hq
  induction hrx with
  | refl => exact hroot
  | @tail y z h hs ih =>
    obtain ⟨F,hF⟩ := hs
    have hf := f.unary.map_func F y z hF
    have hg := g.unary.map_func F y z hF
    rw [show f.unary.point y = g.unary.point y from ih] at hf
    exact A.unary.functional F _ _ _ hf hg

end CCO.ResetOrder.Unary
