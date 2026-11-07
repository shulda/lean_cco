import CCO.APRamseyReadout.TupleSupport
import CCO.TerminalHiddenHN.FiniteOrderExtension

/-! Orders on the ENTIRE coordinate-generated support of a marked old
object. Restriction and extension follow the same original induced map
through its proved canonical support embedding. No order on the ambient
infinite hidden structure, Ramsey witness, or new tuple provider is used. -/

universe u v w r l k
namespace CCO.APRamseyReadout.TupleInterpretation
open CCO.FullCode
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable {L : Language.{l}} {V : Type k}
variable {S : CCO.AtomicSource.{u,v,w} ι X} {C : Structure L V} {scheme : RootScheme L}
variable (D : TupleInterpretation (G := G) S C scheme)

/-- The sole expansion datum is an actual global order on every point
of the full generated support, not just on its displayed coordinates. -/
structure ReadoutOn (A : CCO.FiniteInduced (X := X)) where
  order : LinearOrder (D.support A)

@[ext] theorem ReadoutOn.ext {A : CCO.FiniteInduced (X := X)}
    {a b : D.ReadoutOn A} (h : a.order = b.order) : a = b := by
  cases a
  cases b
  cases h
  rfl

def ReadoutComparison {A : CCO.FiniteInduced (X := X)}
    (a : D.ReadoutOn A) (x y : D.support A) : Prop :=
  @LT.lt (D.support A) a.order.toLT x y

/-- Ordered support maps keep the supplied original old map literally.
All comparisons use its canonical full induced support extension. -/
structure ReadoutEmbedding (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (a : D.ReadoutOn A) (b : D.ReadoutOn B) where
  old : CCO.InducedEmbedding S A B
  order_iff : ∀ x y,
    @LT.lt _ b.order.toLT ((D.supportEmbedding H old).point x)
      ((D.supportEmbedding H old).point y) ↔ @LT.lt _ a.order.toLT x y

namespace ReadoutEmbedding
variable {D}

def id (H : CCO.HomogeneousSource S G) {A : CCO.FiniteInduced (X := X)} (a : D.ReadoutOn A) :
    D.ReadoutEmbedding H a a :=
  ⟨oldId A,by intro x y; rw [D.supportEmbedding_id]; rfl⟩

def comp (H : CCO.HomogeneousSource S G) {A B E : CCO.FiniteInduced (X := X)}
    {a : D.ReadoutOn A} {b : D.ReadoutOn B} {c : D.ReadoutOn E}
    (g : D.ReadoutEmbedding H b c) (f : D.ReadoutEmbedding H a b) :
    D.ReadoutEmbedding H a c :=
  ⟨oldComp g.old f.old,by
    intro x y
    rw [D.supportEmbedding_comp]
    exact (g.order_iff _ _).trans (f.order_iff x y)⟩

/-- Expanded maps have no additional data beyond their old point map. -/
@[ext] theorem ext (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    {f g : D.ReadoutEmbedding H a b}
    (h : ∀ x, f.old.toEmbedding x = g.old.toEmbedding x) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have he : f = g := by
        cases f
        cases g
        have hp := Function.Embedding.ext h
        cases hp
        rfl
      cases he
      rfl

@[simp] theorem comp_id (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (f : D.ReadoutEmbedding H a b) : f.comp H (id H a) = f :=
  ext H (fun _ => rfl)

@[simp] theorem id_comp (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (f : D.ReadoutEmbedding H a b) : (id H b).comp H f = f :=
  ext H (fun _ => rfl)

theorem comp_assoc (H : CCO.HomogeneousSource S G)
    {A B E F : CCO.FiniteInduced (X := X)}
    {a : D.ReadoutOn A} {b : D.ReadoutOn B} {c : D.ReadoutOn E} {d : D.ReadoutOn F}
    (h : D.ReadoutEmbedding H c d) (g : D.ReadoutEmbedding H b c)
    (f : D.ReadoutEmbedding H a b) :
    (h.comp H g).comp H f = h.comp H (g.comp H f) :=
  ext H (fun _ => rfl)

end ReadoutEmbedding

theorem readout_comparison_iff (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} {a : D.ReadoutOn A} {b : D.ReadoutOn B}
    (f : D.ReadoutEmbedding H a b) (x y : D.support A) :
    D.ReadoutComparison b ((D.supportEmbedding H f.old).point x)
        ((D.supportEmbedding H f.old).point y) ↔ D.ReadoutComparison a x y :=
  f.order_iff x y

/-- Restriction pulls back the exact target order along the canonical
embedding of the entire support of this same supplied old map. -/
def restrictReadout (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B)
    (b : D.ReadoutOn B) : D.ReadoutOn A := by
  letI : LinearOrder (D.support B) := b.order
  exact ⟨LinearOrder.lift' (D.supportEmbedding H e).point (D.supportEmbedding H e).injective⟩

def restrictReadoutEmbedding (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B)
    (b : D.ReadoutOn B) : D.ReadoutEmbedding H (D.restrictReadout H e b) b :=
  ⟨e,fun _ _ => Iff.rfl⟩

@[simp] theorem restrictReadoutEmbedding_old (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B)
    (b : D.ReadoutOn B) : (D.restrictReadoutEmbedding H e b).old = e := rfl

theorem comparison_restrict (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B)
    (b : D.ReadoutOn B) (x y : D.support A) :
    D.ReadoutComparison (D.restrictReadout H e b) x y ↔
      D.ReadoutComparison b ((D.supportEmbedding H e).point x)
        ((D.supportEmbedding H e).point y) := Iff.rfl

@[simp] theorem restrictReadout_id (H : CCO.HomogeneousSource S G)
    {A : CCO.FiniteInduced (X := X)} (a : D.ReadoutOn A) :
    D.restrictReadout H (oldId A) a = a := by
  apply ReadoutOn.ext
  apply LinearOrder.ext_lt
  intro x y
  change @LT.lt _ a.order.toLT ((D.supportEmbedding H (oldId A)).point x)
      ((D.supportEmbedding H (oldId A)).point y) ↔ @LT.lt _ a.order.toLT x y
  rw [D.supportEmbedding_id]
  rfl

theorem restrictReadout_comp (H : CCO.HomogeneousSource S G)
    {A B E : CCO.FiniteInduced (X := X)}
    (g : CCO.InducedEmbedding S B E) (f : CCO.InducedEmbedding S A B)
    (c : D.ReadoutOn E) :
    D.restrictReadout H (oldComp g f) c = D.restrictReadout H f (D.restrictReadout H g c) := by
  apply ReadoutOn.ext
  apply LinearOrder.ext_lt
  intro x y
  change @LT.lt _ c.order.toLT ((D.supportEmbedding H (oldComp g f)).point x)
      ((D.supportEmbedding H (oldComp g f)).point y) ↔
    @LT.lt _ c.order.toLT ((D.supportEmbedding H g).point ((D.supportEmbedding H f).point x))
      ((D.supportEmbedding H g).point ((D.supportEmbedding H f).point y))
  rw [D.supportEmbedding_comp]
  rfl

theorem readout_nonempty (A : CCO.FiniteInduced (X := X)) : Nonempty (D.ReadoutOn A) := by
  letI : Fintype (D.support A) := Fintype.ofFinite _
  exact ⟨⟨LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective⟩⟩

/-- The fixed old carrier has finitely many order expansions because
the entire coordinate-generated support is finite. -/
theorem readout_precompact (A : CCO.FiniteInduced (X := X)) : Finite (D.ReadoutOn A) := by
  apply Finite.of_injective (fun a : D.ReadoutOn A => fun x y => @LT.lt _ a.order.toLT x y)
  intro a b h
  apply ReadoutOn.ext
  apply LinearOrder.ext_lt
  intro x y
  exact Iff.of_eq (congrFun (congrFun h x) y)

/-- Extend the prescribed order on ALL source support points through
the same original map. No compatibility or ambient-order premise occurs. -/
theorem readout_reasonable (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B)
    (a : D.ReadoutOn A) :
    ∃ b : D.ReadoutOn B, D.restrictReadout H e b = a := by
  letI : LinearOrder (D.support A) := a.order
  obtain ⟨o,ho⟩ := CCO.TerminalHiddenHN.finite_linearOrder_extension
    (D.supportEmbedding H e).point (D.supportEmbedding H e).injective
  refine ⟨⟨o⟩,?_⟩
  apply ReadoutOn.ext
  apply LinearOrder.ext_lt
  exact ho

theorem readout_reasonable_lift (H : CCO.HomogeneousSource S G)
    {A B : CCO.FiniteInduced (X := X)} (e : CCO.InducedEmbedding S A B)
    (a : D.ReadoutOn A) :
    ∃ (b : D.ReadoutOn B) (f : D.ReadoutEmbedding H a b), f.old = e := by
  obtain ⟨b,hb⟩ := D.readout_reasonable H e a
  subst a
  exact ⟨b,D.restrictReadoutEmbedding H e b,rfl⟩

end
end CCO.APRamseyReadout.TupleInterpretation
