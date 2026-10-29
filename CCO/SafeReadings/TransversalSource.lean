import CCO.OwnerTransversal.TransversalInstance
import CCO.OwnerTransversal.TransversalInfinite
import CCO.OwnerTransversal.Primitivity
import CCO.OwnerTransversal.TransversalCompletion

/-! The actual typed source on the owner fibres of the INTERNALLY
constructed transversal U. Its atoms retain literal original names and
are proved non-F; this is not the original named carrier containing F. -/

open scoped FirstOrder
open FirstOrder FirstOrder.Language

universe v w t
namespace CCO.SafeReadings.TransversalSource
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open OwnerTransversal

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R))

abbrev Carrier (b : ↥B) := OwnerFibre S H R B (TransversalAge.model S H R B) b
abbrev Motion := TableAut S H R B (TransversalAge.limitTable S H R B)

def Nonthin (a : S.Atom () ()) : Prop :=
  ∀ x y : M, col S x y = some a → ¬ finitePacket S H x y

include H R in
theorem realized_nonthin (x y : TransversalAge.U S H R B) (a : S.Atom () ())
    (ha : (TransversalAge.limitTable S H R B).colour x y = some a) : Nonthin S H a := by
  have hxy : x ≠ y := by
    rintro rfl
    rw [TransversalAge.colour_diag S H R B] at ha
    cases ha
  obtain ⟨p,q,_,_,hpq,hn⟩ := (TransversalAge.model S H R B).realize_pair x y hxy
  intro u v huv hF
  have hc : S.colour p.val q.val = S.colour u v := hpq.trans (ha.trans huv.symm)
  exact hn ((finitePacket S H).property _ _ _ _ hc |>.mpr hF)

abbrev Palette (b c : ↥B) := {a : S.Atom () () // Nonthin S H a ∧
  ∃ (x : Carrier S H R B b) (y : Carrier S H R B c),
    (TransversalAge.limitTable S H R B).colour x.val y.val = some a}

def colour {b c : ↥B} (x : Carrier S H R B b) (y : Carrier S H R B c) :
    Option (Palette S H R B b c) :=
  match hc : (TransversalAge.limitTable S H R B).colour x.val y.val with
  | none => none
  | some a => some ⟨a,realized_nonthin S H R B x.val y.val a hc,x,y,hc⟩

theorem colour_map {b c : ↥B} (x : Carrier S H R B b) (y : Carrier S H R B c) :
    (colour S H R B x y).map Subtype.val = (TransversalAge.limitTable S H R B).colour x.val y.val := by
  unfold colour
  split <;> rename_i h <;> exact h.symm

theorem colour_some_iff {b c : ↥B} (x : Carrier S H R B b) (y : Carrier S H R B c)
    (a : Palette S H R B b c) :
    colour S H R B x y = some a ↔ (TransversalAge.limitTable S H R B).colour x.val y.val = some a.val := by
  constructor
  · intro h
    rw [← colour_map S H R B x y,h]
    rfl
  · intro h
    unfold colour
    split
    next hc => rw [hc] at h; cases h
    next d hc =>
      apply congrArg some
      exact Subtype.ext (Option.some.inj (hc.symm.trans h))

def converse {b c : ↥B} (a : Palette S H R B b c) : Palette S H R B c b :=
  ⟨a.val,a.property.1,by
    obtain ⟨x,y,hxy⟩ := a.property.2
    exact ⟨y,x,(TransversalAge.colour_symm S H R B y.val x.val).trans hxy⟩⟩

def sigmaEquiv : (Σ b : ↥B, Carrier S H R B b) ≃ TransversalAge.U S H R B where
  toFun p := p.2.val
  invFun x := ⟨(TransversalAge.limitTable S H R B).owner x,⟨x,rfl⟩⟩
  left_inv := by
    rintro ⟨b,⟨x,hx⟩⟩
    cases hx
    rfl
  right_inv _ := rfl

def source : AtomicSource.{v,0,w} ↥B (Carrier S H R B) where
  Atom := Palette S H R B
  finiteSort := Fintype.ofFinite _
  finiteAtom := fun _ _ => by
    let := S.finiteAtom () ()
    exact Fintype.ofFinite _
  nonemptySort := by
    intro b
    obtain ⟨x,hx⟩ := (TransversalAge.owner_sort_infinite S H R B b).nonempty
    exact ⟨⟨x,hx⟩⟩
  conv := converse S H R B
  conv_invol := fun _ => Subtype.ext rfl
  symmetricLoop := fun _ => Subtype.ext rfl
  colour := colour S H R B
  colour_none_iff := by
    intro b c x y
    constructor
    · intro hc
      have hn : (TransversalAge.limitTable S H R B).colour x.val y.val = none := by
        rw [← colour_map S H R B x y,hc]
        rfl
      exact (sigmaEquiv S H R B).injective ((TransversalAge.colour_none S H R B _ _).mp hn)
    · intro he
      apply Option.map_eq_none_iff.mp
      rw [colour_map]
      exact (TransversalAge.colour_none S H R B _ _).mpr (congrArg (sigmaEquiv S H R B) he)
  colour_swap := by
    intro b c x y a
    rw [colour_some_iff,colour_some_iff]
    exact Iff.of_eq (congrArg (fun d => d = some a.val) (TransversalAge.colour_symm S H R B x.val y.val))
  realized := by
    intro b c a
    obtain ⟨x,y,hxy⟩ := a.property.2
    exact ⟨x,y,(colour_some_iff S H R B x y a).mpr hxy⟩

theorem literal_converse {b c : ↥B} (a : (source S H R B).Atom b c) :
    ((source S H R B).conv a).val = a.val := rfl

theorem colour_eq_iff {b c : ↥B} (x x' : Carrier S H R B b) (y y' : Carrier S H R B c) :
    (source S H R B).colour x y = (source S H R B).colour x' y' ↔
      (TransversalAge.limitTable S H R B).colour x.val y.val = (TransversalAge.limitTable S H R B).colour x'.val y'.val := by
  constructor
  · intro hh
    exact (colour_map S H R B x y).symm.trans
      ((congrArg (Option.map Subtype.val) hh).trans (colour_map S H R B x' y'))
  · intro hh
    apply Option.map_injective Subtype.val_injective
    exact (colour_map S H R B x y).trans (hh.trans (colour_map S H R B x' y').symm)

theorem tagged_eq {p q p' q' : Σ b : ↥B, Carrier S H R B b}
    (hp : p.1 = p'.1) (hq : q.1 = q'.1)
    (hc : (TransversalAge.limitTable S H R B).colour p.2.val q.2.val =
      (TransversalAge.limitTable S H R B).colour p'.2.val q'.2.val) :
    taggedColour (source S H R B) p q = taggedColour (source S H R B) p' q' := by
  rcases p with ⟨b,x⟩; rcases p' with ⟨b',x'⟩
  rcases q with ⟨c,y⟩; rcases q' with ⟨c',y'⟩
  dsimp at hp hq
  subst b'; subst c'
  let combine (z : Option (Palette S H R B b c)) :
      Σ b : ↥B, Σ c : ↥B, Option (Palette S H R B b c) := ⟨b,⟨c,z⟩⟩
  exact congrArg combine ((colour_eq_iff S H R B x x' y y').mpr hc)

def forgetColour (c : Σ b : ↥B, Σ d : ↥B, Option (Palette S H R B b d)) :
    FullColour S := c.2.2.map Subtype.val

@[simp] theorem forget_tagged (p q : Σ b : ↥B, Carrier S H R B b) :
    forgetColour S H R B (taggedColour (source S H R B) p q) =
      (TransversalAge.limitTable S H R B).colour p.2.val q.2.val := colour_map S H R B _ _

instance motionAction : MulAction (Motion S H R B) (Σ b : ↥B, Carrier S H R B b) where
  smul g p := (sigmaEquiv S H R B).symm (g.val ((sigmaEquiv S H R B) p))
  one_smul p := (sigmaEquiv S H R B).symm_apply_apply p
  mul_smul g h p := by
    change _ = (sigmaEquiv S H R B).symm
      (g.val ((sigmaEquiv S H R B) ((sigmaEquiv S H R B).symm (h.val _))))
    rw [Equiv.apply_symm_apply]
    rfl

theorem motion_sort (g : Motion S H R B) (p : Σ b : ↥B, Carrier S H R B b) :
    (g • p).1 = p.1 := (TableAut.owner g p.2.val).trans p.2.property

theorem homogeneous : HomogeneousSource (source S H R B) (Motion S H R B) where
  preserves_sort := motion_sort S H R B
  preserves_colours g p q := tagged_eq S H R B (motion_sort S H R B g p)
    (motion_sort S H R B g q) (TableAut.colour g p.2.val q.2.val)
  extends_finite_diagram f h hc := by
    have ho (i) : (TransversalAge.limitTable S H R B).owner (f i).2.val =
        (TransversalAge.limitTable S H R B).owner (h i).2.val := by
      exact (f i).2.property.trans
        ((congrArg (fun z => z.1) (hc i i)).trans (h i).2.property.symm)
    have hcol (i j) : (TransversalAge.limitTable S H R B).colour (f i).2.val (f j).2.val =
        (TransversalAge.limitTable S H R B).colour (h i).2.val (h j).2.val := by
      simpa only [forget_tagged] using congrArg (forgetColour S H R B) (hc i j)
    obtain ⟨g,hg⟩ := TransversalAge.tuple_homogeneous S H R B (fun i => (f i).2.val)
      (fun i => (h i).2.val) ho hcol
    have hp := (TransversalAge.limitCoding S H R B).embedding_preserves
      (TransversalAge.limitCoding S H R B) g.toEmbedding
    let k : Motion S H R B := ⟨g.toEquiv,
      (fun b x => (congrArg (· = b) (hp.1 x)).to_iff),
      (fun c x y => (congrArg (· = c) (hp.2 x y)).to_iff)⟩
    refine ⟨k,fun i => ?_⟩
    apply (sigmaEquiv S H R B).injective
    exact hg i

theorem primitive (b : ↥B) (Q : Setoid (Carrier S H R B b))
    (invariant : ∀ g : Motion S H R B, ∀ x y, Q x y →
      Q (OwnerTransversal.fibrePerm S H R B (TransversalAge.model S H R B) b g x)
        (OwnerTransversal.fibrePerm S H R B (TransversalAge.model S H R B) b g y)) : Q = ⊥ ∨ Q = ⊤ :=
  (⟨Q,invariant⟩ : SortEquivalence S H R B (TransversalAge.model S H R B) b).eqv_eq_bot_or_top

end
end CCO.SafeReadings.TransversalSource
