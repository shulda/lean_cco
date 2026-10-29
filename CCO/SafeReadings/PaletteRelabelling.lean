import CCO.SafeReadings.MenuCalculus
import CCO.StrongExact.ExactConverse

/-! Pure tagged action from actual literal palette transport and the
actual triangle table. Original exactness is DERIVED by positive-word
transport; it is not an additional provider field. -/
universe u v w z t
namespace CCO.SafeReadings
open Selectors StrongExact
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable (Γ : Type z) [Group Γ] (N : Type t)

structure PaletteRelabelling where
  owner : Γ →* Equiv.Perm ι
  label : ∀ {i j}, S.Atom i j → N
  label_injective : ∀ i j, Function.Injective (@label i j)
  transport : ∀ g {i j} (a : S.Atom i j),
    ∃ b : S.Atom (owner g i) (owner g j), label b = label a
  converse_label : ∀ {i j} (a : S.Atom i j), label (S.conv a) = label a
  triangle : ∀ g {i j k} (a : S.Atom i j) (b : S.Atom j k) (c : S.Atom i k)
    (a' : S.Atom (owner g i) (owner g j)) (b' : S.Atom (owner g j) (owner g k))
    (c' : S.Atom (owner g i) (owner g k)),
    label a' = label a → label b' = label b → label c' = label c →
    (S.Triangle a b c ↔ S.Triangle a' b' c')

namespace PaletteRelabelling
variable {S Γ N} (P : PaletteRelabelling S Γ N)
noncomputable section

def castAtom {i j i' j'} (hi : i = i') (hj : j = j') (a : S.Atom i j) : S.Atom i' j' :=
  hi ▸ hj ▸ a

theorem label_cast {i j i' j'} (hi : i = i') (hj : j = j') (a : S.Atom i j) :
    P.label (castAtom hi hj a) = P.label a := by cases hi; cases hj; rfl

def atomMove (g : Γ) {i j} (a : S.Atom i j) : S.Atom (P.owner g i) (P.owner g j) :=
  Classical.choose (P.transport g a)

theorem atomMove_label (g : Γ) {i j} (a : S.Atom i j) :
    P.label (P.atomMove g a) = P.label a := Classical.choose_spec (P.transport g a)

theorem owner_inv (g : Γ) (i : ι) : P.owner g⁻¹ (P.owner g i) = i := by
  have hh := congrArg (fun e : Equiv.Perm ι => e i) (P.owner.map_mul g⁻¹ g)
  simpa only [inv_mul_cancel,map_one,Equiv.Perm.one_apply,Equiv.Perm.mul_apply] using hh.symm

theorem atomMove_bijective (g : Γ) (i j) : Function.Bijective (fun a : S.Atom i j => P.atomMove g a) := by
  constructor
  · intro a b he
    apply P.label_injective i j
    simpa only [P.atomMove_label] using congrArg P.label he
  · intro b
    obtain ⟨a,ha⟩ := P.transport g⁻¹ b
    let a' : S.Atom i j := castAtom (P.owner_inv g i) (P.owner_inv g j) a
    refine ⟨a',?_⟩
    apply P.label_injective
    exact (P.atomMove_label g a').trans ((P.label_cast _ _ a).trans ha)

def atomEquiv (g : Γ) (i j) : S.Atom i j ≃ S.Atom (P.owner g i) (P.owner g j) :=
  Equiv.ofBijective (P.atomMove g) (P.atomMove_bijective g i j)

def menuMove (g : Γ) {i j} (D : S.Menu i j) : S.Menu (P.owner g i) (P.owner g j) := P.atomEquiv g i j '' D

def move (g : Γ) (D : TaggedMenu S) : TaggedMenu S :=
  ⟨P.owner g D.1,P.owner g D.2.1,P.menuMove g D.2.2⟩

theorem names_move (g : Γ) (D : TaggedMenu S) : names S P.label (P.move g D) = names S P.label D := by
  rcases D with ⟨i,j,D⟩
  ext n
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,he⟩
    exact ⟨a,ha,(P.atomMove_label g a).symm.trans he⟩
  · rintro ⟨a,ha,he⟩
    exact ⟨P.atomMove g a,⟨a,ha,rfl⟩,(P.atomMove_label g a).trans he⟩

theorem tagged_eq {D E : TaggedMenu S} (hp : Parallel S D E)
    (hn : names S P.label D = names S P.label E) : D = E := by
  rcases D with ⟨i,j,D⟩
  rcases E with ⟨i',j',E⟩
  rcases hp with ⟨hi,hj⟩
  cases hi; cases hj
  have he : D = E := by
    ext a
    constructor
    · intro ha
      obtain ⟨b,hb,hbname⟩ := hn ▸ (show P.label a ∈ names S P.label ⟨i,j,D⟩ from ⟨a,ha,rfl⟩)
      exact P.label_injective i j hbname ▸ hb
    · intro ha
      obtain ⟨b,hb,hbname⟩ := hn.symm ▸ (show P.label a ∈ names S P.label ⟨i,j,E⟩ from ⟨a,ha,rfl⟩)
      exact P.label_injective i j hbname ▸ hb
  rw [he]

theorem move_one (D : TaggedMenu S) : P.move 1 D = D := by
  apply P.tagged_eq
  · constructor <;> simp only [move,map_one,Equiv.Perm.one_apply]
  · exact P.names_move _ _

theorem move_mul (g h : Γ) (D : TaggedMenu S) : P.move (g*h) D = P.move g (P.move h D) := by
  apply P.tagged_eq
  · constructor <;> simp only [move,map_mul,Equiv.Perm.mul_apply]
  · rw [P.names_move,P.names_move,P.names_move]

def action (g : Γ) : TaggedMenu S ≃ TaggedMenu S where
  toFun := P.move g
  invFun := P.move g⁻¹
  left_inv D := by rw [← P.move_mul,inv_mul_cancel,P.move_one]
  right_inv D := by rw [← P.move_mul,mul_inv_cancel,P.move_one]

theorem names_flip (D : TaggedMenu S) : names S P.label (flip S D) = names S P.label D := by
  rcases D with ⟨i,j,D⟩
  ext n
  constructor
  · rintro ⟨a,ha,he⟩
    exact ⟨S.conv a,ha,(P.converse_label a).trans he⟩
  · rintro ⟨a,ha,he⟩
    exact ⟨S.conv a,S.mem_opposite ha,(P.converse_label a).trans he⟩

theorem move_flip (g : Γ) (D : TaggedMenu S) : P.move g (flip S D) = flip S (P.move g D) := by
  apply P.tagged_eq
  · exact ⟨rfl,rfl⟩
  · rw [P.names_move,P.names_flip,P.names_flip,P.names_move]

theorem menuMove_product (g : Γ) {i j k} (D : S.Menu i j) (E : S.Menu j k) :
    P.menuMove g (S.product D E) = S.product (P.menuMove g D) (P.menuMove g E) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨c,⟨a,ha,b,hb,ht⟩,rfl⟩
    exact ⟨P.atomMove g a,⟨a,ha,rfl⟩,P.atomMove g b,⟨b,hb,rfl⟩,
      (P.triangle g a b c _ _ _ (P.atomMove_label g a) (P.atomMove_label g b) (P.atomMove_label g c)).mp ht⟩
  · rintro c' ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,ht⟩
    obtain ⟨c,hc⟩ := (P.atomMove_bijective g i k).2 c'
    refine ⟨c,⟨a,ha,b,hb,?_⟩,hc⟩
    apply (P.triangle g a b c _ _ c' (P.atomMove_label g a) (P.atomMove_label g b) _).mpr ht
    rw [← hc]; exact P.atomMove_label g c

@[simp] theorem menuMove_singleton (g : Γ) {i j} (a : S.Atom i j) :
    P.menuMove g {a} = {P.atomMove g a} := Set.image_singleton

theorem menuMove_present (g : Γ) {i j} (ws : List (PositiveWord S i j)) :
    ∃ vs : List (PositiveWord S (P.owner g i) (P.owner g j)),
      P.menuMove g (present S ws) = present S vs := by
  have hWord : ∀ {i j} (word : PositiveWord S i j),
      ∃ target : PositiveWord S (P.owner g i) (P.owner g j),
        P.menuMove g (PositiveWord.profile S word) = PositiveWord.profile S target := by
    intro i j word
    induction word with
    | single a => exact ⟨.single (P.atomMove g a),P.menuMove_singleton g a⟩
    | cons a rest ih =>
      obtain ⟨tail,htail⟩ := ih
      exact ⟨.cons (P.atomMove g a) tail,by rw [PositiveWord.profile,P.menuMove_product,P.menuMove_singleton,htail]; rfl⟩
  induction ws with
  | nil =>
    refine ⟨[],?_⟩
    rw [present_nil,present_nil]
    exact Set.image_univ.trans (P.atomEquiv g i j).surjective.range_eq
  | cons word rest ih =>
    obtain ⟨target,ht⟩ := hWord word
    obtain ⟨vs,hvs⟩ := ih
    refine ⟨target :: vs,?_⟩
    rw [present_cons,present_cons,menuMove,Set.image_inter (P.atomEquiv g i j).injective]
    exact congrArg₂ (fun A B : S.Menu _ _ => A ∩ B) ht hvs

theorem move_exact (g : Γ) {D : TaggedMenu S} (hD : IsExact S D) : IsExact S (P.move g D) := by
  rcases D with ⟨i,j,D⟩
  change Exact S D at hD
  obtain ⟨hne,ws,he⟩ := hD
  subst D
  obtain ⟨vs,hvs⟩ := P.menuMove_present g ws
  exact ⟨Set.Nonempty.image (P.atomEquiv g i j) hne,vs,hvs⟩

def pureAction : PureTagAction S Γ N where
  tag := fun g => P.owner g
  act := P.action
  one := P.move_one
  mul := P.move_mul
  source := fun _ _ => rfl
  target := fun _ _ => rfl
  label := P.label
  label_injective := P.label_injective
  literal := P.names_move
  exact := by
    intro g D
    constructor
    · intro hd
      change IsExact S (P.move g D) at hd
      have hh := P.move_exact g⁻¹ hd
      simpa only [← P.move_mul,inv_mul_cancel,P.move_one] using hh
    · exact P.move_exact g
  opposite := P.move_flip
  product := by
    rintro g _ _ _ ⟨i,j,k,D,E,rfl,rfl,rfl⟩
    exact ⟨P.owner g i,P.owner g j,P.owner g k,P.menuMove g D,P.menuMove g E,rfl,rfl,
      by change (⟨_,_,P.menuMove g (S.product D E)⟩ : TaggedMenu S) = _; rw [P.menuMove_product]⟩

theorem literalConverse : LiteralConverse S P.pureAction := P.converse_label
end
end PaletteRelabelling
end CCO.SafeReadings
