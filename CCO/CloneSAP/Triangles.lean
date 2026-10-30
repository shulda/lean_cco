import CCO.CloneSAP.Amalgamation
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Finset.Image

/-! Triangle-definedness is expressed on literal complete named pair tables.
Local maps are INDUCED embeddings on every set of at most three vertices;
thus singleton and pair admissibility are checked, including empty palettes. -/
universe u v w z
namespace CCO.CloneSAP
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

abbrev FullCode := Σ i, Σ j, Option (S.Atom i j)

def eraseFull : FullCode (source S) → FullCode S :=
  fun c => ⟨c.1,c.2.1,c.2.2.bind (eraseAtom S)⟩

@[simp] theorem eraseFull_colour (p q : Sigma (Carrier X)) :
    eraseFull S (taggedColour (source S) p q) = taggedColour S (owner p) (owner q) := by
  simp only [eraseFull,taggedColour,colour_erase,owner]

def diagonalCode (c : FullCode S) : Prop := c.2.2 = none

@[simp] theorem diagonalCode_colour (p q : Sigma X) :
    diagonalCode S (taggedColour S p q) ↔ p = q := S.colour_none_iff p.2 q.2

/-- Local admissibility includes all actual named unary/pair data below size3. -/
def SmallEmbeddings {V : Type z} (c : V → V → FullCode S) : Prop :=
  ∀ (F : Finset V), F.card ≤ 3 → ∃ f : F ↪ Sigma X,
    ∀ a b, taggedColour S (f a) (f b) = c a.val b.val

/-- The usual triangle-defined finite complete age, stated without a syntactic
palette containing unused atoms. Any invalid complete code fails a local gate. -/
def TriangleDefined : Prop :=
  ∀ (V : Type z) [Finite V] (c : V → V → FullCode S),
    SmallEmbeddings S c → ∃ f : V ↪ Sigma X,
      ∀ a b, taggedColour S (f a) (f b) = c a b

namespace ClonePattern
variable {S : AtomicSource.{u,v,w} ι X} {V : Type z} [Finite V] [DecidableEq V] (c : V → V → FullCode (source S))
variable (small : SmallEmbeddings (source S) c)

def oldCode (x y : V) := eraseFull S (c x y)
def sameOwner (x y : V) := diagonalCode S (oldCode c x y)

include small

/-- Every tested triple simultaneously realizes its three owner equalities. -/
theorem triple (x y z : V) :
    ∃ f : ({x,y,z} : Finset V) ↪ Sigma (Carrier X),
      ∀ a b, taggedColour (source S) (f a) (f b) = c a.val b.val := by
  classical
  apply small
  exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ
    ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ (by simp))))

omit small in
theorem owner_local {F : Finset V} (f : F ↪ Sigma (Carrier X))
    (hf : ∀ a b, taggedColour (source S) (f a) (f b) = c a.val b.val) (a b : F) :
    oldCode c a.val b.val = taggedColour S (owner (f a)) (owner (f b)) := by
  rw [oldCode,← hf,eraseFull_colour]

omit small in
theorem sameOwner_local {F : Finset V} (f : F ↪ Sigma (Carrier X))
    (hf : ∀ a b, taggedColour (source S) (f a) (f b) = c a.val b.val) (a b : F) :
    sameOwner c a.val b.val ↔ owner (f a) = owner (f b) := by
  rw [sameOwner,owner_local c f hf,diagonalCode_colour]

/-- C06: two c-edges force the third, with actual logical diagonals retained. -/
theorem owner_equivalence : Equivalence (sameOwner c) := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro x
    obtain ⟨f,hf⟩ := triple c small x x x
    exact (sameOwner_local c f hf ⟨x,by simp⟩ ⟨x,by simp⟩).mpr rfl
  · intro x y h
    obtain ⟨f,hf⟩ := triple c small x y y
    let a : ({x,y,y} : Finset V) := ⟨x,by simp⟩
    let b : ({x,y,y} : Finset V) := ⟨y,by simp⟩
    exact (sameOwner_local c f hf b a).mpr (((sameOwner_local c f hf a b).mp h).symm)
  · intro x y z hxy hyz
    obtain ⟨f,hf⟩ := triple c small x y z
    let a : ({x,y,z} : Finset V) := ⟨x,by simp⟩
    let b : ({x,y,z} : Finset V) := ⟨y,by simp⟩
    let d : ({x,y,z} : Finset V) := ⟨z,by simp⟩
    exact (sameOwner_local c f hf a d).mpr
      (((sameOwner_local c f hf a b).mp hxy).trans ((sameOwner_local c f hf b d).mp hyz))

/-- C07: actual c,a,b triangles force identical old labels at either endpoint. -/
theorem oldCode_congr_left {x y : V} (hxy : sameOwner c x y) (z : V) :
    oldCode c x z = oldCode c y z := by
  classical
  obtain ⟨f,hf⟩ := triple c small x y z
  let a : ({x,y,z} : Finset V) := ⟨x,by simp⟩
  let b : ({x,y,z} : Finset V) := ⟨y,by simp⟩
  let d : ({x,y,z} : Finset V) := ⟨z,by simp⟩
  have he := (sameOwner_local c f hf a b).mp hxy
  rw [show oldCode c x z = _ from owner_local c f hf a d,
    show oldCode c y z = _ from owner_local c f hf b d,he]

theorem oldCode_congr_right {x y : V} (hxy : sameOwner c x y) (z : V) :
    oldCode c z x = oldCode c z y := by
  classical
  obtain ⟨f,hf⟩ := triple c small x y z
  let a : ({x,y,z} : Finset V) := ⟨x,by simp⟩
  let b : ({x,y,z} : Finset V) := ⟨y,by simp⟩
  let d : ({x,y,z} : Finset V) := ⟨z,by simp⟩
  have he := (sameOwner_local c f hf a b).mp hxy
  rw [show oldCode c z x = _ from owner_local c f hf d a,
    show oldCode c z y = _ from owner_local c f hf d b,he]

/-- The complete diagram's literal clone-kernel quotient. -/
def ownerSetoid : Setoid V := ⟨sameOwner c,owner_equivalence c small⟩
abbrev Owners := Quotient (ownerSetoid c small)
def classOf (x : V) : Owners c small := Quotient.mk _ x
noncomputable def rep (q : Owners c small) : V := q.out

@[simp] theorem class_rep (q : Owners c small) : classOf c small (rep c small q) = q :=
  Quotient.out_eq q

theorem rep_class (x : V) : sameOwner c (rep c small (classOf c small x)) x :=
  Quotient.exact (class_rep c small (classOf c small x))

noncomputable def quotientCode (q r : Owners c small) : FullCode S :=
  oldCode c (rep c small q) (rep c small r)

@[simp] theorem quotientCode_class (x y : V) :
    quotientCode c small (classOf c small x) (classOf c small y) = oldCode c x y := by
  unfold quotientCode
  exact (oldCode_congr_left c small (rep_class c small x) _).trans
    (oldCode_congr_right c small (rep_class c small y) _)

/-- C08: every small complete owner quotient object has actual old types. -/
theorem quotient_small : SmallEmbeddings S (quotientCode c small) := by
  classical
  intro F hF
  let r : F ↪ V := {
    toFun q := rep c small q.val
    inj' := by
      intro q r he
      apply Subtype.ext
      exact (class_rep c small q.val).symm.trans ((congrArg (classOf c small) he).trans (class_rep c small r.val)) }
  let E : Finset V := (Finset.univ : Finset F).map r
  have hE : E.card ≤ 3 := by simpa only [E,Finset.card_map,Finset.card_univ,Fintype.card_coe] using hF
  obtain ⟨f,hf⟩ := small E hE
  let rr : F → E := fun q => ⟨r q,by simp only [E,Finset.mem_map]; exact ⟨q,Finset.mem_univ _,rfl⟩⟩
  let g : F → Sigma X := fun q => owner (f (rr q))
  have hg : Function.Injective g := by
    intro q r he
    apply Subtype.ext
    rw [← class_rep c small q.val,← class_rep c small r.val]
    apply Quotient.sound
    exact (sameOwner_local c f hf (rr q) (rr r)).mpr he
  refine ⟨⟨g,hg⟩,?_⟩
  intro q r
  exact (owner_local c f hf (rr q) (rr r)).symm

/-- C09: old triangle-definedness and genuine fresh indices realize the
complete clone diagram inducedly, with no CCO or amalgamation assumption. -/
theorem realize (triangles : TriangleDefined.{u,v,w,z} S) :
    ∃ f : V ↪ Sigma (Carrier X), ∀ a b, taggedColour (source S) (f a) (f b) = c a b := by
  classical
  letI : Finite (Owners c small) := Quotient.finite _
  obtain ⟨g,hg⟩ := triangles (Owners c small) (quotientCode c small) (quotient_small c small)
  obtain ⟨f,hf⟩ := fresh_lift (fun x => g (classOf c small x))
  refine ⟨f,?_⟩
  intro x y
  obtain ⟨l,hl⟩ := triple c small x y y
  let a : ({x,y,y} : Finset V) := ⟨x,by simp⟩
  let b : ({x,y,y} : Finset V) := ⟨y,by simp⟩
  have ho : taggedColour S (owner (f x)) (owner (f y)) =
      taggedColour S (owner (l a)) (owner (l b)) := by
    rw [hf,hf,hg,quotientCode_class]
    exact owner_local c l hl a b
  have hd : f x = f y ↔ l a = l b := by
    constructor
    · intro he
      have : x = y := f.injective he
      subst y
      rfl
    · intro he
      have : x = y := congrArg Subtype.val (l.injective he)
      exact congrArg f this
  exact (tagged_reconstruct S ho hd).trans (hl a b)

end ClonePattern

/-- The genuine clone triangle-definedness export. -/
theorem triangle_defined (triangles : TriangleDefined.{u,v,w,z} S) :
    TriangleDefined.{u,v,w,z} (source S) := by
  classical
  intro V _ c hc
  exact ClonePattern.realize c hc triangles

end CCO.CloneSAP
