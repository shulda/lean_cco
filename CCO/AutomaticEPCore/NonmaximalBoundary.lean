import CCO.Finite
import CCO.SIR.Positive.Direct.Homogeneity
import CCO.StrongExact.AgeAP
import CCO.APCharacter.Rank.Source
import CCO.ParityHasse.Original.Equivalences
import CCO.ExactCRT.ExactLattice
import Mathlib.Data.Finset.Lattice.Fold
import Lean.Elab.Tactic.Omega
import CCO.RealClosure.Bounds.Examples.CycleConsistency
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Countable
import Mathlib.Logic.Encodable.Basic

/-! B063 D10/C60: the literal four-atom countably infinite source and its
actual four-label support table. This module proves the concrete table
obstruction directly; no automatic-core or maximal-character theorem is
used to certify a deliberately nonmaximal orientation. -/

universe z
namespace CCO.AutomaticEPCore.NonmaximalBoundary
open CCO.RealClosure.Bounds.Examples

abbrev Block := Nat × Bool
abbrev Atom := Bool × Bool
abbrev Label := Bool × Bool

structure Point where
  block : Block
  bit : Bool
  clone : Nat
  deriving DecidableEq

instance : Inhabited Point := ⟨⟨(0,false),false,0⟩⟩
instance : Countable Point := Function.Injective.countable
  (f := fun x : Point => (x.block,x.bit,x.clone)) (by
    intro x y h
    cases x; cases y
    simpa only [Prod.mk.injEq,Point.mk.injEq] using h)
instance : Infinite Point := Infinite.of_injective
  (fun n : Nat => (⟨(0,false),false,n⟩ : Point)) (by
    intro m n h
    exact congrArg Point.clone h)

/-- The atom records same-block incidence and the actual global bit gain.
`(true,false)` is genuine clone diversity, never logical equality. -/
def pattern (x y : Point) : Atom := (decide (x.block = y.block),x.bit ^^ y.bit)

def colour (x y : Point) : Option Atom :=
  if x = y then none else some (pattern x y)

@[simp] theorem colour_none (x y : Point) : colour x y = none ↔ x = y := by
  simp [colour]

@[simp] theorem colour_some (x y : Point) (a : Atom) :
    colour x y = some a ↔ x ≠ y ∧ pattern x y = a := by
  by_cases h : x = y <;> simp [colour,h]

theorem colour_symm (x y : Point) : colour x y = colour y x := by
  simp only [colour,pattern,eq_comm,Bool.xor_comm]

/-- The actual source has precisely c,b,r,s, with occurring diversity pairs. -/
def source : AtomicSource Unit (fun _ => Point) where
  Atom := fun _ _ => Atom
  finiteSort := inferInstance
  finiteAtom := fun _ _ => inferInstance
  nonemptySort := fun _ => inferInstance
  conv := id
  conv_invol := fun _ => rfl
  symmetricLoop := fun _ => rfl
  colour := colour
  colour_none_iff := by
    intro i j x y
    cases i; cases j
    simpa using colour_none x y
  colour_swap := by
    intro i j x y a
    exact congrArg (· = some a) (colour_symm x y) |>.to_iff
  realized := by
    intro i j a
    let x : Point := ⟨(0,false),false,0⟩
    let y : Point := ⟨(if a.1 then 0 else 1,false),a.2,1⟩
    refine ⟨x,y,(colour_some x y a).mpr ⟨?_,?_⟩⟩
    · intro h
      have hh := congrArg Point.clone h
      change 0 = 1 at hh
      cases hh
    · rcases a with ⟨e,d⟩
      cases e <;> cases d <;> rfl

@[simp] theorem source_colour {i j : Unit} (x y : Point) :
    source.colour (i := i) (j := j) x y = colour x y := rfl

theorem atom_card : Fintype.card Atom = 4 := by decide


abbrev owner (x : Point) : Block × Bool := (x.block,x.bit)

theorem point_eq_iff (x y : Point) :
    x = y ↔ x.block = y.block ∧ x.bit = y.bit ∧ x.clone = y.clone := by
  cases x; cases y
  simp only [Point.mk.injEq]

theorem pattern_of_colour {x y x' y' : Point}
    (h : colour x y = colour x' y') : pattern x y = pattern x' y' := by
  cases hc : colour x y with
  | none =>
    have he := (colour_none x y).mp hc
    have he' := (colour_none x' y').mp (h.symm.trans hc)
    subst y; subst y'
    simp [pattern]
  | some a =>
    exact ((colour_some x y a).mp hc).2.trans
      ((colour_some x' y' a).mp (h.symm.trans hc)).2.symm

theorem block_bit_of_colour_eq {x y x' y' : Point}
    (h : colour x y = colour x' y') :
    (x.block = y.block ↔ x'.block = y'.block) ∧
      (x.bit ^^ y.bit) = (x'.bit ^^ y'.bit) := by
  have hp := pattern_of_colour h
  exact ⟨decide_eq_decide.mp (congrArg Prod.fst hp),congrArg Prod.snd hp⟩

def autGroup : Subgroup (Equiv.Perm Point) where
  carrier := {g | ∀ x y, colour (g x) (g y) = colour x y}
  one_mem' := by intro x y; rfl
  mul_mem' := by intro g h hg hh x y; exact (hg (h x) (h y)).trans (hh x y)
  inv_mem' := by
    intro g hg x y
    have h := hg (g⁻¹ x) (g⁻¹ y)
    simpa using h.symm

abbrev Aut := autGroup

@[simp] theorem aut_colour (g : Aut) (x y : Point) :
    colour (g • x) (g • y) = colour x y := g.property x y

/-- Original automorphisms may independently permute clone fibres but use
ONE common bit flip on the whole original source. -/
def motionPerm (π : Equiv.Perm Block) (d : Bool)
    (τ : (Block × Bool) → Equiv.Perm Nat) : Equiv.Perm Point where
  toFun x := ⟨π x.block,d ^^ x.bit,τ (owner x) x.clone⟩
  invFun x := ⟨π.symm x.block,d ^^ x.bit,
    (τ (π.symm x.block,d ^^ x.bit)).symm x.clone⟩
  left_inv := by
    rintro ⟨b,p,n⟩
    cases d <;> cases p <;> simp [owner]
  right_inv := by
    rintro ⟨b,p,n⟩
    cases d <;> cases p <;> simp [owner]

theorem motionPerm_pattern (π : Equiv.Perm Block) (d : Bool)
    (τ : (Block × Bool) → Equiv.Perm Nat) (x y : Point) :
    pattern (motionPerm π d τ x) (motionPerm π d τ y) = pattern x y := by
  simp only [pattern,motionPerm,Equiv.coe_fn_mk,π.injective.eq_iff]
  cases d <;> cases x.bit <;> cases y.bit <;> rfl

theorem motionPerm_colour (π : Equiv.Perm Block) (d : Bool)
    (τ : (Block × Bool) → Equiv.Perm Nat) (x y : Point) :
    colour (motionPerm π d τ x) (motionPerm π d τ y) = colour x y := by
  simp only [colour,(motionPerm π d τ).injective.eq_iff,motionPerm_pattern]

def motion (π : Equiv.Perm Block) (d : Bool)
    (τ : (Block × Bool) → Equiv.Perm Nat) : Aut :=
  ⟨motionPerm π d τ,motionPerm_colour π d τ⟩

/-- Every actual complete finite original partial isomorphism extends in
this infinite four-atom model, including tuples with repeated points. -/
theorem finite_extension {V : Type*} [Finite V] (f h : V → Point)
    (hc : ∀ v w, colour (f v) (f w) = colour (h v) (h w)) :
    ∃ g : Aut, ∀ v, g • f v = h v := by
  classical
  have coords := fun v w => block_bit_of_colour_eq (hc v w)
  obtain ⟨π,hπ⟩ := SIR.Positive.Direct.exists_perm_of_kernel
    (fun v => (f v).block) (fun v => (h v).block) (fun v w => (coords v w).1)
  by_cases hv : Nonempty V
  · let v₀ := Classical.choice hv
    let d := (h v₀).bit ^^ (f v₀).bit
    have hd (v : V) : (d ^^ (f v).bit) = (h v).bit := by
      have hh := (coords v v₀).2
      dsimp only [d]
      cases hfv : (f v).bit <;> cases hhv : (h v).bit <;>
        cases hf₀ : (f v₀).bit <;> cases hh₀ : (h v₀).bit <;> simp_all
    have hτ : ∀ a : Block × Bool, ∃ τ : Equiv.Perm Nat,
        ∀ v : {v // owner (f v) = a}, τ (f v).clone = (h v).clone := by
      intro a
      apply SIR.Positive.Direct.exists_perm_of_kernel
      intro v w
      have ho : owner (f v) = owner (f w) := v.property.trans w.property.symm
      have hb : (f v).block = (f w).block := congrArg Prod.fst ho
      have hp : (f v).bit = (f w).bit := congrArg Prod.snd ho
      have hb' : (h v).block = (h w).block := (coords v w).1.mp hb
      have hp' : (h v).bit = (h w).bit := by rw [← hd v,← hd w,hp]
      have hi : f v = f w ↔ h v = h w := by
        have he := congrArg (· = none) (hc v w) |>.to_iff
        simpa only [colour_none] using he
      constructor
      · intro hn
        exact congrArg Point.clone (hi.mp ((point_eq_iff _ _).mpr ⟨hb,hp,hn⟩))
      · intro hn
        exact congrArg Point.clone (hi.mpr ((point_eq_iff _ _).mpr ⟨hb',hp',hn⟩))
    choose τ ht using hτ
    refine ⟨motion π d τ,fun v => ?_⟩
    apply (point_eq_iff _ _).mpr
    exact ⟨hπ v,hd v,ht (owner (f v)) ⟨v,rfl⟩⟩
  · exact ⟨1,fun v => False.elim (hv ⟨v⟩)⟩

theorem homogeneous : HomogeneousSource source Aut where
  preserves_sort := by intro g p; rcases p with ⟨i,x⟩; cases i; rfl
  preserves_colours := by
    intro g p q
    rcases p with ⟨i,x⟩; rcases q with ⟨j,y⟩
    cases i; cases j
    simp only [taggedColour,Sigma.smul_mk,source_colour,aut_colour]
  extends_finite_diagram := by
    intro V _ f h hc
    have hh : ∀ v w, colour (f v).2 (f w).2 = colour (h v).2 (h w).2 := by
      intro v w
      exact congrArg (fun z : Σ _ : Unit, Σ _ : Unit, Option Atom => z.2.2) (hc v w)
    obtain ⟨g,hg⟩ := finite_extension (fun v => (f v).2) (fun v => (h v).2) hh
    exact ⟨g,fun v => Sigma.ext (Subsingleton.elim _ _) (heq_of_eq (hg v))⟩

theorem ageAP : AgeAP source := source.ageAP_of_homogeneous homogeneous

def pointEquiv : Point ≃ (Block × Bool) × Nat where
  toFun x := (owner x,x.clone)
  invFun x := ⟨x.1.1,x.1.2,x.2⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

abbrev TaggedPoint := Sigma (fun _ : Unit => Point)
def tag (x : Point) : TaggedPoint := ⟨(),x⟩
@[simp] theorem tag_val (p : TaggedPoint) : tag p.2 = p := by
  rcases p with ⟨i,p⟩; cases i; rfl

@[simp] theorem tagged_colour_eq (p q r s : TaggedPoint) :
    taggedColour source p q = taggedColour source r s ↔ colour p.2 q.2 = colour r.2 s.2 := by
  rcases p with ⟨i,p⟩; rcases q with ⟨j,q⟩
  rcases r with ⟨k,r⟩; rcases s with ⟨l,s⟩
  cases i; cases j; cases k; cases l
  simp only [taggedColour, source_colour, Sigma.mk.injEq, heq_eq_eq, true_and]
  constructor
  · exact fun h => congrArg (fun z : Σ _ : Unit, Option Atom => z.2) h
  · exact fun h => congrArg (fun c : Option Atom => (⟨(),c⟩ : Σ _ : Unit, Option Atom)) h

noncomputable def points (A : FiniteInduced (X := fun _ : Unit => Point)) : Finset Point :=
  A.finite_vertices.toFinset.image Sigma.snd

@[simp] theorem mem_points (A : FiniteInduced (X := fun _ : Unit => Point)) (x : Point) :
    x ∈ points A ↔ tag x ∈ A.vertices := by
  classical
  simp only [points, Finset.mem_image, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨p,hp,rfl⟩; simpa only [tag_val] using hp
  · intro h; exact ⟨tag x,h,rfl⟩

noncomputable def indexBound (B C : Finset Point) : ℕ := (B ∪ C).sup Point.clone + 1

theorem index_lt_bound {B C : Finset Point} {x : Point} (hx : x ∈ B ∪ C) :
    x.clone < indexBound B C := Nat.lt_succ_of_le (Finset.le_sup hx)

noncomputable def freshen (B C : Finset Point) (x : Point) : Point := by
  classical
  exact if x ∈ C then x else { x with clone := indexBound B C + x.clone }

@[simp] theorem freshen_fixed {B C : Finset Point} {x : Point} (hx : x ∈ C) :
    freshen B C x = x := by
  classical
  simp [freshen,hx]
@[simp] theorem freshen_owner (B C : Finset Point) (x : Point) :
    owner (freshen B C x) = owner x := by
  classical
  unfold freshen
  split_ifs <;> rfl
theorem freshen_clone {B C : Finset Point} {x : Point} (hx : x ∉ C) :
    (freshen B C x).clone = indexBound B C + x.clone := by
  classical
  simp [freshen,hx]

theorem freshen_injective (B C : Finset Point) : Function.Injective (freshen B C) := by
  classical
  intro x y h
  by_cases hx : x ∈ C <;> by_cases hy : y ∈ C
  · simpa only [freshen_fixed hx, freshen_fixed hy] using h
  · have hi := congrArg Point.clone h
    rw [freshen_fixed hx, freshen_clone hy] at hi
    have hl := index_lt_bound (B := B) (C := C) (Finset.mem_union_right B hx)
    omega
  · have hi := congrArg Point.clone h
    rw [freshen_clone hx, freshen_fixed hy] at hi
    have hl := index_lt_bound (B := B) (C := C) (Finset.mem_union_right B hy)
    omega
  · apply pointEquiv.injective
    have ho := congrArg owner h
    simp only [freshen_owner] at ho
    have hn := congrArg Point.clone h
    rw [freshen_clone hx, freshen_clone hy] at hn
    exact Prod.ext ho (Nat.add_left_cancel hn)

theorem pattern_of_owner {x y x' y' : Point} (hx : owner x = owner x')
    (hy : owner y = owner y') : pattern x y = pattern x' y' := by
  have hb := congrArg Prod.fst hx
  have hp := congrArg Prod.snd hx
  have hb' := congrArg Prod.fst hy
  have hp' := congrArg Prod.snd hy
  dsimp only [owner] at hb hp hb' hp'
  simp only [pattern,hb,hp,hb',hp']

theorem freshen_colour (B C : Finset Point) (x y : Point) :
    colour (freshen B C x) (freshen B C y) = colour x y := by
  unfold colour
  simp only [(freshen_injective B C).eq_iff,
    pattern_of_owner (freshen_owner B C x) (freshen_owner B C y)]

theorem freshen_mem_right {B C : Finset Point} {x : Point}
    (h : freshen B C x ∈ B) : x ∈ C := by
  classical
  by_contra hx
  have hl := index_lt_bound (B := B) (C := C) (Finset.mem_union_left C h)
  rw [freshen_clone hx] at hl
  omega

/-- Strong amalgamation in the actual infinite source, using ordinary
homogeneous alignment followed by fresh original clone indices. -/
theorem strongAmalgamation : AgeSAP source where
  strong_amalgamate := by
    classical
    intro C A B eCA eCB
    letI : Finite ↥C.vertices := C.finite_vertices.to_subtype
    letI : Finite ↥A.vertices := A.finite_vertices.to_subtype
    letI : Fintype ↥C.vertices := Fintype.ofFinite _
    have hc : ∀ c d : ↥C.vertices,
        colour (eCA.toEmbedding c).val.2 (eCA.toEmbedding d).val.2 =
          colour (eCB.toEmbedding c).val.2 (eCB.toEmbedding d).val.2 := by
      intro c d
      exact (tagged_colour_eq _ _ _ _).mp
        ((eCA.preserves_colours c d).symm.trans (eCB.preserves_colours c d))
    obtain ⟨g,hg⟩ := finite_extension
      (fun c : ↥C.vertices => (eCA.toEmbedding c).val.2)
      (fun c => (eCB.toEmbedding c).val.2) hc
    let base : Finset Point := Finset.univ.image (fun c : ↥C.vertices => (eCB.toEmbedding c).val.2)
    let move (x : Point) := freshen (points B) base (g • x)
    have hmove : Function.Injective move := (freshen_injective _ _).comp (MulAction.injective g)
    have hbase (c : ↥C.vertices) : move (eCA.toEmbedding c).val.2 =
        (eCB.toEmbedding c).val.2 := by
      dsimp only [move]
      rw [hg c, freshen_fixed (Finset.mem_image.mpr ⟨c,Finset.mem_univ c,rfl⟩)]
    let fa : ↥A.vertices → TaggedPoint := fun a => tag (move a.val.2)
    let D : FiniteInduced (X := fun _ : Unit => Point) :=
      ⟨Set.range fa ∪ B.vertices, (Set.finite_range fa).union B.finite_vertices⟩
    let eAD : InducedEmbedding source A D := {
      toEmbedding := {
        toFun := fun a => ⟨fa a,Or.inl ⟨a,rfl⟩⟩
        inj' := by
          intro a b h
          have hv := congrArg (fun p : ↥D.vertices => p.val.2) h
          apply Subtype.ext
          exact (tag_val a.val).symm.trans ((congrArg tag (hmove hv)).trans (tag_val b.val)) }
      preserves_sort := by intro a; exact Subsingleton.elim _ _
      preserves_colours := by
        intro a b
        apply (tagged_colour_eq _ _ _ _).mpr
        exact ((freshen_colour _ _ _ _).trans (aut_colour g a.val.2 b.val.2)).symm }
    let eBD : InducedEmbedding source B D := {
      toEmbedding := {
        toFun := fun b => ⟨b.val,Or.inr b.2⟩
        inj' := by
          intro a b h
          apply Subtype.ext
          exact congrArg (fun p : ↥D.vertices => p.val) h }
      preserves_sort := by intro b; rfl
      preserves_colours := by intro a b; rfl }
    refine ⟨D,eAD,eBD,?_,?_⟩
    · intro c
      apply Subtype.ext
      exact (congrArg tag (hbase c)).trans (tag_val _)
    · intro a b hab
      have he : move a.val.2 = b.val.2 := congrArg (fun p : ↥D.vertices => p.val.2) hab
      have hb : move a.val.2 ∈ points B := by
        rw [he]
        exact (mem_points B _).mpr (by simpa only [tag_val] using b.2)
      have hc' : g • a.val.2 ∈ base := freshen_mem_right hb
      rcases Finset.mem_image.mp hc' with ⟨c,_,hc'⟩
      have hm : move a.val.2 = g • a.val.2 := freshen_fixed (Finset.mem_image.mpr ⟨c,Finset.mem_univ c,hc'⟩)
      refine ⟨c,?_,?_⟩
      · apply Subtype.ext
        have hh : g • (eCA.toEmbedding c).val.2 = g • a.val.2 := (hg c).trans hc'
        exact (tag_val _).symm.trans ((congrArg tag (MulAction.injective g hh)).trans (tag_val _))
      · apply Subtype.ext
        exact (tag_val _).symm.trans ((congrArg tag (hc'.trans (hm.symm.trans he))).trans (tag_val _))


/-- Direct actual HOM-CCO construction. Finite equality components receive
fresh block numbers; global bit gains are integrated from the specified
cycle witnesses; distinct clone indices separate every formal vertex. -/
theorem semanticCCO_injective (V : Type z) (D : PartialDiagram source V)
    (hcycles : ∀ C : SimpleCycle D, CycleHom C) :
    ∃ f : DiagramHom D, f.IsInjective := by
  classical
  have hReadBlock {i j : Unit} (x y : Point) (a : source.Atom i j)
      (ha : source.colour x y = some a) :
      (Encodable.encode x.block = Encodable.encode y.block ↔ a.1 = true) := by
    have hp := congrArg Prod.fst ((colour_some x y a).mp ha).2
    change decide (x.block = y.block) = a.1 at hp
    rw [← hp]
    simp only [decide_eq_true_eq]
    exact Encodable.encode_injective.eq_iff
  have hReadBit {i j : Unit} (x y : Point) (a : source.Atom i j)
      (ha : source.colour x y = some a) : (x.bit ^^ y.bit) = a.2 :=
    congrArg Prod.snd ((colour_some x y a).mp ha).2
  obtain ⟨blocks,hblocks⟩ := CycleConsistency.coordinate_labels source D
    (fun a => a.1) (fun _ => rfl) (fun _ x => Encodable.encode x.block)
    (fun x y a ha => hReadBlock x y a ha) hcycles
  obtain ⟨bits,hbits⟩ := CycleConsistency.phase_labels source D
    (fun a => a.2) (fun _ => rfl) (fun _ x => x.bit)
    (fun x y a ha => hReadBit x y a ha) hcycles
  letI : Finite V := D.finite_type
  letI : Fintype V := Fintype.ofFinite _
  let code : V → Nat := fun x => (Fintype.equivFin V x).val
  have hCode : Function.Injective code :=
    Fin.val_injective.comp (Fintype.equivFin V).injective
  let f : DiagramHom D := {
    point := fun x => ⟨(blocks x,false),bits x,code x⟩
    preserves_edge := by
      intro x y h a ha
      apply (colour_some _ _ a).mpr
      refine ⟨?_,Prod.ext ?_ (hbits x y h a ha)⟩
      · intro he
        exact h (hCode (congrArg Point.clone he))
      · change decide ((blocks x,false) = (blocks y,false)) = a.1
        have hh := hblocks x y h a ha
        cases hab : a.1 <;> simp_all
  }
  refine ⟨f,?_⟩
  intro x y he
  exact hCode (congrArg (fun p : Sigma (fun _ : Unit => Point) => p.2.clone) he)

theorem semanticCCO : SemanticCCO.{0,0,z,0} source := by
  intro V D hcycles
  exact ⟨(semanticCCO_injective V D hcycles).choose⟩

/-- The first deliberately nonmaximal marking and the next sheet marking. -/
def label (x : Point) : Label := (x.bit ^^ x.block.2,x.bit)


/-- A block motion with exactly the seed flip required by a global old bit
flip. Each of the two infinite seed classes is permuted independently. -/
def seededBlockPerm (κ : Bool → Equiv.Perm Nat) (d : Bool) : Equiv.Perm Block where
  toFun x := (κ x.2 x.1,d ^^ x.2)
  invFun x := ((κ (d ^^ x.2)).symm x.1,d ^^ x.2)
  left_inv := by rintro ⟨n,b⟩; cases d <;> cases b <;> simp
  right_inv := by rintro ⟨n,b⟩; cases d <;> cases b <;> simp

private theorem extend_coordinates {V : Type*} [Finite V] (f h : V → Point)
    (hc : ∀ v w, colour (f v) (f w) = colour (h v) (h w))
    (π : Equiv.Perm Block) (d : Bool)
    (hπ : ∀ v, π (f v).block = (h v).block)
    (hd : ∀ v, (d ^^ (f v).bit) = (h v).bit) :
    ∃ τ : (Block × Bool) → Equiv.Perm Nat, ∀ v, motion π d τ • f v = h v := by
  classical
  have coords := fun v w => block_bit_of_colour_eq (hc v w)
  have hτ : ∀ a : Block × Bool, ∃ τ : Equiv.Perm Nat,
      ∀ v : {v // owner (f v) = a}, τ (f v).clone = (h v).clone := by
    intro a
    apply SIR.Positive.Direct.exists_perm_of_kernel
    intro v w
    have ho : owner (f v) = owner (f w) := v.property.trans w.property.symm
    have hb : (f v).block = (f w).block := congrArg Prod.fst ho
    have hp : (f v).bit = (f w).bit := congrArg Prod.snd ho
    have hb' : (h v).block = (h w).block := (coords v w).1.mp hb
    have hp' : (h v).bit = (h w).bit := by rw [← hd v,← hd w,hp]
    have hi : f v = f w ↔ h v = h w := by
      have he := congrArg (· = none) (hc v w) |>.to_iff
      simpa only [colour_none] using he
    constructor
    · intro hn
      exact congrArg Point.clone (hi.mp ((point_eq_iff _ _).mpr ⟨hb,hp,hn⟩))
    · intro hn
      exact congrArg Point.clone (hi.mpr ((point_eq_iff _ _).mpr ⟨hb',hp',hn⟩))
  choose τ ht using hτ
  refine ⟨τ,fun v => (point_eq_iff _ _).mpr ?_⟩
  exact ⟨hπ v,hd v,ht (owner (f v)) ⟨v,rfl⟩⟩

/-- Actual original automorphisms extending every finite isomorphism that
preserves lambda, and additionally mu when requested. The chosen old block
motion has the SAME global flip as the old bit; it preserves lambda on all
points, rather than only on the finite tuple. -/
theorem finite_extension_marked {V : Type*} [Finite V] (f h : V → Point)
    (hc : ∀ v w, colour (f v) (f w) = colour (h v) (h w))
    (hLambda : ∀ v, (label (f v)).1 = (label (h v)).1)
    (keepMu : Bool) (hMu : keepMu = true → ∀ v, (f v).bit = (h v).bit) :
    ∃ g : Aut, (∀ v, g • f v = h v) ∧
      (∀ x : Point, (label (g • x)).1 = (label x).1) ∧
      (keepMu = true → ∀ x : Point, (g • x).bit = x.bit) := by
  classical
  by_cases hv : Nonempty V
  · let v₀ := Classical.choice hv
    let d := (h v₀).bit ^^ (f v₀).bit
    have coords := fun v w => block_bit_of_colour_eq (hc v w)
    have hd (v : V) : (d ^^ (f v).bit) = (h v).bit := by
      have hh := (coords v v₀).2
      dsimp only [d]
      cases hfv : (f v).bit <;> cases hhv : (h v).bit <;>
        cases hf₀ : (f v₀).bit <;> cases hh₀ : (h v₀).bit <;> simp_all
    have hSeed (v : V) : (h v).block.2 = (d ^^ (f v).block.2) := by
      have shift : ∀ (d p q s t : Bool), (p ^^ s) = (q ^^ t) →
          (d ^^ p) = q → t = (d ^^ s) := by decide
      exact shift d (f v).bit (h v).bit (f v).block.2 (h v).block.2 (hLambda v) (hd v)
    have hκ : ∀ b : Bool, ∃ κ : Equiv.Perm Nat,
        ∀ v : {v // (f v).block.2 = b}, κ (f v).block.1 = (h v).block.1 := by
      intro b
      apply SIR.Positive.Direct.exists_perm_of_kernel
      intro v w
      have hs : (f v).block.2 = (f w).block.2 := v.property.trans w.property.symm
      have ht : (h v).block.2 = (h w).block.2 := by rw [hSeed v,hSeed w,hs]
      constructor
      · intro hh
        exact congrArg Prod.fst ((coords v w).1.mp (Prod.ext hh hs))
      · intro hh
        exact congrArg Prod.fst ((coords v w).1.mpr (Prod.ext hh ht))
    choose κ hκ using hκ
    let π := seededBlockPerm κ d
    have hπ (v : V) : π (f v).block = (h v).block :=
      Prod.ext (hκ (f v).block.2 ⟨v,rfl⟩) (hSeed v).symm
    obtain ⟨τ,hτ⟩ := extend_coordinates f h hc π d hπ hd
    refine ⟨motion π d τ,hτ,?_,?_⟩
    · intro x
      change ((d ^^ x.bit) ^^ (d ^^ x.block.2)) = (x.bit ^^ x.block.2)
      cases d <;> cases x.bit <;> cases x.block.2 <;> rfl
    · intro hk x
      have hh : d = false := by
        dsimp only [d]
        rw [hMu hk v₀,Bool.xor_self]
      change (d ^^ x.bit) = x.bit
      rw [hh]
      exact Bool.false_xor x.bit
  · exact ⟨1,fun v => False.elim (hv ⟨v⟩),fun _ => rfl,fun _ _ => rfl⟩

/-- The literal old-atom support formula, with no singleton label names. -/
def table (a : Atom) (p q : Label) : Prop :=
  (if a.1 then (p.1 ^^ q.1) = a.2 else True) ∧ (p.2 ^^ q.2) = a.2

private def leftWitness (p : Label) : Point :=
  ⟨(0,p.1 ^^ p.2),p.2,0⟩

private def rightWitness (a : Atom) (q : Label) : Point :=
  ⟨(if a.1 then 0 else 1,q.1 ^^ q.2),q.2,1⟩

private theorem label_left (p : Label) : label (leftWitness p) = p := by
  rcases p with ⟨l,m⟩
  cases l <;> cases m <;> rfl

private theorem label_right (a : Atom) (q : Label) : label (rightWitness a q) = q := by
  rcases q with ⟨l,m⟩
  cases l <;> cases m <;> rfl

private theorem witness_colour (a : Atom) (p q : Label) (h : table a p q) :
    colour (leftWitness p) (rightWitness a q) = some a := by
  rcases a with ⟨e,d⟩
  rcases p with ⟨l,m⟩
  rcases q with ⟨l',m'⟩
  cases e <;> cases d <;> cases l <;> cases m <;> cases l' <;> cases m' <;>
    simp_all [table,colour,pattern,leftWitness,rightWitness]

private theorem table_of_colour (x y : Point) (a : Atom)
    (h : colour x y = some a) : table a (label x) (label y) := by
  obtain ⟨_,rfl⟩ := (colour_some x y a).mp h
  by_cases hb : x.block = y.block
  · have hs : x.block.2 = y.block.2 := congrArg Prod.snd hb
    simp only [table,pattern,label,hb,decide_true,ite_true]
    cases x.bit <;> cases y.bit <;> cases y.block.2 <;> decide
  · simp [table,pattern,hb,label]

/-- Actual realizations, not a finite model approximation: all four labels
occur and these are exactly their old-atom support relations. -/
theorem table_iff_actual (a : Atom) (p q : Label) :
    table a p q ↔ ∃ x y : Point, label x = p ∧ label y = q ∧ colour x y = some a := by
  constructor
  · intro h
    exact ⟨leftWitness p,rightWitness a q,label_left p,label_right a q,
      witness_colour a p q h⟩
  · rintro ⟨x,y,rfl,rfl,h⟩
    exact table_of_colour x y a h

theorem all_four_labels_realized : Function.Surjective label := by
  intro p
  exact ⟨leftWitness p,label_left p⟩

/-- The source's proper old-atom-table retraction. -/
def retract (p : Label) : Label := (p.2,p.2)

theorem retract_preserves (a : Atom) (p q : Label) (h : table a p q) :
    table a (retract p) (retract q) := by
  rcases a with ⟨e,d⟩
  cases e <;> simpa [table,retract] using h.2

theorem retract_idempotent (p : Label) : retract (retract p) = retract p := rfl

theorem retract_not_injective : ¬ Function.Injective retract := by
  intro h
  have hh := h (show retract (false,false) = retract (true,false) from rfl)
  have hb : false = true := congrArg Prod.fst hh
  cases hb

/-- The actual first-maximal support table has only the old global bit. -/
def maximalTable (a : Atom) (p q : Bool) : Prop := (p ^^ q) = a.2

theorem maximal_endomorphism_injective (f : Bool → Bool)
    (hf : ∀ a p q, maximalTable a p q → maximalTable a (f p) (f q)) :
    Function.Injective f := by
  intro p q hpq
  by_contra hne
  have hEdge : maximalTable (true,true) p q := by
    cases p <;> cases q <;> simp_all [maximalTable]
  have hImage := hf (true,true) p q hEdge
  simp only [maximalTable,hpq,Bool.xor_self] at hImage
  cases hImage


/-- Direct unbounded realization with a prescribed lambda on all vertices
and, optionally, prescribed mu. Only actual specified atom compatibility
and the literal old cycle homomorphisms are used. -/
theorem realize_prescribed (V : Type z) (D : PartialDiagram source V)
    (hcycles : ∀ C : SimpleCycle D, CycleHom C)
    (P : V → Bool) (Q : Option (V → Bool))
    (hP : ∀ x y (h : x ≠ y) (a : source.Atom (D.vertexSort x) (D.vertexSort y)),
      D.edge x y h = some a → a.1 = true → (P x ^^ P y) = a.2)
    (hQ : ∀ q, Q = some q → ∀ x y (h : x ≠ y)
      (a : source.Atom (D.vertexSort x) (D.vertexSort y)),
      D.edge x y h = some a → (q x ^^ q y) = a.2) :
    ∃ f : DiagramHom D, f.IsInjective ∧
      (∀ x, (label (f.point x)).1 = P x) ∧
      (∀ q, Q = some q → ∀ x, (f.point x).bit = q x) := by
  classical
  have hReadBlock {i j : Unit} (x y : Point) (a : source.Atom i j)
      (ha : source.colour x y = some a) :
      (Encodable.encode x.block = Encodable.encode y.block ↔ a.1 = true) := by
    have hp := congrArg Prod.fst ((colour_some x y a).mp ha).2
    change decide (x.block = y.block) = a.1 at hp
    rw [← hp]
    simp only [decide_eq_true_eq]
    exact Encodable.encode_injective.eq_iff
  have hReadBit {i j : Unit} (x y : Point) (a : source.Atom i j)
      (ha : source.colour x y = some a) : (x.bit ^^ y.bit) = a.2 :=
    congrArg Prod.snd ((colour_some x y a).mp ha).2
  obtain ⟨blocks,hblocks⟩ := CycleConsistency.coordinate_labels source D
    (fun a => a.1) (fun _ => rfl) (fun _ x => Encodable.encode x.block)
    (fun x y a ha => hReadBlock x y a ha) hcycles
  obtain ⟨bits,hbits,hfixed⟩ : ∃ bits : V → Bool,
      (∀ x y (h : x ≠ y) (a : source.Atom (D.vertexSort x) (D.vertexSort y)),
        D.edge x y h = some a → (bits x ^^ bits y) = a.2) ∧
      (∀ q, Q = some q → bits = q) := by
    cases hQval : Q with
    | none =>
      obtain ⟨bits,hbits⟩ := CycleConsistency.phase_labels source D
        (fun a => a.2) (fun _ => rfl) (fun _ x => x.bit)
        (fun x y a ha => hReadBit x y a ha) hcycles
      refine ⟨bits,hbits,?_⟩
      intro q hq
      cases hq
    | some fixed =>
      refine ⟨fixed,hQ fixed hQval,?_⟩
      intro q hq
      exact Option.some.inj hq
  letI : Finite V := D.finite_type
  letI : Fintype V := Fintype.ofFinite _
  let code : V → Nat := fun x => (Fintype.equivFin V x).val
  have hCode : Function.Injective code :=
    Fin.val_injective.comp (Fintype.equivFin V).injective
  let f : DiagramHom D := {
    point := fun x => ⟨(blocks x,P x ^^ bits x),bits x,code x⟩
    preserves_edge := by
      intro x y h a ha
      apply (colour_some _ _ a).mpr
      refine ⟨?_,Prod.ext ?_ (hbits x y h a ha)⟩
      · intro he
        exact h (hCode (congrArg Point.clone he))
      · change decide ((blocks x,P x ^^ bits x) = (blocks y,P y ^^ bits y)) = a.1
        have hh := hblocks x y h a ha
        cases hab : a.1 with
        | false =>
          have hn : blocks x ≠ blocks y := by simpa only [hab,Bool.false_eq_true,iff_false] using hh
          simp [hn]
        | true =>
          have hb : blocks x = blocks y := hh.mpr hab
          have hs : (P x ^^ bits x) = (P y ^^ bits y) := by
            have exchange : ∀ p q b c : Bool, (p ^^ q) = (b ^^ c) →
                (p ^^ b) = (q ^^ c) := by decide
            exact exchange _ _ _ _ ((hP x y h a ha hab).trans (hbits x y h a ha).symm)
          exact decide_eq_true (Prod.ext hb hs)
  }
  refine ⟨f,?_,?_,?_⟩
  · intro x y he
    exact hCode (congrArg (fun p : Sigma (fun _ : Unit => Point) => p.2.clone) he)
  · intro x
    change (bits x ^^ (P x ^^ bits x)) = P x
    cases P x <;> cases bits x <;> rfl
  · intro q hq x
    exact congrFun (hfixed q hq) x



open ParityHasse.Original

private theorem bit_eq_of_colour_eq {x y x' y' : Point}
    (h : colour x y = colour x' y') : (x.bit = y.bit ↔ x'.bit = y'.bit) := by
  have hx := (block_bit_of_colour_eq h).2
  have zero : ∀ a b c d : Bool, (a ^^ b) = (c ^^ d) → (a = b ↔ c = d) := by decide
  exact zero _ _ _ _ hx

/-- K: same actual block and bit; clone diversity remains inside K. -/
def cloneEq : ColourEq source () := ⟨Setoid.ker owner,by
  intro x y x' y' h
  change owner x = owner y ↔ owner x' = owner y'
  simp only [owner,Prod.mk.injEq]
  exact and_congr (block_bit_of_colour_eq h).1 (bit_eq_of_colour_eq h)⟩

/-- B: same original block. -/
def blockEq : ColourEq source () := ⟨Setoid.ker Point.block,by
  intro x y x' y' h
  exact (block_bit_of_colour_eq h).1⟩

/-- S: the actual same-bit equivalence; it is the maximal parity gate. -/
def sheetEq : ColourEq source () := ⟨Setoid.ker Point.bit,by
  intro x y x' y' h
  exact bit_eq_of_colour_eq h⟩


@[simp] theorem cloneEq_apply (x y : Point) : cloneEq x y ↔ owner x = owner y := Iff.rfl
@[simp] theorem blockEq_apply (x y : Point) : blockEq x y ↔ x.block = y.block := Iff.rfl
@[simp] theorem sheetEq_apply (x y : Point) : sheetEq x y ↔ x.bit = y.bit := Iff.rfl

private def origin : Point := ⟨(0,false),false,0⟩
private def representative (a : Atom) : Point :=
  ⟨(if a.1 then 0 else 1,false),a.2,1⟩
private def accepts (E : ColourEq source ()) (a : Atom) : Prop := E origin (representative a)

private theorem representative_colour (a : Atom) : colour origin (representative a) = some a := by
  rcases a with ⟨b,d⟩
  cases b <;> cases d <;> rfl

private theorem invariant_atom_iff (E : ColourEq source ()) {x y : Point}
    (a : Atom) (ha : colour x y = some a) : E x y ↔ accepts E a :=
  E.property x y origin (representative a) (ha.trans (representative_colour a).symm)

private theorem eq_of_accepts (E F : ColourEq source ())
    (h : ∀ a, accepts E a ↔ accepts F a) : E = F := by
  apply ColourEq.ext
  intro x y
  by_cases hxy : x = y
  · subst y
    exact iff_of_true (E.val.refl x) (F.val.refl x)
  · have hc : colour x y = some (pattern x y) := by simp [colour,hxy]
    exact (invariant_atom_iff E _ hc).trans ((h _).trans (invariant_atom_iff F _ hc).symm)

private theorem accepts_forces_clone (E : ColourEq source ()) (a : Atom)
    (ha : accepts E a) : accepts E (true,false) := by
  let z : Point := ⟨(if a.1 then 0 else 1,false),a.2,2⟩
  have hx : colour origin z = some a := by
    rcases a with ⟨b,d⟩
    cases b <;> cases d <;> rfl
  have hy : colour z (representative (true,false)) = some a := by
    rcases a with ⟨b,d⟩
    cases b <;> cases d <;> rfl
  exact E.val.trans ((invariant_atom_iff E a hx).mpr ha) ((invariant_atom_iff E a hy).mpr ha)

private theorem accepts_s_forces_r (E : ColourEq source ()) (hs : accepts E (false,true)) :
    accepts E (false,false) := by
  let z : Point := ⟨(2,false),true,2⟩
  have hx : colour origin z = some (false,true) := rfl
  have hy : colour z (representative (false,false)) = some (false,true) := rfl
  exact E.val.trans ((invariant_atom_iff E _ hx).mpr hs) ((invariant_atom_iff E _ hy).mpr hs)

private theorem accepts_r_s_forces_b (E : ColourEq source ())
    (hr : accepts E (false,false)) (hs : accepts E (false,true)) : accepts E (true,true) := by
  let z : Point := ⟨(1,false),false,2⟩
  have hx : colour origin z = some (false,false) := rfl
  have hy : colour z (representative (true,true)) = some (false,true) := rfl
  exact E.val.trans ((invariant_atom_iff E _ hx).mpr hr) ((invariant_atom_iff E _ hy).mpr hs)

private theorem accepts_b_r_forces_s (E : ColourEq source ())
    (hb : accepts E (true,true)) (hr : accepts E (false,false)) : accepts E (false,true) := by
  let z : Point := ⟨(0,false),true,2⟩
  have hx : colour origin z = some (true,true) := rfl
  have hy : colour z (representative (false,true)) = some (false,false) := rfl
  exact E.val.trans ((invariant_atom_iff E _ hx).mpr hb) ((invariant_atom_iff E _ hy).mpr hr)

/-- The ENTIRE original invariant-equivalence lattice, proved from actual
old orbital witnesses and transitivity, without an exact-lattice assumption. -/
theorem full_equivalence_classification (E : ColourEq source ()) :
    E = ⊥ ∨ E = cloneEq ∨ E = blockEq ∨ E = sheetEq ∨ E = ⊤ := by
  classical
  by_cases hs : accepts E (false,true)
  · have hr := accepts_s_forces_r E hs
    have hb := accepts_r_s_forces_b E hr hs
    have hc := accepts_forces_clone E _ hs
    right; right; right; right
    apply eq_of_accepts
    rintro ⟨b,d⟩
    cases b <;> cases d <;> simp_all [accepts,representative,origin]
  · by_cases hb : accepts E (true,true)
    · have hc := accepts_forces_clone E _ hb
      have hr : ¬ accepts E (false,false) := fun hr => hs (accepts_b_r_forces_s E hb hr)
      right; right; left
      apply eq_of_accepts
      rintro ⟨b,d⟩
      cases b <;> cases d <;> simp_all [accepts,representative,origin]
    · by_cases hr : accepts E (false,false)
      · have hc := accepts_forces_clone E _ hr
        right; right; right; left
        apply eq_of_accepts
        rintro ⟨b,d⟩
        cases b <;> cases d <;> simp_all [accepts,representative,origin]
      · by_cases hc : accepts E (true,false)
        · right; left
          apply eq_of_accepts
          rintro ⟨b,d⟩
          cases b <;> cases d <;> simp_all [accepts,representative,origin,owner]
        · left
          apply eq_of_accepts
          rintro ⟨b,d⟩
          cases b <;> cases d <;> simp_all [accepts,representative,origin,ColourEq.bot_apply]

/-- The nonmaximal clone gate is strictly smaller than the same-bit gate. -/
theorem clone_lt_sheet : cloneEq < sheetEq := by
  refine lt_of_le_of_ne (fun _ _ h => congrArg Prod.snd h) ?_
  intro he
  have hs : sheetEq origin (representative (false,false)) := rfl
  rw [← he] at hs
  have hh : (0 : Nat) = 1 := congrArg (fun o : Block × Bool => o.1.1) hs
  cases hh

theorem clone_lt_block : cloneEq < blockEq := by
  refine lt_of_le_of_ne (fun _ _ h => congrArg Prod.fst h) ?_
  intro he
  have hb : blockEq origin (representative (true,true)) := rfl
  rw [← he] at hb
  have hh : false = true := congrArg (fun o : Block × Bool => o.2) hb
  cases hh

theorem sheet_inf_block : sheetEq ⊓ blockEq = cloneEq := by
  apply ColourEq.ext
  intro x y
  change ((x.bit = y.bit) ∧ x.block = y.block) ↔ owner x = owner y
  simp only [owner,Prod.mk.injEq,and_comm]

/-- Every full invariant complement to the displayed K<B interval is
literally K or S. This proves maximality of S, and nonmaximality of K. -/
theorem complement_classification (E : ColourEq source ())
    (hK : cloneEq ≤ E) (hMeet : E ⊓ blockEq = cloneEq) : E = cloneEq ∨ E = sheetEq := by
  rcases full_equivalence_classification E with he | he | he | he | he
  · have hh : cloneEq ≤ (⊥ : ColourEq source ()) := he ▸ hK
    have hc : cloneEq origin (representative (true,false)) := rfl
    have ho := hh hc
    have hn : (0 : Nat) = 1 := congrArg Point.clone ho
    cases hn
  · exact Or.inl he
  · have hh : blockEq ⊓ blockEq = cloneEq := he ▸ hMeet
    have hEq : blockEq = cloneEq := (inf_idem _).symm.trans hh
    exact False.elim (clone_lt_block.ne hEq.symm)
  · exact Or.inr he
  · have hh : (⊤ : ColourEq source ()) ⊓ blockEq = cloneEq := he ▸ hMeet
    have hEq : blockEq = cloneEq := (top_inf_eq _).symm.trans hh
    exact False.elim (clone_lt_block.ne hEq.symm)


private theorem clone_colour_iff (x y : Point) :
    colour x y = some (true,false) ↔ x ≠ y ∧ owner x = owner y := by
  cases hx : x.bit <;> cases hy : y.bit <;>
    simp [colour_some,pattern,owner,Prod.mk.injEq,hx,hy]

private theorem r_colour_iff (x y : Point) :
    colour x y = some (false,false) ↔ x.block ≠ y.block ∧ x.bit = y.bit := by
  have hn : x.block ≠ y.block → x ≠ y := fun h he => h (congrArg Point.block he)
  cases hx : x.bit <;> cases hy : y.bit <;> by_cases hb : x.block = y.block <;>
    simp [colour_some,pattern,hx,hy,hb,hn]

def squareWord (a : Atom) : RawWord source () () :=
  .atom (j := ()) a (.atom (j := ()) a (.nil ()))

/-- K is the literal RAW square c;c, including all true diagonals. -/
theorem clone_square (x y : Point) :
    RawWord.relation source (squareWord (true,false)) x y ↔ cloneEq x y := by
  change (∃ z : Point, colour x z = some (true,false) ∧
    ∃ w : Point, colour z w = some (true,false) ∧ w = y) ↔ owner x = owner y
  constructor
  · rintro ⟨z,hxz,w,hzw,rfl⟩
    exact ((clone_colour_iff x z).mp hxz).2.trans ((clone_colour_iff z w).mp hzw).2
  · intro hxy
    let n := max x.clone y.clone + 1
    let z : Point := ⟨x.block,x.bit,n⟩
    have hxz : x ≠ z := by
      intro he
      have hh := congrArg Point.clone he
      change x.clone = max x.clone y.clone + 1 at hh
      omega
    have hzy : z ≠ y := by
      intro he
      have hh := congrArg Point.clone he
      change max x.clone y.clone + 1 = y.clone at hh
      omega
    exact ⟨z,(clone_colour_iff x z).mpr ⟨hxz,rfl⟩,y,
      (clone_colour_iff z y).mpr ⟨hzy,hxy⟩,rfl⟩

/-- S is the literal RAW square r;r, also on the true diagonal. -/
theorem sheet_square (x y : Point) :
    RawWord.relation source (squareWord (false,false)) x y ↔ sheetEq x y := by
  change (∃ z : Point, colour x z = some (false,false) ∧
    ∃ w : Point, colour z w = some (false,false) ∧ w = y) ↔ x.bit = y.bit
  constructor
  · rintro ⟨z,hxz,w,hzw,rfl⟩
    exact ((r_colour_iff x z).mp hxz).2.trans ((r_colour_iff z w).mp hzw).2
  · intro hxy
    let n := max x.block.1 y.block.1 + 1
    let z : Point := ⟨(n,false),x.bit,0⟩
    have hxz : x.block ≠ z.block := by
      intro he
      have hh := congrArg Prod.fst he
      change x.block.1 = max x.block.1 y.block.1 + 1 at hh
      omega
    have hzy : z.block ≠ y.block := by
      intro he
      have hh := congrArg Prod.fst he
      change max x.block.1 y.block.1 + 1 = y.block.1 at hh
      omega
    exact ⟨z,(r_colour_iff x z).mpr ⟨hxz,rfl⟩,y,(r_colour_iff z y).mpr ⟨hzy,hxy⟩,rfl⟩

private theorem exact_of_word (E : Setoid Point) (w : RawWord source () ())
    (h : ∀ x y, RawWord.relation source w x y ↔ E x y) :
    ExactCRT.IsExactEq source (i := ()) E := by
  let D : RawExact.NonemptyExact source () () := {
    words := [w]
    nonempty := ⟨origin,origin,by
      intro word hw
      have he : word = w := by simpa only [List.mem_singleton] using hw
      rw [he]
      exact (h _ _).mpr (E.refl origin)⟩ }
  refine ⟨D,?_⟩
  funext x y
  apply propext
  constructor
  · intro hx
    exact (h x y).mp (hx w (by simp only [D,List.mem_singleton]))
  · intro hx word hw
    have he : word = w := by simpa only [D,List.mem_singleton] using hw
    rw [he]
    exact (h x y).mpr hx

theorem clone_exact : ExactCRT.IsExactEq source (i := ()) cloneEq.val :=
  exact_of_word cloneEq.val (squareWord (true,false)) clone_square

theorem sheet_exact : ExactCRT.IsExactEq source (i := ()) sheetEq.val :=
  exact_of_word sheetEq.val (squareWord (false,false)) sheet_square

def wordBit {i j : Unit} : RawWord source i j → Bool
  | .nil _ => false
  | .identity tail => wordBit tail
  | .atom a tail => a.2 ^^ wordBit tail

/-- Every actual RAW word has one fixed total bit gain. -/
theorem word_relation_bit {i j : Unit} (w : RawWord source i j) (x y : Point)
    (h : RawWord.relation source w x y) : (x.bit ^^ y.bit) = wordBit w := by
  induction w generalizing x with
  | nil i =>
    change x = y at h
    subst y
    exact Bool.xor_self _
  | identity tail ih => exact ih x h
  | @atom i j k a tail ih =>
    obtain ⟨z,hxz,hzy⟩ := h
    have ha : (x.bit ^^ z.bit) = a.2 := congrArg Prod.snd ((colour_some x z a).mp hxz).2
    change (x.bit ^^ y.bit) = (a.2 ^^ wordBit tail)
    calc
      _ = ((x.bit ^^ z.bit) ^^ (z.bit ^^ y.bit)) := by
        cases x.bit <;> cases z.bit <;> cases y.bit <;> rfl
      _ = _ := by rw [ha,ih z hzy]

/-- B cannot be exact: it contains both gains while being proper.
The empty defining family is checked separately as actual Top. -/
theorem block_not_exact : ¬ ExactCRT.IsExactEq source (i := ()) blockEq.val := by
  rintro ⟨D,hD⟩
  cases hp : D.words with
  | nil =>
    have hbad : blockEq origin (representative (false,false)) := by
      rw [← hD,hp,RawExact.evaluate_nil]
      trivial
    have hh : (0 : Nat) = 1 := congrArg Prod.fst hbad
    cases hh
  | cons word rest =>
    have h0 : RawExact.evaluate source D.words origin origin := by rw [hD]
    have h1 : RawExact.evaluate source D.words origin (representative (true,true)) := by
      rw [hD]
      rfl
    have hm : word ∈ D.words := by simpa only [hp] using (show word ∈ word :: rest from List.mem_cons_self)
    have hb0 := word_relation_bit word origin origin (h0 word hm)
    have hb1 := word_relation_bit word origin (representative (true,true)) (h1 word hm)
    change false = wordBit word at hb0
    change true = wordBit word at hb1
    exact Bool.false_ne_true (hb0.trans hb1.symm)

/-- The exact sublattice is precisely Id<K<S<Top; the extra FULL relation
B is excluded by the complete RAW-word calculation above. -/
theorem exact_equivalence_classification (E : ColourEq source ())
    (h : ExactCRT.IsExactEq source (i := ()) E.val) :
    E = ⊥ ∨ E = cloneEq ∨ E = sheetEq ∨ E = ⊤ := by
  rcases full_equivalence_classification E with he | he | he | he | he
  · exact Or.inl he
  · exact Or.inr (Or.inl he)
  · exact False.elim (block_not_exact (he ▸ h))
  · exact Or.inr (Or.inr (Or.inl he))
  · exact Or.inr (Or.inr (Or.inr he))

namespace Prefix

inductive Stage | first | both
  deriving DecidableEq

def Label : Stage → Type
  | .first => Bool
  | .both => NonmaximalBoundary.Label
instance (k : Stage) : Fintype (Label k) := by cases k <;> dsimp [Label] <;> infer_instance
instance (k : Stage) : DecidableEq (Label k) := by cases k <;> dsimp [Label] <;> infer_instance

def mark : (k : Stage) → Point → Label k
  | .first, x => (label x).1
  | .both, x => label x

abbrev β (k : Stage) (_ : Unit) := Label k
abbrev child (k : Stage) := APCharacter.Rank.Child (β k)
abbrev carrier (k : Stage) := APCharacter.Rank.Point (β k) (fun _ => mark k)

theorem inhabited (k : Stage) (c : child k) : Nonempty (carrier k c) := by
  rcases c with ⟨i,b⟩
  cases i
  cases k with
  | first => exact ⟨⟨⟨(0,b),false,0⟩,by cases b <;> rfl⟩⟩
  | both => exact ⟨⟨leftWitness b,label_left b⟩⟩

noncomputable def source (k : Stage) : AtomicSource (child k) (carrier k) :=
  APCharacter.Rank.source NonmaximalBoundary.source (β k) (fun _ => mark k) (inhabited k)

def erase (k : Stage) (x : Sigma (carrier k)) : Point := x.2.val

theorem erase_injective (k : Stage) : Function.Injective (erase k) := by
  intro x y h
  apply APCharacter.Rank.forget_injective (β k) (fun _ => mark k)
  exact Sigma.ext (Subsingleton.elim _ _) (heq_of_eq h)

def oldEquiv (k : Stage) : Sigma (carrier k) ≃ Point where
  toFun := erase k
  invFun x := ⟨⟨(),mark k x⟩,⟨x,rfl⟩⟩
  left_inv := by intro x; apply erase_injective k; rfl
  right_inv := by intro x; rfl

theorem colour_map (k : Stage) {c d : child k} (x : carrier k c) (y : carrier k d) :
    ((source k).colour x y).map Subtype.val = colour x.val y.val :=
  APCharacter.Rank.colour_map NonmaximalBoundary.source (β k) (fun _ => mark k) x y

theorem colour_some (k : Stage) {c d : child k} (x : carrier k c) (y : carrier k d)
    (a : (source k).Atom c d) :
    (source k).colour x y = some a ↔ colour x.val y.val = some a.val :=
  APCharacter.Rank.colour_some_iff NonmaximalBoundary.source (β k) (fun _ => mark k) x y a

theorem finite_extension (k : Stage) {V : Type*} [Finite V] (f h : V → Point)
    (hc : ∀ v w, colour (f v) (f w) = colour (h v) (h w))
    (hm : ∀ v, mark k (f v) = mark k (h v)) :
    ∃ g : Aut, (∀ v, g • f v = h v) ∧ ∀ x, mark k (g • x) = mark k x := by
  cases k with
  | first =>
    obtain ⟨g,hg,hl,_⟩ := finite_extension_marked f h hc hm false
      (fun h => Bool.noConfusion h)
    exact ⟨g,hg,hl⟩
  | both =>
    obtain ⟨g,hg,hl,hp⟩ := finite_extension_marked f h hc
      (fun v => congrArg Prod.fst (hm v)) true
      (fun _ v => congrArg Prod.snd (hm v))
    exact ⟨g,hg,fun x => Prod.ext (hl x) (hp rfl x)⟩

def autGroup (k : Stage) : Subgroup Aut where
  carrier := {g | ∀ x, mark k (g • x) = mark k x}
  one_mem' := by intro x; rfl
  mul_mem' := by intro g h hg hh x; exact (hg (h • x)).trans (hh x)
  inv_mem' := by
    intro g hg x
    have hh := hg (g⁻¹ • x)
    simpa using hh.symm
abbrev FullGroup (k : Stage) := autGroup k

instance (k : Stage) (c : child k) : MulAction (FullGroup k) (carrier k c) where
  smul g x := ⟨g.val • x.val, (g.property x.val).trans x.property⟩
  one_smul x := by apply Subtype.ext; exact one_smul Aut x.val
  mul_smul g h x := by apply Subtype.ext; exact mul_smul g.val h.val x.val

theorem action_colours (k : Stage) (g : FullGroup k) (p q : Sigma (carrier k)) :
    taggedColour (source k) (g • p) (g • q) = taggedColour (source k) p q := by
  rcases p with ⟨c,x⟩
  rcases q with ⟨d,y⟩
  change (⟨c,d,(source k).colour (g • x) (g • y)⟩ : Σ c, Σ d, Option ((source k).Atom c d)) =
    ⟨c,d,(source k).colour x y⟩
  apply congrArg (fun a => (⟨c,d,a⟩ : Σ c, Σ d, Option ((source k).Atom c d)))
  apply Option.map_injective Subtype.val_injective
  rw [colour_map,colour_map]
  exact aut_colour g.val x.val y.val

theorem homogeneous (k : Stage) : HomogeneousSource (source k) (FullGroup k) where
  preserves_sort := by intro g p; cases p; rfl
  preserves_colours := action_colours k
  extends_finite_diagram := by
    intro V _ f h hc
    have hs (v : V) : (f v).1 = (h v).1 :=
      congrArg (fun a : Σ c, Σ d, Option ((source k).Atom c d) => a.1) (hc v v)
    have hm (v : V) : mark k (erase k (f v)) = mark k (erase k (h v)) :=
      (f v).2.property.trans ((congrArg Sigma.snd (hs v)).trans (h v).2.property.symm)
    have hcol : ∀ v w, colour (erase k (f v)) (erase k (f w)) =
        colour (erase k (h v)) (erase k (h w)) := by
      intro v w
      have hh := hc v w
      let read : (Σ c, Σ d, Option ((source k).Atom c d)) → Option Atom :=
        fun a => a.2.2.map Subtype.val
      have he := congrArg read hh
      exact (colour_map k (f v).2 (f w).2).symm.trans
        (he.trans (colour_map k (h v).2 (h w).2))
    obtain ⟨g,hg,hmark⟩ := finite_extension k (fun v => erase k (f v)) (fun v => erase k (h v)) hcol hm
    refine ⟨⟨g,hmark⟩,fun v => ?_⟩
    apply erase_injective k
    exact hg v

def pLabel (k : Stage) (c : child k) : Bool :=
  match k with
  | .first => c.2
  | .both => c.2.1
def qLabel (c : child .both) : Bool := c.2.2

theorem point_p (k : Stage) {c : child k} (x : carrier k c) : (label x.val).1 = pLabel k c := by
  cases k with
  | first => exact x.property
  | both => exact congrArg Prod.fst x.property
theorem point_q {c : child .both} (x : carrier .both c) : x.val.bit = qLabel c :=
  congrArg Prod.snd x.property

def oldDiagram (k : Stage) {V : Type z} (D : PartialDiagram (source k) V) :
    PartialDiagram NonmaximalBoundary.source V where
  finite_type := D.finite_type
  vertexSort _ := ()
  edge x y h := (D.edge x y h).map Subtype.val
  edge_reverse := by
    intro x y h a
    constructor
    · intro ha
      obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp ha
      rw [(D.edge_reverse x y h b).mp hb]
      rfl
    · intro ha
      obtain ⟨b,hb,he⟩ := Option.map_eq_some_iff.mp ha
      rw [(D.edge_reverse y x h.symm b).mp hb]
      change some b.val = some a
      exact congrArg some he

def newCycle (k : Stage) {V : Type z} (D : PartialDiagram (source k) V)
    (C : SimpleCycle (oldDiagram k D)) : SimpleCycle D where
  length := C.length
  length_ge_three := C.length_ge_three
  length_pos := C.length_pos
  vertices := C.vertices
  next_ne := C.next_ne
  specified := by
    intro p
    obtain ⟨a,ha⟩ := C.specified p
    obtain ⟨b,hb,_⟩ := Option.map_eq_some_iff.mp ha
    exact ⟨b,hb⟩

theorem old_cycle_hom (k : Stage) {V : Type z} (D : PartialDiagram (source k) V)
    (cycles : ∀ C : SimpleCycle D, CycleHom C) (C : SimpleCycle (oldDiagram k D)) :
    CycleHom C := by
  obtain ⟨p,hp⟩ := cycles (newCycle k D C)
  refine ⟨fun i => (p i).val,?_⟩
  intro i a ha
  obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp ha
  have hh := congrArg (Option.map Subtype.val) (hp i b hb)
  exact (colour_map k (p i) (p (cyclicNext C.length_pos i))).symm.trans hh

theorem atom_p (k : Stage) {c d : child k} (a : (source k).Atom c d)
    (ha : a.val.1 = true) : (pLabel k c ^^ pLabel k d) = a.val.2 := by
  obtain ⟨x,y,hxy⟩ := a.property
  have hh := (table_of_colour x.val y.val a.val hxy).1
  change (if a.val.1 then ((label x.val).1 ^^ (label y.val).1) = a.val.2 else True) at hh
  simpa only [ha,ite_true,point_p] using hh

theorem atom_q {c d : child .both} (a : (source .both).Atom c d) :
    (qLabel c ^^ qLabel d) = a.val.2 := by
  obtain ⟨x,y,hxy⟩ := a.property
  have hh := congrArg Prod.snd ((NonmaximalBoundary.colour_some x.val y.val a.val).mp hxy).2
  change (x.val.bit ^^ y.val.bit) = a.val.2 at hh
  simpa only [point_q] using hh

def qPrescription (k : Stage) {V : Type z} (D : PartialDiagram (source k) V) :
    Option (V → Bool) := match k with
  | .first => none
  | .both => some (fun x => qLabel (D.vertexSort x))

/-- Both deliberately chosen prefixes have actual HOM-CCO, proved directly
from cycle compatibility, with all named lambda/mu predicates retained. -/
theorem semanticCCO (k : Stage) : SemanticCCO.{0,0,z,0} (source k) := by
  intro V D cycles
  let P : V → Bool := fun x => pLabel k (D.vertexSort x)
  have hP : ∀ x y (h : x ≠ y)
      (a : NonmaximalBoundary.source.Atom ((oldDiagram k D).vertexSort x) ((oldDiagram k D).vertexSort y)),
      (oldDiagram k D).edge x y h = some a → a.1 = true → (P x ^^ P y) = a.2 := by
    intro x y h a ha hb
    obtain ⟨c,hc,rfl⟩ := Option.map_eq_some_iff.mp ha
    exact atom_p k c hb
  have hQ : ∀ q, qPrescription k D = some q → ∀ x y (h : x ≠ y)
      (a : NonmaximalBoundary.source.Atom ((oldDiagram k D).vertexSort x) ((oldDiagram k D).vertexSort y)),
      (oldDiagram k D).edge x y h = some a → (q x ^^ q y) = a.2 := by
    cases k with
    | first => intro q hq; cases hq
    | both =>
      intro q hq x y h a ha
      have he : (fun x => qLabel (D.vertexSort x)) = q := Option.some.inj hq
      subst q
      obtain ⟨c,hc,rfl⟩ := Option.map_eq_some_iff.mp ha
      exact atom_q c
  obtain ⟨f,hfi,hfp,hfq⟩ := realize_prescribed V (oldDiagram k D)
    (old_cycle_hom k D cycles) P (qPrescription k D) hP hQ
  have hm (x : V) : mark k (f.point x) = (D.vertexSort x).2 := by
    cases k with
    | first => exact hfp x
    | both => exact Prod.ext (hfp x) (hfq (fun x => qLabel (D.vertexSort x)) rfl x)
  refine ⟨{
    point := fun x => ⟨f.point x,hm x⟩
    preserves_edge := ?_
  }⟩
  intro x y h a ha
  apply (colour_some k _ _ a).mpr
  apply f.preserves_edge x y h a.val
  change (D.edge x y h).map Subtype.val = some a.val
  rw [ha]
  rfl

noncomputable section

def freshen (k : Stage) (B C : Finset (Sigma (carrier k))) (x : Sigma (carrier k)) :
    Sigma (carrier k) := by
  classical
  let y := NonmaximalBoundary.freshen (B.image (erase k)) (C.image (erase k)) (erase k x)
  have hm : mark k y = mark k (erase k x) := by
    have ho := NonmaximalBoundary.freshen_owner (B.image (erase k)) (C.image (erase k)) (erase k x)
    have hl : label y = label (erase k x) := by
      apply Prod.ext
      · exact congrArg (fun o : Block × Bool => o.2 ^^ o.1.2) ho
      · exact congrArg (fun o : Block × Bool => o.2) ho
    cases k with
    | first => exact congrArg Prod.fst hl
    | both => exact hl
  exact ⟨x.1,⟨y,hm.trans x.2.property⟩⟩

@[simp] theorem freshen_sort (k : Stage) (B C : Finset (Sigma (carrier k)))
    (x : Sigma (carrier k)) : (freshen k B C x).1 = x.1 := rfl

@[simp] theorem erase_freshen (k : Stage) (B C : Finset (Sigma (carrier k)))
    (x : Sigma (carrier k)) :
    erase k (freshen k B C x) = NonmaximalBoundary.freshen (B.image (erase k)) (C.image (erase k)) (erase k x) := rfl

theorem freshen_injective (k : Stage) (B C : Finset (Sigma (carrier k))) :
    Function.Injective (freshen k B C) := by
  intro x y h
  apply erase_injective k
  exact NonmaximalBoundary.freshen_injective _ _ (congrArg (erase k) h)

theorem freshen_fixed (k : Stage) {B C : Finset (Sigma (carrier k))}
    {x : Sigma (carrier k)} (hx : x ∈ C) : freshen k B C x = x := by
  classical
  apply erase_injective k
  exact NonmaximalBoundary.freshen_fixed (Finset.mem_image.mpr ⟨x,hx,rfl⟩)

theorem freshen_mem_right (k : Stage) {B C : Finset (Sigma (carrier k))}
    {x : Sigma (carrier k)} (hx : freshen k B C x ∈ B) : x ∈ C := by
  classical
  have hh : NonmaximalBoundary.freshen (B.image (erase k)) (C.image (erase k)) (erase k x) ∈
      B.image (erase k) := Finset.mem_image.mpr ⟨freshen k B C x,hx,rfl⟩
  obtain ⟨c,hc,he⟩ := Finset.mem_image.mp (NonmaximalBoundary.freshen_mem_right hh)
  exact erase_injective k he ▸ hc

theorem freshen_colours (k : Stage) (B C : Finset (Sigma (carrier k)))
    (x y : Sigma (carrier k)) :
    taggedColour (source k) (freshen k B C x) (freshen k B C y) =
      taggedColour (source k) x y := by
  rcases x with ⟨c,x⟩
  rcases y with ⟨d,y⟩
  apply congrArg (fun a => (⟨c,d,a⟩ : Σ c, Σ d, Option ((source k).Atom c d)))
  apply Option.map_injective Subtype.val_injective
  exact (colour_map k _ _).trans
    ((NonmaximalBoundary.freshen_colour _ _ _ _).trans (colour_map k x y).symm)

/-- Both concrete unary prefixes have genuine SAP. All named predicates
are retained while the original infinite clone index separates the legs. -/
theorem strongAmalgamation (k : Stage) : AgeSAP (source k) where
  strong_amalgamate := by
    classical
    intro C A B eCA eCB
    letI : Finite ↥C.vertices := C.finite_vertices.to_subtype
    letI : Finite ↥A.vertices := A.finite_vertices.to_subtype
    letI : Fintype ↥C.vertices := Fintype.ofFinite _
    obtain ⟨g,hg⟩ := (homogeneous k).extends_finite_diagram
      (fun c : ↥C.vertices => (eCA.toEmbedding c).val)
      (fun c => (eCB.toEmbedding c).val)
      (fun c d => (eCA.preserves_colours c d).symm.trans (eCB.preserves_colours c d))
    let base : Finset (Sigma (carrier k)) :=
      Finset.univ.image (fun c : ↥C.vertices => (eCB.toEmbedding c).val)
    let move (x : Sigma (carrier k)) := freshen k B.finite_vertices.toFinset base (g • x)
    have hmove : Function.Injective move := (freshen_injective k _ _).comp (MulAction.injective g)
    have hbase (c : ↥C.vertices) : move (eCA.toEmbedding c).val = (eCB.toEmbedding c).val := by
      dsimp only [move]
      rw [hg c, freshen_fixed k (Finset.mem_image.mpr ⟨c,Finset.mem_univ c,rfl⟩)]
    let fa : ↥A.vertices → Sigma (carrier k) := fun a => move a.val
    let D : FiniteInduced (X := carrier k) :=
      ⟨Set.range fa ∪ B.vertices, (Set.finite_range fa).union B.finite_vertices⟩
    let eAD : InducedEmbedding (source k) A D := {
      toEmbedding := {
        toFun := fun a => ⟨fa a,Or.inl ⟨a,rfl⟩⟩
        inj' := by
          intro a b h
          exact Subtype.ext (hmove (congrArg (fun p : ↥D.vertices => p.val) h)) }
      preserves_sort := fun a => (homogeneous k).preserves_sort g a.val
      preserves_colours := by
        intro a b
        exact ((freshen_colours k _ _ _ _).trans
          ((homogeneous k).preserves_colours g a.val b.val)).symm }
    let eBD : InducedEmbedding (source k) B D := {
      toEmbedding := {
        toFun := fun b => ⟨b.val,Or.inr b.2⟩
        inj' := fun a b h => Subtype.ext (congrArg (fun p : ↥D.vertices => p.val) h) }
      preserves_sort := fun _ => rfl
      preserves_colours := fun _ _ => rfl }
    refine ⟨D,eAD,eBD,?_,?_⟩
    · intro c
      exact Subtype.ext (hbase c)
    · intro a b hab
      have he : move a.val = b.val := congrArg (fun p : ↥D.vertices => p.val) hab
      have hb : move a.val ∈ B.finite_vertices.toFinset :=
        B.finite_vertices.mem_toFinset.mpr (he.symm ▸ b.property)
      have hc : g • a.val ∈ base := freshen_mem_right k hb
      obtain ⟨c,_,hc⟩ := Finset.mem_image.mp hc
      have hm : move a.val = g • a.val :=
        freshen_fixed k (Finset.mem_image.mpr ⟨c,Finset.mem_univ c,hc⟩)
      refine ⟨c,?_,?_⟩
      · exact Subtype.ext (MulAction.injective g ((hg c).trans hc))
      · exact Subtype.ext (hc.trans (hm.symm.trans he))


/-- The full two-orbital equivalence-of-infinite-cliques colour structure. -/
def partitionColour (x y : Nat × Nat) : Option Bool :=
  if x = y then none else some (decide (x.1 = y.1))

/-- ALL invariant equivalences of this actual infinite partition model are
identity, same row, or Top. No exactness or terminal-core theorem is used. -/
theorem partition_classification (E : Setoid (Nat × Nat))
    (hInv : ∀ x y x' y', partitionColour x y = partitionColour x' y' →
      (E x y ↔ E x' y')) :
    (∀ x y, E x y ↔ x = y) ∨
      (∀ x y, E x y ↔ x.1 = y.1) ∨ (∀ x y, E x y) := by
  classical
  let o : Nat × Nat := (0,0)
  let c : Nat × Nat := (0,1)
  let r : Nat × Nat := (1,0)
  have hOutside (h : E o r) : ∀ x y, x.1 ≠ y.1 → E x y := by
    intro x y hne
    have hp : x ≠ y := fun he => hne (congrArg Prod.fst he)
    apply (hInv o r x y ?_).mp h
    simp [partitionColour,o,r,hp,hne]
  by_cases hr : E o r
  · right; right
    intro x y
    let z : Nat × Nat := (max x.1 y.1 + 1,0)
    have hxz : x.1 ≠ z.1 := by dsimp [z]; omega
    have hzy : z.1 ≠ y.1 := by dsimp [z]; omega
    exact E.trans (hOutside hr x z hxz) (hOutside hr z y hzy)
  · have noOutside : ∀ x y, E x y → x.1 = y.1 := by
      intro x y hxy
      by_contra hn
      have hp : x ≠ y := fun he => hn (congrArg Prod.fst he)
      apply hr
      apply (hInv x y o r ?_).mp hxy
      simp [partitionColour,o,r,hp,hn]
    by_cases hc : E o c
    · right; left
      intro x y
      refine ⟨noOutside x y,?_⟩
      intro hrow
      by_cases hxy : x = y
      · exact hxy ▸ E.refl x
      · apply (hInv o c x y ?_).mp hc
        simp [partitionColour,o,c,hxy,hrow]
    · left
      intro x y
      constructor
      · intro hxy
        by_contra hn
        have hrow := noOutside x y hxy
        apply hc
        apply (hInv x y o c ?_).mp hxy
        simp [partitionColour,o,c,hn,hrow]
      · intro hxy
        exact hxy ▸ E.refl x

private def fixedPoint (p : NonmaximalBoundary.Label) (q : Nat × Nat) : Point :=
  ⟨(q.1,p.1 ^^ p.2),p.2,q.2⟩

private theorem fixedPoint_label (p : NonmaximalBoundary.Label) (q : Nat × Nat) :
    label (fixedPoint p q) = p := by
  rcases p with ⟨l,m⟩
  cases l <;> cases m <;> rfl

/-- Every literal terminal label has infinitely many blocks, each with
infinitely many clones. This equivalence retains the actual source points. -/
def fixedEquiv (p : NonmaximalBoundary.Label) :
    carrier .both ⟨(),p⟩ ≃ Nat × Nat where
  toFun x := (x.val.block.1,x.val.clone)
  invFun q := ⟨fixedPoint p q,fixedPoint_label p q⟩
  left_inv := by
    intro x
    apply Subtype.ext
    apply (point_eq_iff _ _).mpr
    have hbit : x.val.bit = p.2 := congrArg Prod.snd x.property
    have hseed : x.val.block.2 = (p.1 ^^ p.2) := by
      have recover : ∀ (b s l m : Bool), (b ^^ s,b) = (l,m) → s = (l ^^ m) := by decide
      exact recover x.val.bit x.val.block.2 p.1 p.2 x.property
    exact ⟨Prod.ext rfl hseed.symm,hbit.symm,rfl⟩
  right_inv := by intro q; rfl

private theorem fixedPoint_colour (p : NonmaximalBoundary.Label) (x y : Nat × Nat) :
    colour (fixedPoint p x) (fixedPoint p y) =
      (partitionColour x y).map (fun b => (b,false)) := by
  rcases x with ⟨n,k⟩
  rcases y with ⟨m,l⟩
  by_cases hn : n = m <;> by_cases hk : k = l <;>
    simp [colour,pattern,fixedPoint,partitionColour,Point.mk.injEq,Prod.mk.injEq,hn,hk]

/-- Full invariant equivalences on every actual final sort, including all
orbital unions rather than merely exact presentations. -/
theorem final_equivalence_trichotomy (p : NonmaximalBoundary.Label)
    (E : ParityHasse.Original.ColourEq (source .both) ⟨(),p⟩) :
    (∀ x y, E x y ↔ x = y) ∨
      (∀ x y, E x y ↔ (fixedEquiv p x).1 = (fixedEquiv p y).1) ∨
      (∀ x y, E x y) := by
  let R : Setoid (Nat × Nat) := {
    r x y := E ((fixedEquiv p).symm x) ((fixedEquiv p).symm y)
    iseqv := ⟨fun x => E.val.refl _,fun h => E.val.symm h,fun h k => E.val.trans h k⟩ }
  have hInv : ∀ x y x' y', partitionColour x y = partitionColour x' y' →
      (R x y ↔ R x' y') := by
    intro x y x' y' h
    apply E.property
    apply Option.map_injective Subtype.val_injective
    rw [colour_map,colour_map]
    change colour (fixedPoint p x) (fixedPoint p y) = colour (fixedPoint p x') (fixedPoint p y')
    rw [fixedPoint_colour,fixedPoint_colour,h]
  rcases partition_classification R hInv with he | he | he
  · left
    intro x y
    have hh := he (fixedEquiv p x) (fixedEquiv p y)
    change E ((fixedEquiv p).symm (fixedEquiv p x))
      ((fixedEquiv p).symm (fixedEquiv p y)) ↔ fixedEquiv p x = fixedEquiv p y at hh
    simpa only [Equiv.symm_apply_apply,(fixedEquiv p).injective.eq_iff] using hh
  · right; left
    intro x y
    have hh := he (fixedEquiv p x) (fixedEquiv p y)
    change E ((fixedEquiv p).symm (fixedEquiv p x))
      ((fixedEquiv p).symm (fixedEquiv p y)) ↔ (fixedEquiv p x).1 = (fixedEquiv p y).1 at hh
    simpa only [Equiv.symm_apply_apply] using hh
  · right; right
    intro x y
    have hh := he (fixedEquiv p x) (fixedEquiv p y)
    change E ((fixedEquiv p).symm (fixedEquiv p x))
      ((fixedEquiv p).symm (fixedEquiv p y)) at hh
    simpa only [Equiv.symm_apply_apply] using hh

/-- Every strict FULL invariant interval of every actual final sort has
infinite index. The proof includes equality-to-Top intervals explicitly. -/
theorem final_strict_index_infinite (p : NonmaximalBoundary.Label)
    (E F : ParityHasse.Original.ColourEq (source .both) ⟨(),p⟩)
    (hEF : E < F) (x : carrier .both ⟨(),p⟩) :
    Infinite (ParityHasse.Original.RelativeClass E.val F.val x) := by
  classical
  have fromSequence (f : Nat → carrier .both ⟨(),p⟩)
      (hf : ∀ n, F x (f n))
      (hsep : ∀ m n, E (f m) (f n) → m = n) :
      Infinite (ParityHasse.Original.RelativeClass E.val F.val x) := by
    let code : Nat → ParityHasse.Original.RelativeClass E.val F.val x :=
      fun n => Quotient.mk _ ⟨f n,hf n⟩
    apply Infinite.of_injective code
    intro m n h
    have hh : (Setoid.comap (fun y : {y // F x y} => y.val) E.val)
        ⟨f m,hf m⟩ ⟨f n,hf n⟩ := Quotient.exact h
    exact hsep m n hh
  let clones (n : Nat) := (fixedEquiv p).symm ((fixedEquiv p x).1,n)
  let blocks (n : Nat) := (fixedEquiv p).symm (n,0)
  rcases final_equivalence_trichotomy p E with he | he | he
  · have hCloneSep : ∀ m n, E (clones m) (clones n) → m = n := by
      intro m n hh
      have hh' := congrArg (fun y => (fixedEquiv p y).2) ((he _ _).mp hh)
      simpa only [clones,Equiv.apply_symm_apply] using hh'
    rcases final_equivalence_trichotomy p F with hf | hf | hf
    · exact False.elim (hEF.not_ge (fun a b hab => (he a b).mpr ((hf a b).mp hab)))
    · exact fromSequence clones (fun n => (hf _ _).mpr (by simp only [clones,Equiv.apply_symm_apply])) hCloneSep
    · exact fromSequence clones (fun n => hf x (clones n)) hCloneSep
  · rcases final_equivalence_trichotomy p F with hf | hf | hf
    · apply False.elim
      apply hEF.not_ge
      intro a b hab
      exact (he a b).mpr (congrArg (fun y => (fixedEquiv p y).1) ((hf a b).mp hab))
    · exact False.elim (hEF.not_ge (fun a b hab => (he a b).mpr ((hf a b).mp hab)))
    · apply fromSequence blocks (fun n => hf x (blocks n))
      intro m n hh
      simpa only [blocks,Equiv.apply_symm_apply] using (he _ _).mp hh
  · exact False.elim (hEF.not_ge (fun a b _ => he a b))

/-- The final actual marked source satisfies literal FULL-cover terminality.
This was proved without a maximal-gate hypothesis or automatic-core input. -/
theorem terminal (c : child .both)
    (E F : ParityHasse.Original.ColourEq (source .both) c) (h : E ⋖ F)
    (x : carrier .both c) :
    Infinite (ParityHasse.Original.RelativeClass E.val F.val x) := by
  rcases c with ⟨i,p⟩
  cases i
  exact final_strict_index_infinite p E F h.lt x

end
end Prefix

end CCO.AutomaticEPCore.NonmaximalBoundary
