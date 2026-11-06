import CCO.CloneTupleGeometry.FullKernelMI
import CCO.RealClosure.Bounds.Packet
import Mathlib.Data.Fintype.Prod

/-! C76: an actual countably infinite homogeneous union of four-point
V4 packets. Its greatest finite-class FULL equivalence is proper MI, but
the UNSPLIT pure-clone kernel is the meet of two strictly larger FULL
equivalences. This model establishes the stated boundary before the safe
terminal construction. No SAP or semantic CCO claim is made for this model. -/

set_option maxHeartbeats 900000
namespace CCO.CloneTupleGeometry.InfinitePacketBoundary
open ParityHasse.Original TerminalPowers RealHull.Geometry
noncomputable section

abbrev Point := ℕ × Bool × Bool
abbrev packet (x : Point) := x.1
abbrev first (x : Point) := x.2.1
abbrev second (x : Point) := x.2.2

inductive Colour | firstDiff | secondDiff | bothDiff | apart
  deriving DecidableEq

instance : Fintype Colour where
  elems := {.firstDiff,.secondDiff,.bothDiff,.apart}
  complete c := by cases c <;> simp

def colour (x y : Point) : Option Colour :=
  if packet x = packet y then
    if first x = first y then
      if second x = second y then none else some .secondDiff
    else if second x = second y then some .firstDiff else some .bothDiff
  else some .apart

theorem colour_none (x y : Point) : colour x y = none ↔ x = y := by
  rcases x with ⟨n,a,b⟩
  rcases y with ⟨m,c,d⟩
  simp only [colour,packet,first,second,Prod.mk.injEq]
  split_ifs <;> simp_all

theorem colour_symm (x y : Point) : colour x y = colour y x := by
  simp only [colour,eq_comm]

def packetRead : Option Colour → Bool
  | some .apart => false
  | _ => true

def firstRead : Option Colour → Bool
  | none | some .secondDiff => true
  | _ => false

def secondRead : Option Colour → Bool
  | none | some .firstDiff => true
  | _ => false

theorem packet_read (x y : Point) :
    packet x = packet y ↔ packetRead (colour x y) = true := by
  unfold colour
  split_ifs <;> simp_all [packetRead]

theorem first_read (x y : Point) :
    (packet x = packet y ∧ first x = first y) ↔ firstRead (colour x y) = true := by
  unfold colour
  split_ifs <;> simp_all [firstRead]

theorem second_read (x y : Point) :
    (packet x = packet y ∧ second x = second y) ↔ secondRead (colour x y) = true := by
  unfold colour
  split_ifs <;> simp_all [secondRead]

theorem kernels_of_colour_eq {x y x' y' : Point} (h : colour x y = colour x' y') :
    (packet x = packet y ↔ packet x' = packet y') ∧
    ((packet x = packet y ∧ first x = first y) ↔
      (packet x' = packet y' ∧ first x' = first y')) ∧
    ((packet x = packet y ∧ second x = second y) ↔
      (packet x' = packet y' ∧ second x' = second y')) := by
  constructor
  · rw [packet_read,packet_read,h]
  constructor
  · rw [first_read,first_read,h]
  · rw [second_read,second_read,h]

private theorem xor_eq_of_pattern (a b c d : Bool) (h : a = b ↔ c = d) :
    (a ^^ b) = (c ^^ d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

theorem bits_of_colour_eq {x y x' y' : Point}
    (h : colour x y = colour x' y') (hp : packet x = packet y) :
    (first x ^^ first y) = (first x' ^^ first y') ∧
      (second x ^^ second y) = (second x' ^^ second y') := by
  have hp' := (kernels_of_colour_eq h).1.mp hp
  have h1 : first x = first y ↔ first x' = first y' := by
    simpa only [hp,hp',true_and] using (kernels_of_colour_eq h).2.1
  have h2 : second x = second y ↔ second x' = second y' := by
    simpa only [hp,hp',true_and] using (kernels_of_colour_eq h).2.2
  exact ⟨xor_eq_of_pattern _ _ _ _ h1,xor_eq_of_pattern _ _ _ _ h2⟩

def source : AtomicSource Unit (fun _ => Point) where
  Atom _ _ := Colour
  finiteSort := inferInstance
  finiteAtom _ _ := inferInstance
  nonemptySort _ := ⟨0,false,false⟩
  conv := id
  conv_invol _ := rfl
  symmetricLoop _ := rfl
  colour := colour
  colour_none_iff := by
    intro i j x y
    cases i
    cases j
    simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using colour_none x y
  colour_swap := by
    intro i j x y a
    exact (congrArg (fun z => z = some a) (colour_symm x y)).to_iff
  realized := by
    intro i j a
    cases a with
    | firstDiff => exact ⟨(0,false,false),(0,true,false),rfl⟩
    | secondDiff => exact ⟨(0,false,false),(0,false,true),rfl⟩
    | bothDiff => exact ⟨(0,false,false),(0,true,true),rfl⟩
    | apart => exact ⟨(0,false,false),(1,false,false),rfl⟩

@[simp] theorem source_colour {i j : Unit} (x y : Point) :
    source.colour (i := i) (j := j) x y = colour x y := rfl

/-- On the one named sort, use the literal full automorphism action at
its unique tag. This also matches the one-sort finite-packet API. -/
instance pointAction : MulAction (FullAut source) Point := fullAutAction source ()

@[instance_reducible] def sourceAction : MulAction (FullAut source) (Sigma (fun _ : Unit => Point)) :=
  @Sigma.instMulAction Unit (FullAut source) (fun _ => Point) inferInstance (fun _ => pointAction)

instance points_countable : Countable Point := inferInstance
instance points_infinite : Infinite Point :=
  Infinite.of_injective (fun n : ℕ => ((n,false,false) : Point))
    (fun _ _ h => congrArg Prod.fst h)

/-- Independent V4 translations inside each packet and arbitrary packet
permutations are actual complete-colour-preserving permutations. -/
def motionPerm (σ : Equiv.Perm ℕ) (δ₁ δ₂ : ℕ → Bool) : Equiv.Perm Point where
  toFun x := (σ (packet x),δ₁ (packet x) ^^ first x,δ₂ (packet x) ^^ second x)
  invFun x := (σ.symm (packet x),δ₁ (σ.symm (packet x)) ^^ first x,
    δ₂ (σ.symm (packet x)) ^^ second x)
  left_inv := by rintro ⟨n,a,b⟩; simp [packet,first,second]
  right_inv := by rintro ⟨n,a,b⟩; simp [packet,first,second]

theorem motionPerm_colour (σ : Equiv.Perm ℕ) (δ₁ δ₂ : ℕ → Bool) (x y : Point) :
    colour (motionPerm σ δ₁ δ₂ x) (motionPerm σ δ₁ δ₂ y) = colour x y := by
  change (if σ (packet x) = σ (packet y) then
    if (δ₁ (packet x) ^^ first x) = (δ₁ (packet y) ^^ first y) then
      if (δ₂ (packet x) ^^ second x) = (δ₂ (packet y) ^^ second y) then none else some Colour.secondDiff
    else if (δ₂ (packet x) ^^ second x) = (δ₂ (packet y) ^^ second y) then some Colour.firstDiff
      else some Colour.bothDiff
    else some Colour.apart) = _
  simp only [σ.injective.eq_iff]
  by_cases hp : packet x = packet y
  · simp [hp,colour]
  · simp [hp,colour]

def motion (σ : Equiv.Perm ℕ) (δ₁ δ₂ : ℕ → Bool) : FullAut source :=
  ⟨fun _ => motionPerm σ δ₁ δ₂,fun _ _ x y => motionPerm_colour σ δ₁ δ₂ x y⟩

/-- One packet anchor chooses each of its TWO translations. Full pair
colours ensure that the same translation works for every old point of
that packet in the finite diagram. -/
theorem finite_extension {V : Type*} [Finite V] (f h : V → Point)
    (hc : ∀ a b, colour (f a) (f b) = colour (h a) (h b)) :
    ∃ g : FullAut source, ∀ a, g.val () (f a) = h a := by
  classical
  obtain ⟨σ,hσ⟩ := CloneSAP.exists_permutation_of_eq_pattern
    (fun a => packet (f a)) (fun a => packet (h a))
    (fun a b => (kernels_of_colour_eq (hc a b)).1)
  let occupied (n : ℕ) := ∃ a, packet (f a) = n
  let anchor (n : ℕ) (hn : occupied n) := Classical.choose hn
  let δ₁ (n : ℕ) : Bool := if hn : occupied n then
    first (h (anchor n hn)) ^^ first (f (anchor n hn)) else false
  let δ₂ (n : ℕ) : Bool := if hn : occupied n then
    second (h (anchor n hn)) ^^ second (f (anchor n hn)) else false
  refine ⟨motion σ δ₁ δ₂,?_⟩
  intro a
  apply Prod.ext (hσ a)
  apply Prod.ext
  · change (δ₁ (packet (f a)) ^^ first (f a)) = first (h a)
    have ha : occupied (packet (f a)) := ⟨a,rfl⟩
    let b := anchor (packet (f a)) ha
    have hb : packet (f b) = packet (f a) := Classical.choose_spec ha
    have hd := (bits_of_colour_eq (hc a b) hb.symm).1
    simp only [δ₁,dite_eq_left ha]
    change ((first (h b) ^^ first (f b)) ^^ first (f a)) = first (h a)
    cases hfa : first (f a) <;> cases hfb : first (f b) <;>
      cases hha : first (h a) <;> cases hhb : first (h b) <;> simp_all
  · change (δ₂ (packet (f a)) ^^ second (f a)) = second (h a)
    have ha : occupied (packet (f a)) := ⟨a,rfl⟩
    let b := anchor (packet (f a)) ha
    have hb : packet (f b) = packet (f a) := Classical.choose_spec ha
    have hd := (bits_of_colour_eq (hc a b) hb.symm).2
    simp only [δ₂,dite_eq_left ha]
    change ((second (h b) ^^ second (f b)) ^^ second (f a)) = second (h a)
    cases hfa : second (f a) <;> cases hfb : second (f b) <;>
      cases hha : second (h a) <;> cases hhb : second (h b) <;> simp_all

theorem homogeneous : @HomogeneousSource Unit (fun _ => Point) source
    (FullAut source) inferInstance sourceAction where
  preserves_sort := by intro g p; rfl
  preserves_colours := by
    rintro g ⟨i,x⟩ ⟨j,y⟩
    exact congrArg (fun c => (⟨i,j,c⟩ : Σ _ : Unit, Σ _ : Unit, Option Colour)) (g.property () () x y)
  extends_finite_diagram := by
    intro V _ f h hc
    have hh (a b : V) : colour (f a).2 (f b).2 = colour (h a).2 (h b).2 :=
      congrArg (fun c : Σ _ : Unit, Σ _ : Unit, Option Colour => c.2.2) (hc a b)
    obtain ⟨g,hg⟩ := finite_extension (fun a => (f a).2) (fun a => (h a).2) hh
    exact ⟨g,fun a => Sigma.ext (Subsingleton.elim _ _) (heq_of_eq (hg a))⟩

def packetEq : ColourEq source () :=
  ⟨Setoid.comap packet (⊥ : Setoid ℕ),by
    intro x y x' y' h
    exact (kernels_of_colour_eq h).1⟩

def firstEq : ColourEq source () :=
  ⟨Setoid.comap (fun x => (packet x,first x)) (⊥ : Setoid (ℕ × Bool)),by
    intro x y x' y' h
    change ((packet x,first x) = (packet y,first y)) ↔
      ((packet x',first x') = (packet y',first y'))
    simpa only [Prod.mk.injEq] using (kernels_of_colour_eq h).2.1⟩

def secondEq : ColourEq source () :=
  ⟨Setoid.comap (fun x => (packet x,second x)) (⊥ : Setoid (ℕ × Bool)),by
    intro x y x' y' h
    change ((packet x,second x) = (packet y,second y)) ↔
      ((packet x',second x') = (packet y',second y'))
    simpa only [Prod.mk.injEq] using (kernels_of_colour_eq h).2.2⟩

def packetClassEquiv (x : Point) : ClassPoint source () packetEq x ≃ Bool × Bool where
  toFun y := (first y.val,second y.val)
  invFun p := ⟨(packet x,p.1,p.2),rfl⟩
  left_inv y := Subtype.ext (Prod.ext y.property rfl)
  right_inv p := by cases p; rfl

theorem packet_class_card (x : Point) : Nat.card (ClassPoint source () packetEq x) = 4 :=
  (Nat.card_congr (packetClassEquiv x)).trans (by simp)

theorem packet_finite : RealClosure.Bounds.FiniteClasses source packetEq := by
  intro x
  exact Finite.of_equiv (Bool × Bool) (packetClassEquiv x).symm

/-- A single actual external pair forces a FULL invariant equivalence
to be Top. Same-packet pairs pass through a fresh third packet. -/
theorem external_pair_top (E : ColourEq source ()) (p q : Point)
    (hpq : E p q) (hne : packet p ≠ packet q) : E = ⊤ := by
  have hApart (x y : Point) (hxy : packet x ≠ packet y) : E x y :=
    (E.property p q x y (by
      change colour p q = colour x y
      simp only [colour,ite_eq_right hne,ite_eq_right hxy])).mp hpq
  apply ColourEq.ext
  intro x y
  constructor
  · intro _; trivial
  · intro _
    let z : Point := (max (packet x) (packet y) + 1,false,false)
    have hx : packet x ≠ packet z := Nat.ne_of_lt (Nat.lt_succ_of_le (Nat.le_max_left _ _))
    have hy : packet y ≠ packet z := Nat.ne_of_lt (Nat.lt_succ_of_le (Nat.le_max_right _ _))
    exact E.val.trans (hApart x z hx) (hApart z y hy.symm)

theorem finite_equivalence_le_packet (E : ColourEq source ())
    (hf : RealClosure.Bounds.FiniteClasses source E) : E ≤ packetEq := by
  intro x y hxy
  by_contra hne
  have he := external_pair_top E x y hxy hne
  letI := hf (0,false,false)
  have hc : Infinite (ClassPoint source () E (0,false,false)) := by
    have hEq : E = ⊤ := he
    let f : Point → ClassPoint source () E (0,false,false) := fun z => ⟨z,by rw [hEq]; trivial⟩
    exact Infinite.of_injective f (fun _ _ h => congrArg Subtype.val h)
  letI := hc
  exact not_finite (ClassPoint source () E (0,false,false))

/-- The greatest finite-class packet Sigma(Id) is literally this
four-point packet relation, not an assumed abstract finite kernel. -/
theorem greatest_finite_packet : RealClosure.Bounds.finitePacket (G := FullAut source) source homogeneous = packetEq :=
  le_antisymm
    (finite_equivalence_le_packet _ (RealClosure.Bounds.finitePacket_finite (G := FullAut source) source homogeneous))
    (RealClosure.Bounds.le_finitePacket (G := FullAut source) source homogeneous packetEq packet_finite)

theorem packet_ne_top : packetEq ≠ ⊤ := by
  intro he
  have hh : packetEq (0,false,false) (1,false,false) := by rw [he]; trivial
  exact Nat.zero_ne_one hh

theorem packet_strict_upper_top (E : ColourEq source ()) (hE : packetEq < E) : E = ⊤ := by
  have hex : ∃ x y : Point, E x y ∧ ¬packetEq x y := by
    by_contra hn
    have hle : E ≤ packetEq := by
      intro x y hxy
      by_contra hnot
      exact hn ⟨x,y,hxy,hnot⟩
    exact hE.not_ge hle
  obtain ⟨x,y,hxy,hnot⟩ := hex
  exact external_pair_top E x y hxy hnot

theorem packet_proper_MI : InfIrred packetEq := by
  constructor
  · intro hmax
    exact packet_ne_top hmax.eq_top
  · intro E F hmeet
    by_cases hE : E = packetEq
    · exact Or.inl hE
    right
    by_contra hF
    have hPE : packetEq ≤ E := by rw [← hmeet]; exact inf_le_left
    have hPF : packetEq ≤ F := by rw [← hmeet]; exact inf_le_right
    have hET := packet_strict_upper_top E (lt_of_le_of_ne hPE (Ne.symm hE))
    have hFT := packet_strict_upper_top F (lt_of_le_of_ne hPF (Ne.symm hF))
    exact packet_ne_top (hmeet.symm.trans (by rw [hET,hFT]; simp))

theorem owner_coordinate_meet : firstEq ⊓ secondEq = ⊥ := by
  apply ColourEq.ext
  intro x y
  change ((packet x,first x) = (packet y,first y) ∧
    (packet x,second x) = (packet y,second y)) ↔ x = y
  constructor
  · rintro ⟨h1,h2⟩
    exact Prod.ext (congrArg (fun p : ℕ × Bool => p.1) h1)
      (Prod.ext (congrArg (fun p : ℕ × Bool => p.2) h1) (congrArg (fun p : ℕ × Bool => p.2) h2))
  · rintro rfl
    exact ⟨rfl,rfl⟩

/-- Pull an actual owner equivalence back to its pure clone source. All
FULL optional clone colours erase to the exact old optional colours. -/
def cloneEq (E : ColourEq source ()) : ColourEq (CloneSAP.source source) () :=
  ⟨Setoid.comap Prod.fst E.val,by
    intro x y x' y' hc
    have ho := congrArg (fun c => c.bind (CloneSAP.eraseAtom source)) hc
    rw [CloneSAP.colour_erase,CloneSAP.colour_erase] at ho
    exact E.property _ _ _ _ ho⟩

theorem clone_coordinate_meet : cloneEq firstEq ⊓ cloneEq secondEq = fullCloneKernel source () := by
  apply ColourEq.ext
  intro x y
  change (firstEq x.1 y.1 ∧ secondEq x.1 y.1) ↔ x.1 = y.1
  have h := congrArg (fun E : ColourEq source () => E x.1 y.1) owner_coordinate_meet
  exact (congrArg (fun p : Prop => p) h).to_iff

theorem clone_coordinate_strict :
    fullCloneKernel source () < cloneEq firstEq ∧ fullCloneKernel source () < cloneEq secondEq := by
  have hle (E : ColourEq source ()) : fullCloneKernel source () ≤ cloneEq E := by
    intro x y hxy
    change E x.1 y.1
    exact hxy ▸ E.val.refl x.1
  constructor
  · apply lt_of_le_of_ne (hle firstEq)
    intro he
    have hh : cloneEq firstEq ((0,false,false),0) ((0,false,true),0) := rfl
    rw [← he] at hh
    have hn : (false : Bool) = true := congrArg (fun x : Point => second x) hh
    cases hn
  · apply lt_of_le_of_ne (hle secondEq)
    intro he
    have hh : cloneEq secondEq ((0,false,false),0) ((0,true,false),0) := rfl
    rw [← he] at hh
    have hn : (false : Bool) = true := congrArg (fun x : Point => first x) hh
    cases hn

/-- The actual UNSPLIT clone kernel fails FULL meet irreducibility even
though the original greatest finite-class equivalence is proper MI. -/
theorem unsplit_clone_kernel_not_MI : ¬InfIrred (fullCloneKernel source ()) := by
  intro h
  rcases h.2 clone_coordinate_meet with hE | hF
  · exact clone_coordinate_strict.1.ne hE.symm
  · exact clone_coordinate_strict.2.ne hF.symm

theorem infinite_homogeneous_packet_boundary :
    Infinite Point ∧ HomogeneousSource source (FullAut source) ∧
      (∀ x : Point, Nat.card (ClassPoint source () packetEq x) = 4) ∧
      RealClosure.Bounds.finitePacket (G := FullAut source) source homogeneous = packetEq ∧
      InfIrred packetEq ∧
      cloneEq firstEq ⊓ cloneEq secondEq = fullCloneKernel source () ∧
      fullCloneKernel source () < cloneEq firstEq ∧
      fullCloneKernel source () < cloneEq secondEq ∧
      ¬InfIrred (fullCloneKernel source ()) :=
  ⟨inferInstance,homogeneous,packet_class_card,greatest_finite_packet,packet_proper_MI,
    clone_coordinate_meet,clone_coordinate_strict.1,clone_coordinate_strict.2,
    unsplit_clone_kernel_not_MI⟩

end
end CCO.CloneTupleGeometry.InfinitePacketBoundary
