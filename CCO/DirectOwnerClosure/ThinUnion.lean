import CCO.DirectOwnerClosure.Basic
import CCO.FinitePackets.Normalization.TerminalThin
import CCO.FinitePackets.Normalization.ElementaryAbelian
import CCO.FinitePackets.Normalization.ColourTransport

/-! Literal thin functions on an entire invariant owner union.  A translation
can move named owners: it is an original-global automorphism and a total
definable function on the union, not necessarily a named automorphism. -/
universe v w t
namespace CCO.DirectOwnerClosure
open ParityHasse.Original RealHull.Geometry FinitePackets.Geometry
open FinitePackets.Normalization

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

/-- C14: the local C22 regularization contradiction, without the bundled
normalization-chain/terminal-thin theorem. -/
theorem packet_thin (normalized : NoFiniteExactKernel S) : ThinBottom S (packet S H) := by
  intro c hc
  cases c with
  | none => exact thin_none S
  | some a =>
    by_contra hnt
    have hn := squareKernel_nonidentity_of_nonthin S H (packet S H) hc hnt
    have he := normalized (squareKernel S H (packet S H))
      (squareKernel_finite S H (packet S H) (finiteIndex_sigma S H ⊥))
      (squareKernelExact S H (packet S H)) (squareKernelExact_represents S H (packet S H))
    exact (ne_of_gt hn) he

abbrev PacketTranslations := Translation S (packet S H) G

theorem normalized_packet_group (normalized : NoFiniteExactKernel S) :
    ThinBottom S (packet S H) ∧ Finite (PacketTranslations S H) ∧
      ∃ d : Nat, Nonempty (PacketTranslations S H ≃* Multiplicative (Fin d → ZMod 2)) ∧
        Nat.card (PacketTranslations S H) = 2^d := by
  have hthin := packet_thin S H normalized
  exact ⟨hthin,translation_finite S (packet S H) H hthin,
    translation_elementary_abelian S (packet S H) H hthin⟩

variable (hthin : ThinBottom S (packet S H))

/-- Every literal translation preserves the full original fine language. -/
def translation_realAut (e : PacketTranslations S H) : FullAut S :=
  ⟨e.val,by
    constructor
    · intro p; cases p
    · intro c x y
      change col S (e.val x) (e.val y) = c ↔ col S x y = c
      rw [translation_preserves_colour S (packet S H) H hthin]⟩

include hthin in
theorem translation_central_full (e : PacketTranslations S H) (g : FullAut S) (x : M) :
    e.val (g.val x) = g.val (e.val x) := by
  have hc := translationColour_below S (packet S H) H e
  apply (hthin _ hc (g.val x)).unique
  · exact translationColour_at S (packet S H) H e (g.val x)
  · exact (fullAut_colour S g x (e.val x)).trans
      (translationColour_at S (packet S H) H e x)

def translationOwnerPerm (E : ColourEq S ()) (e : PacketTranslations S H) :
    Equiv.Perm (Owner S E) where
  toFun := Quotient.map e.val (fun x y h =>
    (fullAut_equivalence S E (translation_realAut S H hthin e) x y).mpr h)
  invFun := Quotient.map e.val.symm (fun x y h => by
    apply (fullAut_equivalence S E (translation_realAut S H hthin e)
      (e.val.symm x) (e.val.symm y)).mp
    change E (e.val (e.val.symm x)) (e.val (e.val.symm y))
    simpa only [Equiv.apply_symm_apply] using h)
  left_inv b := Quotient.inductionOn b (fun x => by
    change Quotient.mk E.val (e.val.symm (e.val x)) = Quotient.mk E.val x
    rw [Equiv.symm_apply_apply])
  right_inv b := Quotient.inductionOn b (fun x => by
    change Quotient.mk E.val (e.val (e.val.symm x)) = Quotient.mk E.val x
    rw [Equiv.apply_symm_apply])

/-- C15: an actual action on quotient owners, with no freeness or
faithfulness requirement on this action. -/
@[instance_reducible] def translation_owner_action (E : ColourEq S ()) :
    MulAction (PacketTranslations S H) (Owner S E) where
  smul e b := translationOwnerPerm S H hthin E e b
  one_smul b := Quotient.inductionOn b (fun _ => rfl)
  mul_smul _e _f b := Quotient.inductionOn b (fun _ => rfl)

theorem translation_owner_mk (E : ColourEq S ()) (e : PacketTranslations S H) (x : M) :
    letI := translation_owner_action S H hthin E
    e • owner S E x = owner S E (e.val x) := rfl

def OwnerInvariant (E : ColourEq S ()) (B : Finset (Owner S E)) : Prop :=
  letI := translation_owner_action S H hthin E
  ∀ (e : PacketTranslations S H) b, b ∈ B → e • b ∈ B

/-- C16: invariance is equivalent to saturation by WHOLE real packets. -/
theorem ownerInvariant_iff_packet_saturated (E : ColourEq S ()) (B : Finset (Owner S E)) :
    OwnerInvariant S H hthin E B ↔
      ∀ x : OwnerUnion S E B, ∀ y : M, packet S H x.val y → owner S E y ∈ B := by
  let := translation_owner_action S H hthin E
  constructor
  · intro h x y hxy
    obtain ⟨e,he,_⟩ := translation_regular S (packet S H) H hthin x.val y hxy
    have hh := h e (owner S E x.val) x.property
    change owner S E (e.val x.val) ∈ B at hh
    simpa only [he] using hh
  · intro h e b hb
    obtain ⟨x,rfl⟩ := Quotient.mk''_surjective b
    exact h ⟨x,hb⟩ (e.val x) (translation_in_packet S (packet S H) G e x)

/-- The thin graph defines a TOTAL function on the invariant union. -/
def thinFunction (E : ColourEq S ()) (B : Finset (Owner S E))
    (hB : OwnerInvariant S H hthin E B) (e : PacketTranslations S H)
    (x : OwnerUnion S E B) : OwnerUnion S E B :=
  ⟨e.val x.val,(ownerInvariant_iff_packet_saturated S H hthin E B).mp hB x _
    (translation_in_packet S (packet S H) G e x.val)⟩

theorem thinFunction_graph (E : ColourEq S ()) (B : Finset (Owner S E))
    (hB : OwnerInvariant S H hthin E B) (e : PacketTranslations S H)
    (x : OwnerUnion S E B) :
    col S x.val (thinFunction S H hthin E B hB e x).val =
      translationColour S (packet S H) (G := G) e :=
  translationColour_at S (packet S H) H e x.val

/-- Its literal old-colour graph has exactly one output in the union. -/
theorem thinFunction_unique (E : ColourEq S ()) (B : Finset (Owner S E))
    (hB : OwnerInvariant S H hthin E B) (e : PacketTranslations S H)
    (x : OwnerUnion S E B) :
    ∃! y : OwnerUnion S E B, col S x.val y.val =
      translationColour S (packet S H) (G := G) e := by
  refine ⟨thinFunction S H hthin E B hB e x,thinFunction_graph S H hthin E B hB e x,?_⟩
  intro y hy
  apply Subtype.ext
  exact (hthin _ (translationColour_below S (packet S H) H e) x.val).unique hy
    (thinFunction_graph S H hthin E B hB e x)

/-- C17: each value of a thin function is individually definable from its
input in the FULL owner-named language.  The function itself need not
preserve the individual owner predicates. -/
theorem thinFunction_definable (E : ColourEq S ()) (B : Finset (Owner S E))
    (hB : OwnerInvariant S H hthin E B) (e : PacketTranslations S H)
    (A : Finset (OwnerUnion S E B)) (a : OwnerUnion S E B) (ha : a ∈ A) :
    thinFunction S H hthin E B hB e a ∈ definableClosure (NamedAut S E B) A := by
  intro g hg
  apply Subtype.ext
  have hga : g.val a = a := hg a ha
  have hc := namedAut_colour S E B g a (thinFunction S H hthin E B hB e a)
  rw [hga] at hc
  have hgraph : col S a.val (e.val a.val) = translationColour S (packet S H) (G := G) e :=
    translationColour_at S (packet S H) H e a.val
  exact (hthin _ (translationColour_below S (packet S H) H e) a.val).unique
    (hc.trans hgraph) hgraph

theorem packet_target_definable (E : ColourEq S ()) (B : Finset (Owner S E))
    (hB : OwnerInvariant S H hthin E B) (A : Finset (OwnerUnion S E B)) :
    {x : OwnerUnion S E B | ∃ a ∈ A, packet S H a.val x.val} ⊆
      definableClosure (NamedAut S E B) A := by
  rintro x ⟨a,ha,hax⟩
  obtain ⟨e,he,_⟩ := translation_regular S (packet S H) H hthin a.val x.val hax
  have hx : thinFunction S H hthin E B hB e a = x := Subtype.ext he
  rw [← hx]
  exact thinFunction_definable S H hthin E B hB e A a ha

theorem packet_target_algebraic (E : ColourEq S ()) (B : Finset (Owner S E))
    (hB : OwnerInvariant S H hthin E B) (A : Finset (OwnerUnion S E B)) :
    {x : OwnerUnion S E B | ∃ a ∈ A, packet S H a.val x.val} ⊆
      algebraicClosure (NamedAut S E B) A :=
  (packet_target_definable S H hthin E B hB A).trans
    (definable_subset_algebraic (NamedAut S E B) A)

end CCO.DirectOwnerClosure
