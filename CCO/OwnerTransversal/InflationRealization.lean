import CCO.OwnerTransversal.InflationLanguage

/-! Finite ACTUAL full inflations realize in N_B. Repeated U origins
are recognized by literal equality, so all phases of one packet use the
SAME old real origin. All t_g and every fine pair are retained. -/
universe v w t
open scoped FirstOrder
open FirstOrder FirstOrder.Language
namespace CCO.OwnerTransversal.Inflation
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization CountableColour TransversalAge
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)

/-- C44's finite realization preserves equality and EVERY fine pair,
including internal packet pairs, and all displayed translation equations. -/
theorem realize_finite_tuple {I : Type*} [Finite I] (p : I → Carrier S H R B) :
    ∃ f : I → NamedCarrier S H R B,
      (∀ i, (namedTable S H R B).owner (f i) = (table S H R B hB).owner (p i)) ∧
      (∀ i j, col S (f i).val (f j).val = (table S H R B hB).colour (p i) (p j)) ∧
      (∀ i j, f i = f j ↔ p i = p j) ∧
      ∀ i j (e : ResidualData.PacketGroup S H),
        p i = (action S H R B).smul e (p j) → f i = packetPoint S H R B hB e (f j) := by
  obtain ⟨o,ho,hc,hs⟩ := TransversalAge.realize_tuple S H R B (fun i => (p i).1)
  have sameOrigin (i j : I) (hij : (p i).1 = (p j).1) : o i = o j := by
    apply Subtype.ext
    apply (col_none S _ _).mp
    exact (hc i j).trans (hij ▸ TransversalAge.colour_diag S H R B (p j).1)
  let f : I → NamedCarrier S H R B := fun i => packetPoint S H R B hB (p i).2 (o i)
  have hcol (i j : I) : col S (f i).val (f j).val =
      (table S H R B hB).colour (p i) (p j) := by
    exact realized_matrix S H R B (fun i => (p i).1) o hc hB i j (p i).2 (p j).2
  refine ⟨f,?_,hcol,?_,?_⟩
  · intro i
    have hh := named_owner_equivariant S H R B hB (p i).2 (o i)
    change ownerLabel S H R B (packetPoint S H R B hB (p i).2 (o i)) =
      (packetOwnerSetAction S H R B hB).smul (p i).2 ((limitTable S H R B).owner (p i).1)
    exact hh.trans (congrArg ((packetOwnerSetAction S H R B hB).smul (p i).2) (ho i))
  · intro i j
    constructor
    · intro he
      have hF : finitePacket S H (o i).val (o j).val := by
        have hi := translation_in_packet S (finitePacket S H) G (p i).2 (o i).val
        have hj := translation_in_packet S (finitePacket S H) G (p j).2 (o j).val
        have hv : (p i).2.val (o i).val = (p j).2.val (o j).val := congrArg Subtype.val he
        rw [hv] at hi
        exact (finitePacket S H).val.trans hi ((finitePacket S H).val.symm hj)
      have hu : (p i).1 = (p j).1 := by
        by_contra hn
        exact hs i j hn hF
      have hoij := sameOrigin i j hu
      have hg : (p i).2 = (p j).2 := by
        apply named_action_free S H R B hB (o j)
        exact (congrArg (packetPoint S H R B hB (p i).2) hoij).symm.trans he
      exact Prod.ext hu hg
    · intro he
      change packetPoint S H R B hB (p i).2 (o i) = packetPoint S H R B hB (p j).2 (o j)
      rw [sameOrigin i j (congrArg Prod.fst he),congrArg Prod.snd he]
  · intro i j e he
    change p i = ((p j).1,e * (p j).2) at he
    have hu := congrArg (fun z : Carrier S H R B => z.1) he
    have hg : (p i).2 = e * (p j).2 := congrArg Prod.snd he
    change packetPoint S H R B hB (p i).2 (o i) =
      packetPoint S H R B hB e (packetPoint S H R B hB (p j).2 (o j))
    rw [sameOrigin i j hu,hg,packetPoint_mul]

/-- Every finite FULL packet-language substructure of the actual
inflation embeds in the actual named source, with all functions retained. -/
theorem realize_finite_substructure
    (A : @Substructure (Signature S H R B) (Carrier S H R B) (inflationStructure S H R B hB))
    [Finite A] :
    letI := inflationStructure S H R B hB
    letI := sourceStructure S H R B hB
    Nonempty (A ↪[Signature S H R B] NamedCarrier S H R B) := by
  letI := action S H R B
  letI := packetNamedAction S H R B hB
  letI := inflationStructure S H R B hB
  letI := sourceStructure S H R B hB
  letI := PacketLanguage.subaction (table S H R B hB) A
  obtain ⟨f,ho,hc,he,ht⟩ := realize_finite_tuple S H R B hB (Subtype.val : A → Carrier S H R B)
  let e : A ↪ NamedCarrier S H R B := ⟨f,fun i j hij => Subtype.ext ((he i j).mp hij)⟩
  refine ⟨{
    toFun := e
    inj' := e.injective
    map_fun' := ?_
    map_rel' := ?_ }⟩
  · intro n F x
    cases F with
    | translate g =>
      change f (g • x 0) = packetPoint S H R B hB g (f (x 0))
      exact ht (g • x 0) (x 0) g rfl
  · intro n r x
    cases r with
    | owner b =>
      change (namedTable S H R B).owner (f (x 0)) = b ↔ (table S H R B hB).owner (x 0).val = b
      rw [ho]
    | colour c =>
      change col S (f (x 0)).val (f (x 1)).val = c ↔
        (table S H R B hB).colour (x 0).val (x 1).val = c
      rw [hc]

omit [Infinite M] in
/-- Independent accepted exact lifting aligns arbitrary finite named
tuples, including repeated values and all unused owners of B. -/
theorem named_tuple_alignment {I : Type*} [Finite I]
    (x y : I → NamedCarrier S H R B)
    (ho : ∀ i, (namedTable S H R B).owner (x i) = (namedTable S H R B).owner (y i))
    (hc : ∀ i j, col S (x i).val (x j).val = col S (y i).val (y j).val) :
    ∃ f : NamedAut S H R B, ∀ i, f.val (x i) = y i := by
  letI := originalQuotientAction S H R.E
  let q : ↥B → Owner S H R := Subtype.val
  have cover (i : I) : ∃ j, q j = owner S H R (x i).val ∧ q j = owner S H R (y i).val :=
    ⟨⟨owner S H R (x i).val,(x i).property⟩,rfl,congrArg Subtype.val (ho i)⟩
  obtain ⟨g,hg,hq⟩ := residual_joint_lifting S H R
    (fun i => (x i).val) (fun i => (y i).val) q q hc
    (fun _ _ => GroupActions.orbital_nonempty _ _) cover
  refine ⟨restrictMotion S H R B g (fun b hb => hq ⟨b,hb⟩),?_⟩
  intro i
  exact Subtype.ext (hg i)

def sourceEquiv (f : NamedAut S H R B) :
    letI := sourceStructure S H R B hB
    NamedCarrier S H R B ≃[Signature S H R B] NamedCarrier S H R B := by
  letI := packetNamedAction S H R B hB
  exact PacketLanguage.equiv (namedTable S H R B) (namedTable S H R B) f.val
    (fun x => Subtype.ext (NamedAut.owner_fixed f x))
    (NamedAut.colour_fixed f) (fun e x => namedAut_commutes S H R B hB f e x)

/-- C46's actual reverse finite-extension instance. The finite inflation
realization is first built, then its whole old image is aligned by one
actual named automorphism. No source model/extension provider is assumed. -/
theorem finite_extension_to_source :
    letI := inflationStructure S H R B hB
    letI := sourceStructure S H R B hB
    PacketBackAndForth.FiniteExtension (Signature S H R B)
      (Carrier S H R B) (NamedCarrier S H R B) := by
  letI := inflationStructure S H R B hB
  letI := sourceStructure S H R B hB
  intro A C _ _ hAC f
  obtain ⟨g⟩ := realize_finite_substructure S H R B hB C
  let inc := Substructure.inclusion hAC
  let x : A → NamedCarrier S H R B := fun a => g (inc a)
  let y : A → NamedCarrier S H R B := f
  have ho : ∀ a, (namedTable S H R B).owner (x a) = (namedTable S H R B).owner (y a) := by
    intro a
    have hx := (g.comp inc).map_rel (CountableColour.Symbol.owner ((namedTable S H R B).owner (x a))) (fun _ => a)
    have hy := f.map_rel (CountableColour.Symbol.owner ((namedTable S H R B).owner (x a))) (fun _ => a)
    exact ((hy.mpr (hx.mp rfl))).symm
  have hc : ∀ a b, col S (x a).val (x b).val = col S (y a).val (y b).val := by
    intro a b
    have hx := (g.comp inc).map_rel (CountableColour.Symbol.colour (col S (x a).val (x b).val)) (![a,b])
    have hy := f.map_rel (CountableColour.Symbol.colour (col S (x a).val (x b).val)) (![a,b])
    exact ((hy.mpr (hx.mp rfl))).symm
  obtain ⟨k,hk⟩ := named_tuple_alignment S H R B x y ho hc
  refine ⟨(sourceEquiv S H R B hB k).toEmbedding.comp g,?_⟩
  apply DFunLike.ext
  intro a
  change k.val (g (inc a)) = f a
  exact hk a

end
end CCO.OwnerTransversal.Inflation
