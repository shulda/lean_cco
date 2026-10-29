import CCO.OwnerTransversal.InflationLanguage
import CCO.OwnerTransversal.TransversalExtension
import CCO.OwnerTransversal.SourcePacketCharts
import CCO.OwnerTransversal.AlignedPacketCharts

/-! The ACTUAL closed extension property in the hard direction N_B→I(U).
Origins on the protectedSet old packets are chosen from the prescribed
embedding's POINT phases, then the actual U extension theorem is applied. -/
open scoped FirstOrder
open FirstOrder FirstOrder.Language
universe v w t
namespace CCO.OwnerTransversal.Inflation
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization CountableColour TransversalAge
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)

/-- Inflate an actual chosen source packet chart after its origin diagram
has embedded in the actual U, retaining every function and fine colour. -/
def chartEmbedding
    (D : @Substructure (Signature S H R B) (NamedCarrier S H R B) (sourceStructure S H R B hB))
    {I : Type*} (o : I → D) (chart : D ≃ I × ResidualData.PacketGroup S H)
    (reconstruct : letI := packetNamedAction S H R B hB
      letI := PacketLanguage.subaction (namedTable S H R B) D
      ∀ x : D, (chart x).2 • o (chart x).1 = x)
    (equivariant : letI := packetNamedAction S H R B hB
      letI := PacketLanguage.subaction (namedTable S H R B) D
      ∀ (g : ResidualData.PacketGroup S H) x, chart (g • x) = ((chart x).1,g * (chart x).2))
    (e : I ↪ U S H R B)
    (ho : ∀ i, (limitTable S H R B).owner (e i) = ownerLabel S H R B (o i).val)
    (hc : ∀ i j, (limitTable S H R B).colour (e i) (e j) = col S (o i).val.val (o j).val.val) :
    letI := sourceStructure S H R B hB
    letI := inflationStructure S H R B hB
    D ↪[Signature S H R B] Carrier S H R B := by
  letI := packetNamedAction S H R B hB
  letI := action S H R B
  letI := packetOwnerSetAction S H R B hB
  letI := sourceStructure S H R B hB
  letI := inflationStructure S H R B hB
  letI := PacketLanguage.subaction (namedTable S H R B) D
  let f : D ↪ Carrier S H R B := {
    toFun x := (e (chart x).1,(chart x).2)
    inj' := by
      intro x y he
      apply chart.injective
      exact Prod.ext (e.injective (congrArg Prod.fst he)) (congrArg (fun p : Carrier S H R B => p.2) he) }
  have hp (x : D) : x.val = packetPoint S H R B hB (chart x).2 (o (chart x).1).val :=
    (congrArg Subtype.val (reconstruct x)).symm
  have hOwner (x : D) : (table S H R B hB).owner (f x) = ownerLabel S H R B x.val := by
    change (chart x).2 • (limitTable S H R B).owner (e (chart x).1) = ownerLabel S H R B x.val
    rw [ho,hp x]
    exact (named_owner_equivariant S H R B hB _ _).symm
  have hColour (x y : D) : (table S H R B hB).colour (f x) (f y) = col S x.val.val y.val.val := by
    change switchColour S (finitePacket S H) ((chart x).2 * (chart y).2)
      ((limitTable S H R B).colour (e (chart x).1) (e (chart y).1)) = col S x.val.val y.val.val
    rw [hc,hp x,hp y]
    exact (two_endpoint_transport S (finitePacket S H) H (R.packet_thin S H) _ _ _ _).symm
  have hTranslate (g : ResidualData.PacketGroup S H) (x : D) : f (g • x) = g • f x := by
    change (e (chart (g • x)).1,(chart (g • x)).2) = (e (chart x).1,g * (chart x).2)
    rw [equivariant]
  exact {
    toFun := f
    inj' := f.injective
    map_fun' := by
      intro n F x
      cases F with
      | translate g => exact hTranslate g (x 0)
    map_rel' := by
      intro n r x
      cases r with
      | owner b => exact (congrArg (· = b) (hOwner (x 0))).to_iff
      | colour c => exact (congrArg (· = c) (hColour (x 0) (x 1))).to_iff }

/-- C45: the genuine closed extension property of the ACTUAL inflation.
The protected origins come from the inverse POINT phase of the prescribed
old embedding, so every old packet point is retained literally. -/
theorem finite_extension_to_inflation :
    letI := sourceStructure S H R B hB
    letI := inflationStructure S H R B hB
    PacketBackAndForth.FiniteExtension (Signature S H R B)
      (NamedCarrier S H R B) (Carrier S H R B) := by
  classical
  letI := packetNamedAction S H R B hB
  letI := action S H R B
  letI := packetOwnerSetAction S H R B hB
  letI := sourceStructure S H R B hB
  letI := inflationStructure S H R B hB
  intro A D _ _ hAD f
  letI := PacketLanguage.subaction (namedTable S H R B) D
  letI := PacketLanguage.subaction (namedTable S H R B) A
  let Q := packets S H R B hB D
  let I := PacketIndex S H R B hB D
  let protectedSet : Set D := {x | x.val ∈ A}
  letI : MulAction (ResidualData.PacketGroup S H) ↥protectedSet := {
    smul g a := ⟨g • a.val,PacketLanguage.translate_mem (namedTable S H R B) A g a.val.val a.property⟩
    one_smul a := Subtype.ext (one_smul _ a.val)
    mul_smul g h a := Subtype.ext (mul_smul g h a.val) }
  let intoA : ↥protectedSet → A := fun a => ⟨a.val.val,a.property⟩
  let fp : ↥protectedSet → Carrier S H R B := fun a => f (intoA a)
  have inclusion (g : ResidualData.PacketGroup S H) (a : ↥protectedSet) :
      (g • a).val = g • a.val := rfl
  have equivariant (g : ResidualData.PacketGroup S H) (a : ↥protectedSet) :
      fp (g • a) = ((fp a).1,g * (fp a).2) := by
    exact f.map_fun (PacketLanguage.Function.translate g) (fun _ => intoA a)
  let o : I → D := Q.anchoredOrigin protectedSet fp
  have po (i : I) : Q.packet (o i) = i := Q.packet_anchoredOrigin protectedSet inclusion fp i
  let chart := Q.anchoredCoordinates protectedSet inclusion fp
  have reconstruct (x : D) : (chart x).2 • o (chart x).1 = x := chart.symm_apply_apply x
  have chartAction (g : ResidualData.PacketGroup S H) (x : D) :
      chart (g • x) = ((chart x).1,g * (chart x).2) :=
    Q.anchoredCoordinates_action protectedSet inclusion fp g x
  let old : Set I := {i | ∃ a : ↥protectedSet, Q.packet a.val = i}
  let oldPoint (i : ↥old) : ↥protectedSet :=
    (Q.anchoredOrigin_protected protectedSet fp equivariant i.property).choose
  have oldOrigin (i : ↥old) : (oldPoint i).val = o i.val :=
    (Q.anchoredOrigin_protected protectedSet fp equivariant i.property).choose_spec.1
  have oldZero (i : ↥old) : (fp (oldPoint i)).2 = 1 :=
    (Q.anchoredOrigin_protected protectedSet fp equivariant i.property).choose_spec.2
  let v : ↥old → U S H R B := fun i => (fp (oldPoint i)).1
  have oldImage (i : ↥old) : fp (oldPoint i) = (v i,1) := Prod.ext rfl (oldZero i)
  have oldNamed (i : ↥old) : (intoA (oldPoint i)).val = (o i.val).val :=
    congrArg (fun x : D => x.val) (oldOrigin i)
  have vInj : Function.Injective v := by
    intro i j hij
    have he : fp (oldPoint i) = fp (oldPoint j) :=
      (oldImage i).trans ((show (v i,(1 : ResidualData.PacketGroup S H)) = (v j,1) from Prod.ext hij rfl).trans (oldImage j).symm)
    have ha : oldPoint i = oldPoint j :=
      Subtype.ext (Subtype.ext (congrArg (fun a : A => a.val) (f.injective he)))
    have ho : o i.val = o j.val := (oldOrigin i).symm.trans ((congrArg Subtype.val ha).trans (oldOrigin j))
    exact Subtype.ext ((po i.val).symm.trans ((congrArg Q.packet ho).trans (po j.val)))
  let oldEmbedding : ↥old ↪ U S H R B := ⟨v,vInj⟩
  have oldOwner (i : ↥old) : (limitTable S H R B).owner (oldEmbedding i) =
      ownerLabel S H R B (o i.val).val := by
    have hh := (f.map_rel (CountableColour.Symbol.owner (ownerLabel S H R B (intoA (oldPoint i)).val))
      (fun _ => intoA (oldPoint i))).mpr rfl
    change (table S H R B hB).owner (fp (oldPoint i)) =
      ownerLabel S H R B (intoA (oldPoint i)).val at hh
    rw [oldImage,table_owner_one,oldNamed] at hh
    exact hh
  have oldColour (i j : ↥old) : (limitTable S H R B).colour (oldEmbedding i) (oldEmbedding j) =
      col S (o i.val).val.val (o j.val).val.val := by
    have hh := (f.map_rel (CountableColour.Symbol.colour
      (col S (intoA (oldPoint i)).val.val (intoA (oldPoint j)).val.val))
      (![intoA (oldPoint i),intoA (oldPoint j)])).mpr rfl
    change (table S H R B hB).colour (fp (oldPoint i)) (fp (oldPoint j)) =
      col S (intoA (oldPoint i)).val.val (intoA (oldPoint j)).val.val at hh
    rw [oldImage,oldImage,table_colour_one,oldNamed,oldNamed] at hh
    exact hh
  have separated (i j : I) (hne : i ≠ j) :
      ¬ finitePacket S H (o i).val.val (o j).val.val := by
    intro hF
    exact hne ((po i).symm.trans (((packet_eq S H R B hB D (o i) (o j)).mpr hF).trans (po j)))
  obtain ⟨eU,hOld,hOwner,hColour⟩ := extend_origins S H R B
    (⟨Subtype.val,Subtype.val_injective⟩ : ↥old ↪ I)
    (fun i => (o i).val) separated oldEmbedding oldOwner oldColour
  let g := chartEmbedding S H R B hB D o chart reconstruct chartAction eU hOwner hColour
  refine ⟨g,?_⟩
  apply DFunLike.ext
  intro a
  let aP : ↥protectedSet := ⟨⟨a.val,hAD a.property⟩,a.property⟩
  let i : ↥old := ⟨Q.packet aP.val,⟨aP,rfl⟩⟩
  have hfst : (chart aP.val).1 = i.val := Q.anchoredCoordinates_fst protectedSet inclusion fp aP.val
  have hact : (chart aP.val).2 • oldPoint i = aP := by
    apply Subtype.ext
    rw [inclusion,oldOrigin]
    simpa only [hfst] using reconstruct aP.val
  have hf := equivariant (chart aP.val).2 (oldPoint i)
  rw [hact] at hf
  have hfirst := congrArg (fun p : Carrier S H R B => p.1) hf
  change (f a).1 = v i at hfirst
  have hphase : (chart aP.val).2 = (f a).2 :=
    Q.anchoredCoordinates_phase protectedSet inclusion fp equivariant aP
  change (eU (chart aP.val).1,(chart aP.val).2) = f a
  apply Prod.ext
  · change eU (chart aP.val).1 = (f a).1
    rw [hfst]
    exact (show eU i.val = v i from hOld i).trans hfirst.symm
  · exact hphase

end
end CCO.OwnerTransversal.Inflation
