import CCO.OwnerTransversal.TransversalAge

/-! Every actual residual owner class has arbitrarily many separated real
packets. Actual finite origin charts then prove that every named sort of
the internally constructed limit is infinite. No original SAP, assumed
infinite transversal, or free action on owners is used. -/

universe v w t
namespace CCO.OwnerTransversal.TransversalAge
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open CountableColour

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (R : ResidualData S H)
variable (B : Finset (Owner S H R))

theorem fresh_origin_in_owner (q : ↥B) (A : Finset (NamedCarrier S H R B)) :
    ∃ x : NamedCarrier S H R B,
      ownerLabel S H R B x = q ∧ x ∉ namedPacketFinset S H R B A := by
  obtain ⟨a,ha⟩ := Quotient.exists_rep q.val
  have hinf : {x : M | R.E a x}.Infinite := by
    intro hf
    exact R.infinite ((finiteClasses_iff_at S H R.E a).mpr (Set.finite_coe_iff.mpr hf))
  let C := realBase S H R B (namedPacketFinset S H R B A)
  obtain ⟨x,hax,hx⟩ := hinf.exists_notMem_finset C
  have howner : owner S H R x = q.val :=
    (Quotient.sound hax).symm.trans ha
  let z : NamedCarrier S H R B := ⟨x,howner ▸ q.property⟩
  refine ⟨z,Subtype.ext howner,?_⟩
  intro hz
  exact hx ((mem_realBase S H R B _ z).mpr hz)

/-- Arbitrary finite multiplicities are constructed inside ONE actual
owner class, outside all packets already selected. -/
theorem separated_origins (q : ↥B) (n : ℕ) :
    ∃ f : Fin n → NamedCarrier S H R B,
      (∀ i, ownerLabel S H R B (f i) = q) ∧
      ∀ i j, i ≠ j → ¬ finitePacket S H (f i).val (f j).val := by
  classical
  induction n with
  | zero => exact ⟨Fin.elim0,fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨f,ho,hs⟩ := ih
    let A := Finset.univ.image f
    obtain ⟨x,hxq,hx⟩ := fresh_origin_in_owner S H R B q A
    have hfresh (j : Fin n) : ¬ finitePacket S H x.val (f j).val := by
      intro hF
      apply hx
      apply (mem_namedPacketFinset S H R B A x).mpr
      refine ⟨(f j).val,?_,(finitePacket S H).val.symm hF⟩
      exact (mem_realBase S H R B A (f j)).mpr
        (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
    refine ⟨Fin.cases x f,Fin.cases hxq ho,?_⟩
    refine Fin.cases ?_ (fun i => ?_)
    · refine Fin.cases ?_ (fun j => ?_)
      · intro h; exact False.elim (h rfl)
      · intro _; exact hfresh j
    · refine Fin.cases ?_ (fun j => ?_)
      · intro _ hF; exact hfresh i ((finitePacket S H).val.symm hF)
      · intro hne
        exact hs i j (fun he => hne (congrArg Fin.succ he))

theorem owner_sort_embeddings [Infinite M] (q : ↥B) (n : ℕ) :
    Nonempty (Fin n ↪ {u : U S H R B | (limitTable S H R B).owner u = q}) := by
  obtain ⟨f,ho,hs⟩ := separated_origins S H R B q n
  let Q : Chart S H R B := {
    n := n
    table := ⟨fun _ => q,fun i j => col S (f i).val (f j).val⟩
    realized := ⟨⟨f,ho,fun _ _ => rfl,hs⟩⟩ }
  obtain ⟨e,he,_⟩ := embed_chart S H R B Q
  exact ⟨⟨fun i => ⟨e i,he i⟩,fun _ _ hh => e.injective (congrArg Subtype.val hh)⟩⟩

/-- C35/C44: ALL named sorts of the ACTUAL internal limit are infinite. -/
theorem owner_sort_infinite [Infinite M] (q : ↥B) :
    Set.Infinite {u : U S H R B | (limitTable S H R B).owner u = q} := by
  intro hf
  let : Fintype {u : U S H R B | (limitTable S H R B).owner u = q} := hf.fintype
  let n := Fintype.card {u : U S H R B | (limitTable S H R B).owner u = q}
  obtain ⟨f⟩ := owner_sort_embeddings S H R B q (n + 1)
  have hc := Fintype.card_le_of_injective f f.injective
  have hbad : n + 1 ≤ n := by simpa only [Fintype.card_fin] using hc
  exact Nat.not_succ_le_self n hbad

end
end CCO.OwnerTransversal.TransversalAge
