import CCO.DirectOwnerClosure.RestrictionImage
import CCO.DirectOwnerClosure.ThinUnion

/-! C20--C21: actual FULL induced algebraicity, literal ambient packet
targets, empty unions, and finite closed packet unions. Countability and
ancillary homogeneity are absent from this entire proof path. -/
universe v w t
namespace CCO.DirectOwnerClosure
open ParityHasse.Original RealHull.Geometry FinitePackets.Geometry
open FinitePackets.Normalization
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

theorem mem_packetHull_realBase [DecidableEq M] (E : ColourEq S ())
    (B : Finset (Owner S E)) (A : Finset (OwnerUnion S E B)) (x : M) :
    x ∈ packetHull S H (realBase S E B A) ↔
      ∃ a ∈ A, packet S H a.val x := by
  constructor
  · rintro ⟨a,ha,hax⟩
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    exact ⟨b,hb,hax⟩
  · rintro ⟨a,ha,hax⟩
    exact ⟨a.val,Finset.mem_image.mpr ⟨a,ha,rfl⟩,hax⟩

theorem packetHull_realBase_subset_union [DecidableEq M] (hthin : ThinBottom S (packet S H))
    (E : ColourEq S ()) (B : Finset (Owner S E)) (hB : OwnerInvariant S H hthin E B)
    (A : Finset (OwnerUnion S E B)) :
    packetHull S H (realBase S E B A) ⊆ {x | owner S E x ∈ B} := by
  intro x hx
  obtain ⟨a,ha,hax⟩ := (mem_packetHull_realBase S H E B A x).mp hx
  exact (ownerInvariant_iff_packet_saturated S H hthin E B).mp hB a x hax

/-- C20, internal form. Every point of the target is individually definable
by a literal thin graph; the upper bound uses the actual restriction IMAGE. -/
theorem owner_union_acl [DecidableEq M] [Infinite M]
    (cco : SemanticCCO.{0,v,0,w} S) {E : ColourEq S ()} (hE : UniqueDirection S E)
    (normalized : NoFiniteExactKernel S) (B : Finset (Owner S E))
    (hB : OwnerInvariant S H (packet_thin S H normalized) E B)
    (A : Finset (OwnerUnion S E B)) :
    algebraicClosure (NamedAut S E B) A =
      {x : OwnerUnion S E B | x.val ∈ packetHull S H (realBase S E B A)} := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hnot
    exact outside_packet_induced_not_algebraic S H cco hE B A x hnot hx
  · intro x hx
    apply packet_target_algebraic S H (packet_thin S H normalized) E B hB A
    exact (mem_packetHull_realBase S H E B A x.val).mp hx

/-- The target is the WHOLE ambient packet hull, not its arbitrary
intersection with the owner union. Invariance supplies the missing inclusion. -/
theorem owner_union_real_acl [DecidableEq M] [Infinite M]
    (cco : SemanticCCO.{0,v,0,w} S) {E : ColourEq S ()} (hE : UniqueDirection S E)
    (normalized : NoFiniteExactKernel S) (B : Finset (Owner S E))
    (hB : OwnerInvariant S H (packet_thin S H normalized) E B)
    (A : Finset (OwnerUnion S E B)) :
    (fun x : OwnerUnion S E B => x.val) '' algebraicClosure (NamedAut S E B) A =
      packetHull S H (realBase S E B A) := by
  rw [owner_union_acl S H cco hE normalized B hB A]
  apply Set.Subset.antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact hy
  · intro x hx
    have hxB := packetHull_realBase_subset_union S H (packet_thin S H normalized) E B hB A hx
    exact ⟨⟨x,hxB⟩,hx,rfl⟩

theorem owner_union_acl_eq_named [DecidableEq M] [Infinite M]
    (cco : SemanticCCO.{0,v,0,w} S) {E : ColourEq S ()} (hE : UniqueDirection S E)
    (normalized : NoFiniteExactKernel S) (B : Finset (Owner S E))
    (hB : OwnerInvariant S H (packet_thin S H normalized) E B)
    (A : Finset (OwnerUnion S E B)) :
    algebraicClosure (NamedAut S E B) A =
      {x : OwnerUnion S E B | x.val ∈ ownerClosure S E B (realBase S E B A)} := by
  rw [named_owner_acl S H cco hE B,owner_union_acl S H cco hE normalized B hB A]

/-- C21: the empty real base has no algebraic real point, even though the
owner-named union need not be transitive across its named owner predicates. -/
theorem owner_union_acl_empty [DecidableEq M] [Infinite M]
    (cco : SemanticCCO.{0,v,0,w} S) {E : ColourEq S ()} (hE : UniqueDirection S E)
    (normalized : NoFiniteExactKernel S) (B : Finset (Owner S E))
    (hB : OwnerInvariant S H (packet_thin S H normalized) E B) :
    algebraicClosure (NamedAut S E B) (∅ : Finset (OwnerUnion S E B)) = ∅ := by
  rw [owner_union_acl S H cco hE normalized B hB ∅]
  have he : realBase S E B (∅ : Finset (OwnerUnion S E B)) = ∅ := Finset.image_empty _
  rw [he]
  ext x
  constructor
  · rintro ⟨a,ha,_⟩
    exact Finset.notMem_empty a ha
  · intro hx
    exact False.elim hx

/-- Empty B is treated on the literal empty carrier, without invoking any
nonempty AtomicSource interface for the induced union. -/
theorem owner_union_empty [DecidableEq M] (E : ColourEq S ())
    (A : Finset (OwnerUnion S E ∅)) :
    A = ∅ ∧ algebraicClosure (NamedAut S E ∅) A = ∅ ∧
      packetHull S H (realBase S E ∅ A) = ∅ := by
  have hx : ∀ x : OwnerUnion S E ∅, False := fun x => Finset.notMem_empty _ x.property
  have hA : A = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun x _ => hx x)
  refine ⟨hA,?_,?_⟩
  · ext x
    exact False.elim (hx x)
  · rw [hA]
    have he : realBase S E ∅ (∅ : Finset (OwnerUnion S E ∅)) = ∅ := Finset.image_empty _
    rw [he]
    ext x
    constructor
    · rintro ⟨a,ha,_⟩
      exact Finset.notMem_empty a ha
    · intro hx
      exact False.elim hx

/-- A finite full-packet union in N_B is absolutely closed there. -/
theorem finite_packet_union_closed [DecidableEq M] [Infinite M]
    (cco : SemanticCCO.{0,v,0,w} S) {E : ColourEq S ()} (hE : UniqueDirection S E)
    (normalized : NoFiniteExactKernel S) (B : Finset (Owner S E))
    (hB : OwnerInvariant S H (packet_thin S H normalized) E B)
    (C : Finset (OwnerUnion S E B))
    (hC : ∀ a ∈ C, ∀ x : OwnerUnion S E B, packet S H a.val x.val → x ∈ C) :
    algebraicClosure (NamedAut S E B) C = (C : Set (OwnerUnion S E B)) := by
  rw [owner_union_acl S H cco hE normalized B hB C]
  ext x
  constructor
  · intro hx
    obtain ⟨a,ha,hax⟩ := (mem_packetHull_realBase S H E B C x.val).mp hx
    exact hC a ha x hax
  · intro hx
    exact (mem_packetHull_realBase S H E B C x.val).mpr ⟨x,hx,(packet S H).val.refl x.val⟩

end CCO.DirectOwnerClosure
