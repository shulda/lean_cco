import CCO.DirectOwnerClosure.OwnerUnionClosure

/-! The single frozen source export and a downstream finite closed-target
consumer. The three closure equalities have separately scoped hypotheses;
countable ancillary homogeneity is not imported or used here. -/
universe v w t
namespace CCO.DirectOwnerClosure
open ParityHasse.Original RealHull.Geometry FinitePackets.Geometry
open FinitePackets.Normalization
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

/-- C25 / lem:consolidated-unary-closure. Normalization and owner invariance
occur ONLY under the third conjunct's quantifiers. All closures use FULL
automorphism groups and the original greatest finite packet may be nonexact. -/
theorem consolidated_unary_closure [DecidableEq M] [Infinite M]
    (cco : SemanticCCO.{0,v,0,w} S) {E : ColourEq S ()} (hE : UniqueDirection S E) :
    (∀ A : Finset M, algebraicClosure (FullAut S) A = packetHull S H A) ∧
    (∀ (B : Finset (Owner S E)) (A : Finset M),
      ownerClosure S E B A = packetHull S H A) ∧
    (∀ (normalized : NoFiniteExactKernel S) (B : Finset (Owner S E))
      (_hB : OwnerInvariant S H (packet_thin S H normalized) E B)
      (A : Finset (OwnerUnion S E B)),
      (fun x : OwnerUnion S E B => x.val) '' algebraicClosure (NamedAut S E B) A =
        packetHull S H (realBase S E B A)) := by
  exact ⟨direct_real_acl S H cco hE,named_owner_acl S H cco hE,
    owner_union_real_acl S H cco hE⟩

/-- A genuine receiving use: one finite full-packet target is simultaneously
closed over real parameters, over the individually named imaginary owners,
and in the FULL induced union. Every total thin function stays in the same
target; its ambient restriction-image orbits remain the actual named orbits.
No thin function is asserted to preserve each named owner predicate. -/
theorem closed_target_in_three_actions [DecidableEq M] [Infinite M]
    (cco : SemanticCCO.{0,v,0,w} S) {E : ColourEq S ()} (hE : UniqueDirection S E)
    (normalized : NoFiniteExactKernel S) (B : Finset (Owner S E))
    (hB : OwnerInvariant S H (packet_thin S H normalized) E B)
    (C : Finset (OwnerUnion S E B))
    (hC : ∀ a ∈ C, ∀ x : OwnerUnion S E B, packet S H a.val x.val → x ∈ C) :
    algebraicClosure (FullAut S) (realBase S E B C) = (realBase S E B C : Set M) ∧
    ownerClosure S E B (realBase S E B C) = (realBase S E B C : Set M) ∧
    algebraicClosure (NamedAut S E B) C = (C : Set (OwnerUnion S E B)) ∧
    (∀ (e : PacketTranslations S H) a, a ∈ C →
      thinFunction S H (packet_thin S H normalized) E B hB e a ∈ C) ∧
    (∀ x : OwnerUnion S E B,
      Subtype.val '' imageOrbit S E B (realBase S E B C) x =
        ownerOrbit S E B (realBase S E B C) x.val) := by
  obtain ⟨hreal,howner,hunion⟩ := consolidated_unary_closure S H cco hE
  have htarget : packetHull S H (realBase S E B C) = (realBase S E B C : Set M) := by
    ext x
    constructor
    · intro hx
      have hxB := packetHull_realBase_subset_union S H (packet_thin S H normalized) E B hB C hx
      obtain ⟨a,ha,hax⟩ := (mem_packetHull_realBase S H E B C x).mp hx
      have hxin : (⟨x,hxB⟩ : OwnerUnion S E B) ∈ C := hC a ha ⟨x,hxB⟩ hax
      exact Finset.mem_image.mpr ⟨⟨x,hxB⟩,hxin,rfl⟩
    · intro hx
      exact ⟨x,hx,(packet S H).val.refl x⟩
  refine ⟨(hreal _).trans htarget,(howner B _).trans htarget,?_,?_,?_⟩
  · have hreadout := hunion normalized B hB C
    ext x
    constructor
    · intro hx
      have hxreal : x.val ∈ packetHull S H (realBase S E B C) := by
        rw [← hreadout]
        exact ⟨x,hx,rfl⟩
      obtain ⟨a,ha,hax⟩ := (mem_packetHull_realBase S H E B C x.val).mp hxreal
      exact hC a ha x hax
    · intro hx
      exact packet_target_algebraic S H (packet_thin S H normalized) E B hB C
        ⟨x,hx,(packet S H).val.refl x.val⟩
  · intro e a ha
    exact hC a ha _ (translation_in_packet S (packet S H) G e a.val)
  · intro x
    exact imageOrbit_eq_ambient S E B (realBase S E B C) x

end CCO.DirectOwnerClosure
