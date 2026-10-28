import CCO.FinitePackets.Geometry.Lattice
import CCO.FinitePackets.Geometry.RelativeIndices

/-! The ACTUAL class projection across any invariant E. Its kernel is
D = K meet (E join J), and its fibres are actual relative classes. These
maps do not invoke a minimal cut, exactness, CCO or a quotient source. -/
universe u v w t
namespace CCO.FinitePackets.Geometry
open CCO.ParityHasse.Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]
variable (H : HomogeneousSource S G)

/-- Send each real J-class to its containing (E join J)-class. -/
def crossingProjection (E J K : ColourEq S i) (x : X i) :
    RelativeClass J.val K.val x →
      RelativeClass (ColourEq.join S H E J).val (ColourEq.join S H E K).val x := by
  letI := ColourEq.lattice S H (i := i)
  exact Quotient.map (fun y =>
    (⟨y.val,(show K ≤ E ⊔ K from le_sup_right) y.property⟩ : {y // (E ⊔ K) x y}))
    (fun _ _ h => (show J ≤ E ⊔ J from le_sup_right) h)

theorem crossingProjection_surjective (E J K : ColourEq S i) (x : X i) :
    Function.Surjective (crossingProjection S H E J K x) := by
  letI := ColourEq.lattice S H (i := i)
  intro q
  refine Quotient.inductionOn q ?_
  intro y
  have hpath : ColourEq.join S H K E x y.val := by
    change (K.val ⊔ E.val) x y.val
    rw [sup_comm]
    exact y.property
  obtain ⟨z,hK,hE⟩ := (actual_join_iff S H K E x y.val).mp hpath
  refine ⟨Quotient.mk _ (⟨z,hK⟩ : {z // K x z}),?_⟩
  apply Quotient.sound
  exact (show E ≤ E ⊔ J from le_sup_left) hE

/-- On representatives in one K-class, equality of projected classes is
exactly the genuine represented kernel D. -/
theorem crossingProjection_kernel_representatives (E J K : ColourEq S i) (x : X i)
    (y z : {y // K x y}) :
    crossingProjection S H E J K x (Quotient.mk _ y) =
      crossingProjection S H E J K x (Quotient.mk _ z) ↔
        (K ⊓ ColourEq.join S H E J) y.val z.val := by
  constructor
  · intro h
    change Quotient.mk (Setoid.comap (fun p : {p // ColourEq.join S H E K x p} => p.val)
      (ColourEq.join S H E J).val) _ = Quotient.mk _ _ at h
    have he := Quotient.exact h
    change ColourEq.join S H E J y.val z.val at he
    exact ⟨K.val.trans (K.val.symm y.property) z.property,he⟩
  · intro h
    exact Quotient.sound h.2

def crossingKernelClassMap (E J K : ColourEq S i) (x : X i) :
    RelativeClass (K ⊓ ColourEq.join S H E J).val K.val x →
      RelativeClass (ColourEq.join S H E J).val (ColourEq.join S H E K).val x := by
  letI := ColourEq.lattice S H (i := i)
  exact Quotient.map (fun y =>
    (⟨y.val,(show K ≤ E ⊔ K from le_sup_right) y.property⟩ : {y // (E ⊔ K) x y}))
    (fun _ _ h => h.2)

theorem crossingKernelClassMap_injective (E J K : ColourEq S i) (x : X i) :
    Function.Injective (crossingKernelClassMap S H E J K x) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro y z h
  change crossingProjection S H E J K x (Quotient.mk _ y) =
    crossingProjection S H E J K x (Quotient.mk _ z) at h
  exact Quotient.sound ((crossingProjection_kernel_representatives S H E J K x y z).mp h)

theorem crossingKernelClassMap_surjective (E J K : ColourEq S i) (x : X i) :
    Function.Surjective (crossingKernelClassMap S H E J K x) := by
  intro q
  obtain ⟨p,hp⟩ := crossingProjection_surjective S H E J K x q
  revert hp
  refine Quotient.inductionOn p ?_
  intro y hy
  exact ⟨Quotient.mk _ y,hy⟩

noncomputable def crossingKernelClassEquiv (E J K : ColourEq S i) (x : X i) :
    RelativeClass (K ⊓ ColourEq.join S H E J).val K.val x ≃
      RelativeClass (ColourEq.join S H E J).val (ColourEq.join S H E K).val x :=
  Equiv.ofBijective (crossingKernelClassMap S H E J K x)
    ⟨crossingKernelClassMap_injective S H E J K x,
      crossingKernelClassMap_surjective S H E J K x⟩

theorem crossing_inner_le (E J K : ColourEq S i) (hJK : J ≤ K) :
    J ≤ K ⊓ ColourEq.join S H E J := by
  letI := ColourEq.lattice S H (i := i)
  exact le_inf hJK le_sup_right

theorem crossingProjection_factor (E J K : ColourEq S i) (hJK : J ≤ K) (x : X i)
    (q : RelativeClass J.val K.val x) :
    crossingKernelClassEquiv S H E J K x
      (relativeCoarsening J.val (K ⊓ ColourEq.join S H E J).val K.val
        (crossing_inner_le S H E J K hJK) x q) = crossingProjection S H E J K x q := by
  refine Quotient.inductionOn q ?_
  intro y
  rfl

/-- The kernel description on arbitrary actual J-classes, not merely
an equality of numerical indices or an abstract interval isomorphism. -/
theorem crossingProjection_kernel (E J K : ColourEq S i) (hJK : J ≤ K) (x : X i)
    (p q : RelativeClass J.val K.val x) :
    crossingProjection S H E J K x p = crossingProjection S H E J K x q ↔
      relativeCoarsening J.val (K ⊓ ColourEq.join S H E J).val K.val
        (crossing_inner_le S H E J K hJK) x p =
      relativeCoarsening J.val (K ⊓ ColourEq.join S H E J).val K.val
        (crossing_inner_le S H E J K hJK) x q := by
  rw [← crossingProjection_factor S H E J K hJK x p,
    ← crossingProjection_factor S H E J K hJK x q]
  exact (crossingKernelClassEquiv S H E J K x).injective.eq_iff

/-- The actual fibre over the projected real class of y is the quotient of
the D-class of y by J. The map uses the SAME real representatives. -/
noncomputable def crossingFibreEquiv (E J K : ColourEq S i) (hJK : J ≤ K) (x : X i)
    (y : {y // K x y}) :
    RelativeClass J.val (K ⊓ ColourEq.join S H E J).val y.val ≃
      {q : RelativeClass J.val K.val x //
        crossingProjection S H E J K x q =
          crossingProjection S H E J K x (Quotient.mk _ y)} :=
  (relativeFibreEquiv J.val (K ⊓ ColourEq.join S H E J).val K.val
    (crossing_inner_le S H E J K hJK) inf_le_left x y).trans
      (Equiv.subtypeEquivRight (fun q =>
        (crossingProjection_kernel S H E J K hJK x q (Quotient.mk _ y)).symm))

theorem crossing_target_finite (E J K : ColourEq S i) (x : X i)
    [Finite (RelativeClass J.val K.val x)] :
    Finite (RelativeClass (ColourEq.join S H E J).val (ColourEq.join S H E K).val x) :=
  Finite.of_surjective _ (crossingProjection_surjective S H E J K x)

theorem crossing_fibre_finite_card (E J K : ColourEq S i) (hJK : J ≤ K) (x : X i)
    [Finite (RelativeClass J.val K.val x)] (y : {y // K x y}) :
    Finite {q : RelativeClass J.val K.val x //
      crossingProjection S H E J K x q =
        crossingProjection S H E J K x (Quotient.mk _ y)} ∧
    Nat.card {q : RelativeClass J.val K.val x //
      crossingProjection S H E J K x q =
        crossingProjection S H E J K x (Quotient.mk _ y)} =
      relativeIndex J.val (K ⊓ ColourEq.join S H E J).val y.val := by
  letI : Finite (RelativeClass J.val (K ⊓ ColourEq.join S H E J).val y.val) :=
    Finite.of_equiv _ (crossingFibreEquiv S H E J K hJK x y).symm
  exact ⟨inferInstance,(Nat.card_congr (crossingFibreEquiv S H E J K hJK x y)).symm⟩

/-- Every actual projection fibre has the claimed UNIFORM meet index.
The numerical rerouting uses the actual transposition bijections; original
group motion then changes its real anchor from y back to x. -/
theorem crossing_fibre_meet_card (E J K : ColourEq S i) (hJK : J ≤ K)
    (hfin : FiniteIndex S J K) (x : X i) (y : {y // K x y}) :
    Finite {q : RelativeClass J.val K.val x //
      crossingProjection S H E J K x q =
        crossingProjection S H E J K x (Quotient.mk _ y)} ∧
    Nat.card {q : RelativeClass J.val K.val x //
      crossingProjection S H E J K x q =
        crossingProjection S H E J K x (Quotient.mk _ y)} =
      relativeIndex (E ⊓ J).val (E ⊓ K).val x := by
  letI := hfin x
  letI := finiteIndex_restrict S E J K hfin x
  have hf := crossing_fibre_finite_card S H E J K hJK x y
  exact ⟨hf.1,hf.2.trans ((relativeIndex_meet_reroute S H E J K hJK y.val).trans
    (relativeIndex_uniform S H (E ⊓ J) (E ⊓ K) y.val x))⟩

/-- C17 as a single actual source consumer: the genuine projection is onto,
BOTH factors are finite and positive, and the actual finite index factors.
No minimal cut, countability, exact quotient or CCO premise occurs. -/
theorem actual_crossing_projection_and_index (E J K : ColourEq S i) (hJK : J ≤ K)
    (hfin : FiniteIndex S J K) (x : X i) :
    Function.Surjective (crossingProjection S H E J K x) ∧
      Finite (RelativeClass (ColourEq.join S H E J).val (ColourEq.join S H E K).val x) ∧
      Finite (RelativeClass (E ⊓ J).val (E ⊓ K).val x) ∧
      0 < relativeIndex (ColourEq.join S H E J).val (ColourEq.join S H E K).val x ∧
      0 < relativeIndex (E ⊓ J).val (E ⊓ K).val x ∧
      relativeIndex J.val K.val x =
        relativeIndex (ColourEq.join S H E J).val (ColourEq.join S H E K).val x *
          relativeIndex (E ⊓ J).val (E ⊓ K).val x := by
  letI := hfin x
  letI := finiteIndex_join_crossing S H E J K hJK hfin x
  letI := finiteIndex_restrict S E J K hfin x
  exact ⟨crossingProjection_surjective S H E J K x,inferInstance,inferInstance,
    Nat.card_pos,Nat.card_pos,relativeIndex_factorization S H E J K hJK hfin x⟩

end CCO.FinitePackets.Geometry
