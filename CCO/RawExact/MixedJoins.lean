import CCO.RawSource

/-!
# Original one-sort symmetric RAW mixed-join algebra (B002 C16-C17)

These are actual binary relation equalities, including logical equality
atoms. Their algebra needs invariance, equivalence and a real pair-flip;
exact word-presentability is not needed. Partial-map compatibility and
the later ambient lifting theorem are separate obligations.
-/

universe u

namespace CCO.RawExact

open RawSymmetric

variable {A G : Type u} [Group G] [MulAction G A]

theorem raw_comp_assoc (P Q R : A → A → Prop) :
    compose (compose P Q) R = compose P (compose Q R) := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, ⟨w, hxw, hwy⟩, hyz⟩
    exact ⟨w, hxw, y, hwy, hyz⟩
  · rintro ⟨w, hxw, y, hwy, hyz⟩
    exact ⟨y, ⟨w, hxw, hwy⟩, hyz⟩

theorem equiv_comp_self (E : A → A → Prop)
    (hE : EquivRel E) :
    compose E E = E := by
  funext x z
  apply propext
  constructor
  · rintro ⟨y, hxy, hyz⟩
    exact hE.trans x y z hxy hyz
  · intro hxz
    exact ⟨z, hxz, hE.refl z⟩

/-- C16 RAW algebra: if J is the join E;H, then
E;R;H = J;R;J = J;R = R;J, including diagonal RAW input R.
The complete one-sort symmetric source supplies the pair-flip below. -/
theorem mixed_join_reduction
    (E H R : A → A → Prop)
    (hE : EquivRel E) (hH : EquivRel H)
    (invE : ∀ (g : G) x y, E x y → E (g • x) (g • y))
    (invH : ∀ (g : G) x y, H x y → H (g • x) (g • y))
    (invR : ∀ (g : G) x y, R x y → R (g • x) (g • y))
    (hflip : PairFlip (G := G) (A := A)) :
    let J := compose E H
    compose (compose E R) H = compose (compose J R) J ∧
    compose (compose J R) J = compose J R ∧
    compose J R = compose R J := by
  let J := compose E H
  have hJE : EquivRel J :=
    (comp_equivalences_is_join E H hE hH invE invH hflip).1
  have invJ : ∀ (g : G) x y, J x y → J (g • x) (g • y) := by
    rintro g x y ⟨z, hxz, hzy⟩
    exact ⟨g • z, invE g x z hxz, invH g z y hzy⟩
  have commRH : compose R H = compose H R :=
    invariant_commute R H invR invH hflip
  have commRJ : compose R J = compose J R :=
    invariant_commute R J invR invJ hflip
  have hFirst : compose (compose E R) H = compose J R := by
    calc
      compose (compose E R) H = compose E (compose R H) :=
        raw_comp_assoc E R H
      _ = compose E (compose H R) := by rw [commRH]
      _ = compose (compose E H) R := (raw_comp_assoc E H R).symm
  have hSecond : compose (compose J R) J = compose J R := by
    calc
      compose (compose J R) J = compose J (compose R J) :=
        raw_comp_assoc J R J
      _ = compose J (compose J R) := by rw [commRJ]
      _ = compose (compose J J) R := (raw_comp_assoc J J R).symm
      _ = compose J R := by rw [equiv_comp_self J hJE]
  exact ⟨hFirst.trans hSecond.symm, hSecond, commRJ.symm⟩

/-- C17 RAW algebra: for J subset K, J;R;K=K;R;K=R;K.
No exactness or choice of quotient lifts is used here. -/
theorem nested_mixed_reduction
    (J K R : A → A → Prop)
    (hJ : EquivRel J) (hK : EquivRel K)
    (hJK : ∀ x y, J x y → K x y)
    (invK : ∀ (g : G) x y, K x y → K (g • x) (g • y))
    (invR : ∀ (g : G) x y, R x y → R (g • x) (g • y))
    (hflip : PairFlip (G := G) (A := A)) :
    compose (compose J R) K = compose (compose K R) K ∧
    compose (compose K R) K = compose R K := by
  have hJKcomp : compose J K = K := by
    funext x y
    apply propext
    constructor
    · rintro ⟨z, hxz, hzy⟩
      exact hK.trans x z y (hJK x z hxz) hzy
    · intro hxy
      exact ⟨x, hJ.refl x, hxy⟩
  have commRK : compose R K = compose K R :=
    invariant_commute R K invR invK hflip
  have hSat : compose (compose K R) K = compose R K := by
    calc
      compose (compose K R) K = compose K (compose R K) :=
        raw_comp_assoc K R K
      _ = compose K (compose K R) := by rw [commRK]
      _ = compose (compose K K) R := (raw_comp_assoc K K R).symm
      _ = compose K R := by rw [equiv_comp_self K hK]
      _ = compose R K := commRK.symm
  have hJKR : compose (compose J R) K = compose R K := by
    calc
      compose (compose J R) K = compose J (compose R K) :=
        raw_comp_assoc J R K
      _ = compose J (compose K R) := by rw [commRK]
      _ = compose (compose J K) R := (raw_comp_assoc J K R).symm
      _ = compose K R := by rw [hJKcomp]
      _ = compose R K := commRK.symm
  exact ⟨hJKR.trans hSat.symm, hSat⟩

end CCO.RawExact

universe v w

namespace CCO.RawExact

section ActualSource

variable {ι : Type v} {X : ι → Type w}
variable (S : AtomicSource ι X)
variable {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]

/-- Actual-source C16 algebra, not merely an arbitrary pair-flip provider.
The raw optional colour may be the real same-sort diagonal. -/
theorem actual_mixed_join_of_homogeneous
    (H : HomogeneousSource S G) {i : ι}
    (E K : X i → X i → Prop)
    (hE : RawSymmetric.EquivRel E)
    (hK : RawSymmetric.EquivRel K)
    (invE : ∀ (g : G) x y, E x y → E (g • x) (g • y))
    (invK : ∀ (g : G) x y, K x y → K (g • x) (g • y))
    (a : Option (S.Atom i i)) :
    let J := RawSymmetric.compose E K
    RawSymmetric.compose (RawSymmetric.compose E (S.rawAtomRel a)) K =
      RawSymmetric.compose (RawSymmetric.compose J (S.rawAtomRel a)) J ∧
    RawSymmetric.compose (RawSymmetric.compose J (S.rawAtomRel a)) J =
      RawSymmetric.compose J (S.rawAtomRel a) ∧
    RawSymmetric.compose J (S.rawAtomRel a) =
      RawSymmetric.compose (S.rawAtomRel a) J := by
  have hAtom : ∀ (g : G) x y,
      S.rawAtomRel a x y → S.rawAtomRel a (g • x) (g • y) :=
    S.rawAtomRel_invariant a (S.colourInvariant_of_homogeneous H)
  exact mixed_join_reduction E K (S.rawAtomRel a)
    hE hK invE invK hAtom (S.pair_flip_of_homogeneous H)

/-- Actual-source C17 algebra. Its hypothesis J≤K is explicitly
retained and includes the original identity quotient. -/
theorem actual_nested_mixed_of_homogeneous
    (H : HomogeneousSource S G) {i : ι}
    (J K : X i → X i → Prop)
    (hJ : RawSymmetric.EquivRel J)
    (hK : RawSymmetric.EquivRel K)
    (hJK : ∀ x y, J x y → K x y)
    (invK : ∀ (g : G) x y, K x y → K (g • x) (g • y))
    (a : Option (S.Atom i i)) :
    RawSymmetric.compose (RawSymmetric.compose J (S.rawAtomRel a)) K =
      RawSymmetric.compose (RawSymmetric.compose K (S.rawAtomRel a)) K ∧
    RawSymmetric.compose (RawSymmetric.compose K (S.rawAtomRel a)) K =
      RawSymmetric.compose (S.rawAtomRel a) K := by
  have hAtom : ∀ (g : G) x y,
      S.rawAtomRel a x y → S.rawAtomRel a (g • x) (g • y) :=
    S.rawAtomRel_invariant a (S.colourInvariant_of_homogeneous H)
  exact nested_mixed_reduction J K (S.rawAtomRel a)
    hJ hK hJK invK hAtom (S.pair_flip_of_homogeneous H)

/-- A genuine source-level consumer testing C17 at the logical identity
quotient, for every optional original atom, including the real diagonal. -/
theorem actual_identity_nested_of_homogeneous
    (H : HomogeneousSource S G) {i : ι}
    (K : X i → X i → Prop)
    (hK : RawSymmetric.EquivRel K)
    (invK : ∀ (g : G) x y, K x y → K (g • x) (g • y))
    (a : Option (S.Atom i i)) :
    RawSymmetric.compose
      (RawSymmetric.compose (fun x y : X i => x = y) (S.rawAtomRel a)) K =
      RawSymmetric.compose (S.rawAtomRel a) K := by
  have hId : RawSymmetric.EquivRel (fun x y : X i => x = y) :=
    ⟨(fun _ => rfl), (fun _ _ h => h.symm),
     (fun _ _ _ hxy hyz => hxy.trans hyz)⟩
  have hIdK : ∀ x y : X i, x = y → K x y := by
    rintro x y rfl
    exact hK.refl x
  have hNested := S.actual_nested_mixed_of_homogeneous H
    (fun x y : X i => x = y) K hId hK hIdK invK a
  exact hNested.1.trans hNested.2

end ActualSource
end CCO.RawExact
