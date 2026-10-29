import CCO.FiniteLift.Mixed
import CCO.FiniteLift.Closure

/-! C21: one actual three-sort finite tuple, including ALL K-classes
and ALL complete H-owners. The nine pair types are verified before
invoking joint exact homogeneity. No owner onto/kernel premise occurs. -/

universe v w t
namespace CCO.FiniteLift
open RawExact Owners.Product Owners.Provider OwnerCover
variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A] [Countable A]
variable (HS : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (K H : ExactKernel S G)

private def Family : Unit ⊕ Bool → Type v
  | .inl _ => A
  | .inr false => K.Q
  | .inr true => H.Q

private instance familyAction (s : Unit ⊕ Bool) : MulAction G (Family S K H s) := by
  cases s with
  | inl _ => dsimp [Family]; infer_instance
  | inr b => cases b <;> dsimp [Family] <;> infer_instance

private def projection : ∀ s, A → Family S K H s
  | .inl _ => id
  | .inr false => K.proj
  | .inr true => H.proj

/-- ENTIRE prescribed finite actions with a compatible real sparse map
lift by ONE original G-element. Coincident actual quotients satisfy the
same pair checks, which force agreement rather than independent copies. -/
theorem three_sort_ambient (finiteK : K.FiniteClasses)
    (Dbar : Set K.Q) (Bbar : Set (J S HS cco K H).Q)
    (finiteDbar : Dbar.Finite) (finiteBbar : Bbar.Finite)
    (imageD : rK S HS cco K H '' Dbar = Bbar)
    (p : OrbitalPartial (G := G) (Subtype.val : fullPreimage K.proj Dbar → A))
    (β : OrbitalAut G K.Q (Subtype.val : Dbar → K.Q))
    (γ : OrbitalAut G H.Q (Subtype.val : ((rH S HS cco K H) ⁻¹' Bbar) → H.Q))
    (matching : ownerAction S HS cco K H Bbar γ =
      (quotientOwner S HS cco K H Dbar Bbar imageD).action β)
    (compK : ∀ x : p.domain,
      K.proj (p.map x).val = (β.val (fullProjection K.proj Dbar x.val)).val)
    (compH : ∀ x : p.domain,
      H.proj (p.map x).val =
        (γ.val (realOwnerProjection S HS cco K H Dbar Bbar imageD x.val)).val) :
    ∃ g : G,
      (∀ x : p.domain, g • x.val.val = (p.map x).val) ∧
      (∀ q : Dbar, g • q.val = (β.val q).val) ∧
      (∀ b : ((rH S HS cco K H) ⁻¹' Bbar), g • b.val = (γ.val b).val) := by
  classical
  letI : Finite Dbar := finiteDbar.to_subtype
  letI : Finite ((rH S HS cco K H) ⁻¹' Bbar) :=
    (complete_packet_finite S HS cco K H finiteK Bbar finiteBbar).to_subtype
  letI : Finite (fullPreimage K.proj Dbar) :=
    (K.fullPreimage_finite finiteK Dbar finiteDbar).to_subtype
  let δ := (quotientOwner S HS cco K H Dbar Bbar imageD).action β
  have βcoarse (q : Dbar) :
      rK S HS cco K H (β.val q).val =
        (δ.val (quotientOwnerProjection S HS cco K H Dbar Bbar imageD q)).val := by
    exact (congrArg Subtype.val
      ((quotientOwner S HS cco K H Dbar Bbar imageD).action_projection β q)).symm
  have γcoarse (b : ((rH S HS cco K H) ⁻¹' Bbar)) :
      rH S HS cco K H (γ.val b).val =
        (δ.val (fullProjection (rH S HS cco K H) Bbar b)).val := by
    have hh := (fullOwnerQuotient S HS cco K H Bbar).action_projection γ b
    change (ownerAction S HS cco K H Bbar γ).val
      (fullProjection (rH S HS cco K H) Bbar b) =
        fullProjection (rH S HS cco K H) Bbar (γ.val b) at hh
    rw [matching] at hh
    exact (congrArg Subtype.val hh).symm
  have mixedK (x : p.domain) (q : Dbar) :
      GroupActions.orbital (G := G) x.val.val q.val (p.map x).val (β.val q).val := by
    apply (K.real_quotient_orbital HS _ _ _ _).mpr
    rw [compK]
    exact orbitalAut_pair β (fullProjection K.proj Dbar x.val) q
  have mixedH (x : p.domain) (b : ((rH S HS cco K H) ⁻¹' Bbar)) :
      GroupActions.orbital (G := G) x.val.val b.val (p.map x).val (γ.val b).val := by
    apply (H.real_quotient_orbital HS _ _ _ _).mpr
    rw [compH]
    exact orbitalAut_pair γ (realOwnerProjection S HS cco K H Dbar Bbar imageD x.val) b
  have mixedKH (q : Dbar) (b : ((rH S HS cco K H) ⁻¹' Bbar)) :
      GroupActions.orbital (G := G) q.val b.val (β.val q).val (γ.val b).val := by
    apply (mixed_orbital S HS cco K H _ _ _ _).mpr
    rw [βcoarse,γcoarse]
    exact orbitalAut_pair δ (quotientOwnerProjection S HS cco K H Dbar Bbar imageD q)
      (fullProjection (rH S HS cco K H) Bbar b)
  let π := projection S K H
  have ontoπ : ∀ s, Function.Surjective (π s) := by
    intro s
    cases s with
    | inl _ => exact Function.surjective_id
    | inr b => cases b; exact K.onto; exact H.onto
  have equivπ : ∀ s (g : G) a, π s (g • a) = g • π s a := by
    intro s g a
    cases s with
    | inl _ => rfl
    | inr b => cases b; exact K.proj_smul g a; exact H.proj_smul g a
  let E : ∀ _ : Unit ⊕ Bool, NonemptyExact S () ()
    | .inl _ => exactIdentityAtom S ()
    | .inr false => K.exact
    | .inr true => H.exact
  have hE : ∀ s, GroupActions.kernel (π s) = evaluate S (E s).words := by
    intro s
    cases s with
    | inl _ =>
      change GroupActions.kernel (id : A → A) = evaluate S (exactIdentityAtom S ()).words
      rw [exactIdentityAtom_relation S ()]; rfl
    | inr b => cases b; exact K.kernel; exact H.kernel
  let I := p.domain ⊕ (Dbar ⊕ ((rH S HS cco K H) ⁻¹' Bbar))
  let sort : I → Unit ⊕ Bool
    | .inl _ => .inl ()
    | .inr (.inl _) => .inr false
    | .inr (.inr _) => .inr true
  let src : ∀ i : I, Family S K H (sort i)
    | .inl x => x.val.val
    | .inr (.inl q) => q.val
    | .inr (.inr b) => b.val
  let dst : ∀ i : I, Family S K H (sort i)
    | .inl x => (p.map x).val
    | .inr (.inl q) => (β.val q).val
    | .inr (.inr b) => (γ.val b).val
  have hp : ∀ i j : I,
      GroupActions.orbital (G := G) (src i) (src j) (dst i) (dst j) := by
    intro i j
    cases i with
    | inl x =>
      cases j with
      | inl y => exact p.pair x y
      | inr j => cases j with
        | inl q => exact mixedK x q
        | inr b => exact mixedH x b
    | inr i =>
      cases j with
      | inl x =>
        cases i with
        | inl q => obtain ⟨g,hx,hq⟩ := mixedK x q; exact ⟨g,hq,hx⟩
        | inr b => obtain ⟨g,hx,hb⟩ := mixedH x b; exact ⟨g,hb,hx⟩
      | inr j =>
        cases i with
        | inl q =>
          cases j with
          | inl q' => exact orbitalAut_pair β q q'
          | inr b => exact mixedKH q b
        | inr b =>
          cases j with
          | inl q => obtain ⟨g,hq,hb⟩ := mixedKH q b; exact ⟨g,hb,hq⟩
          | inr b' => exact orbitalAut_pair γ b b'
  obtain ⟨g,hg⟩ := finite_quotient_tuple_lifting_of_CCO S HS cco
    (Family S K H) (fun _ => ()) π ontoπ equivπ E hE sort src dst hp
  exact ⟨g,fun x => hg (.inl x),fun q => hg (.inr (.inl q)),
    fun b => hg (.inr (.inr b))⟩

/-- Restrict the ONE ambient lift to the same finite full preimage.
Both entire finite quotient actions are retained exactly. -/
theorem three_sort_lift (finiteK : K.FiniteClasses)
    (Dbar : Set K.Q) (Bbar : Set (J S HS cco K H).Q)
    (finiteDbar : Dbar.Finite) (finiteBbar : Bbar.Finite)
    (imageD : rK S HS cco K H '' Dbar = Bbar)
    (p : OrbitalPartial (G := G) (Subtype.val : fullPreimage K.proj Dbar → A))
    (β : OrbitalAut G K.Q (Subtype.val : Dbar → K.Q))
    (γ : OrbitalAut G H.Q (Subtype.val : ((rH S HS cco K H) ⁻¹' Bbar) → H.Q))
    (matching : ownerAction S HS cco K H Bbar γ =
      (quotientOwner S HS cco K H Dbar Bbar imageD).action β)
    (compK : ∀ x : p.domain,
      K.proj (p.map x).val = (β.val (fullProjection K.proj Dbar x.val)).val)
    (compH : ∀ x : p.domain,
      H.proj (p.map x).val =
        (γ.val (realOwnerProjection S HS cco K H Dbar Bbar imageD x.val)).val) :
    ∃ α : OrbitalAut G A (Subtype.val : fullPreimage K.proj Dbar → A),
      p.Extends α ∧
      finiteAction K.proj K.onto K.proj_smul Dbar α = β ∧
      (realOwner S HS cco K H Dbar Bbar imageD).action α = γ := by
  classical
  obtain ⟨g,hp,hβ,hγ⟩ := three_sort_ambient S HS cco K H finiteK Dbar Bbar
    finiteDbar finiteBbar imageD p β γ matching compK compH
  letI : Finite (fullPreimage K.proj Dbar) :=
    (K.fullPreimage_finite finiteK Dbar finiteDbar).to_subtype
  have invariantD : ∀ x : fullPreimage K.proj Dbar,
      (ambientAut g).val x.val ∈ fullPreimage K.proj Dbar := by
    intro x
    change K.proj (g • x.val) ∈ Dbar
    rw [K.proj_smul]
    change g • (fullProjection K.proj Dbar x).val ∈ Dbar
    rw [hβ]
    exact (β.val (fullProjection K.proj Dbar x)).property
  let α : OrbitalAut G A (Subtype.val : fullPreimage K.proj Dbar → A) :=
    restrictAut (ambientAut g) (fullPreimage K.proj Dbar) invariantD
  refine ⟨α,?_,?_,?_⟩
  · intro x; exact Subtype.ext (hp x)
  · apply Subtype.ext
    apply Equiv.ext
    intro q
    obtain ⟨x,rfl⟩ := fullProjection_onto K.proj K.onto Dbar q
    rw [finiteAction_projection]
    apply Subtype.ext
    exact (K.proj_smul g x.val).trans (hβ (fullProjection K.proj Dbar x))
  · apply Subtype.ext
    apply Equiv.ext
    intro b
    obtain ⟨x,rfl⟩ := realOwnerProjection_onto S HS cco K H Dbar Bbar imageD b
    refine ((realOwner S HS cco K H Dbar Bbar imageD).action_projection α x).trans ?_
    apply Subtype.ext
    exact (H.proj_smul g x.val).trans
      (hγ (realOwnerProjection S HS cco K H Dbar Bbar imageD x))

end CCO.FiniteLift
