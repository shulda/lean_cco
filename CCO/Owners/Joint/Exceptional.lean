import CCO.Owners.Joint.Matching

/-! C23–26: synchronize a GIVEN exceptional coordinate map. The target is
the literal compatible coordinate target; no identification with acl,
safe palette, MI provider or rank theorem is asserted. -/
namespace CCO.Owners.Joint
variable {I Γ B : Type*} {K R Bi Di : I → Type*}
variable [Group Γ] [∀ i, Group (K i)] [∀ i, Group (R i)]
variable [MulAction Γ B] [∀ i, MulAction (R i) (Bi i)] [∀ i, MulAction (K i) (Di i)]
variable (d : OwnerDiagram I B Bi) (full : FullOwners d)
variable (π : ∀ i, Di i → Bi i)
variable (own : ∀ i, K i →* R i) (rho : ∀ i, Γ →* R i)
variable (eqπ : ∀ i g x, π i (g • x) = own i g • π i x)
variable (eqβ : ∀ i g b, d.beta i (g • b) = rho i g • d.beta i b)
variable (lift : ∀ i, GroupActions.PrescribedLift (own i) (π i))

include eqπ eqβ lift

/-- Complete a matching tuple while retaining its exceptional coordinate
as exactly the given element, rather than choosing a replacement lift. -/
theorem retain_exceptional (e : I) (x y : Carrier d Di π) (g : Γ)
    (hg : g • owner d Di π full x = owner d Di π full y)
    (a : K e) (ha : own e a = rho e g) (haxy : a • x.val e = y.val e) :
    letI := witnessAction d full π own rho eqπ eqβ
    ∃ k : Matching own rho, k.val.1 = g ∧ k.val.2 e = a ∧ k • x = y := by
  classical
  letI := witnessAction d full π own rho eqπ eqβ
  have hi : ∀ i, rho i g • π i (x.val i) = π i (y.val i) := by
    intro i
    rw [← beta_owner d Di π full x i, ← eqβ, hg, beta_owner]
  choose b hb hmove using (fun i => lift i (x.val i) (y.val i) (rho i g) (hi i))
  let c : ∀ i, K i := Function.update b e a
  have hc : ∀ i, own i (c i) = rho i g := by
    intro i
    by_cases he : i = e
    · subst i; simpa only [c, Function.update_self] using ha
    · simpa only [c, Function.update_of_ne he] using hb i
  refine ⟨⟨(g,c),hc⟩,rfl,by simp only [c, Function.update_self],?_⟩
  apply Subtype.ext
  funext i
  change c i • x.val i = y.val i
  by_cases he : i = e
  · subst i; simpa only [c, Function.update_self] using haxy
  · simpa only [c, Function.update_of_ne he] using hmove i

/-- Conditional exceptional-root support, with all quantified input data
visible. One ORIGINAL input point is chosen first, then its whole owner
is synchronized with the given exceptional owner action. -/
theorem exceptional_target (e : I)
    (A0 Z : Set (Carrier d Di π)) (z : Carrier d Di π) (hz : z ∈ Z)
    (target : ∀ i, Set (Di i)) (F : ∀ i, Setoid (Di i))
    (invariantF : ∀ i (k : K i) x y, F i x y → F i (k • x) (k • y))
    (closedTarget : ∀ i (a : Carrier d Di π), a ∈ A0 →
      ∀ y, F i (a.val i) y → y ∈ target i)
    (clique : ∀ i, i ≠ e → ∀ w ∈ Z, F i (z.val i) (w.val i))
    (exceptional : K e)
    (exceptionalZ : ∀ w ∈ Z, exceptional • w.val e ∈ target e)
    (exceptionalRoot : exceptional • z.val e ∈ (fun w : Carrier d Di π => w.val e) '' A0)
    (ownerM3 : Function.Surjective (rho e) ∧
      GroupActions.FibreTransitive (rho e) (d.beta e)) :
    letI := witnessAction d full π own rho eqπ eqβ
    ∃ k : Matching own rho, k.val.2 e = exceptional ∧ k • z ∈ A0 ∧
      ∀ w ∈ Z, ∀ i, (k • w).val i ∈ target i := by
  letI := witnessAction d full π own rho eqπ eqβ
  obtain ⟨a,ha,hae⟩ := exceptionalRoot
  have compat : own e exceptional • d.beta e (owner d Di π full z) =
      d.beta e (owner d Di π full a) := by
    rw [beta_owner, ← eqπ, ← hae, beta_owner]
  letI : Nonempty B := ⟨owner d Di π full z⟩
  obtain ⟨g,hg,hga⟩ :=
    (GroupActions.prescribed_action_point_lifting (rho e) (d.beta e)
      (d.beta_surjective e) (eqβ e)).mp ownerM3
      (owner d Di π full z) (owner d Di π full a) (own e exceptional) compat
  obtain ⟨k,_,hke,hka⟩ := retain_exceptional d full π own rho eqπ eqβ lift e z a g hga
    exceptional hg.symm hae.symm
  refine ⟨k,hke,by simpa only [hka] using ha,?_⟩
  intro w hw i
  classical
  by_cases he : i = e
  · subst i
    change k.val.2 e • w.val e ∈ target e
    rw [hke]
    exact exceptionalZ w hw
  · apply closedTarget i a ha
    change F i (a.val i) (k.val.2 i • w.val i)
    have h := invariantF i (k.val.2 i) (z.val i) (w.val i) (clique i he w hw)
    have hroot : k.val.2 i • z.val i = a.val i := congrFun (congrArg Subtype.val hka) i
    simpa only [hroot] using h

end CCO.Owners.Joint
