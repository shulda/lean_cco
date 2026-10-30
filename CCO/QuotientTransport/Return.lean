import CCO.QuotientTransport.Composition

/-! Every cut of one actual typed closed word is labelled by ONE original
quotient. The recursive run below composes the actual consecutive quotient
bijections, and returns literally to that original quotient. -/
universe u v w
namespace CCO.QuotientTransport
variable {G : Type u} [Group G] {I : Type w} {X : I → Type v}
variable [∀ i, MulAction G (X i)]

structure Letter (G : Type u) [Group G] (X : I → Type v)
    [∀ i, MulAction G (X i)] (i j : I) where
  relation : TRel X i j
  invariant : Invariant (G := G) relation
  nonempty : ∃ x y, relation x y

abbrev Word (G : Type u) [Group G] (X : I → Type v) [∀ i, MulAction G (X i)] :=
  TypedWord (Letter G X)

namespace Word
abbrev eval {i j : I} (p : Word G X i j) : TRel X i j := TypedWord.eval Letter.relation p

variable (trans : ∀ i, ∀ x y : X i, ∃ g : G, g • x = y)

theorem serial_coserial (trans : ∀ i, ∀ x y : X i, ∃ g : G, g • x = y) {i j : I} (p : Word G X i j) : Serial p.eval ∧ Coserial p.eval := by
  induction p with
  | nil i => exact ⟨fun x => ⟨x,rfl⟩,fun x => ⟨x,rfl⟩⟩
  | @cons i j k P tail ih =>
    obtain ⟨hp,hp'⟩ := serial_coserial_of_invariant P.relation P.invariant P.nonempty (trans i) (trans j)
    constructor
    · intro x
      obtain ⟨y,hy⟩ := hp x
      obtain ⟨z,hz⟩ := ih.1 y
      exact ⟨z,y,hy,hz⟩
    · intro z
      obtain ⟨y,hy⟩ := ih.2 z
      obtain ⟨x,hx⟩ := hp' y
      exact ⟨x,y,hx,hy⟩

theorem invariant {i j : I} (p : Word G X i j) : Invariant (G := G) p.eval := by
  induction p with
  | nil i => intro g x y h; exact congrArg (g • ·) h
  | cons P tail ih =>
    rintro g x z ⟨y,hxy,hyz⟩
    exact ⟨g • y,P.invariant g x y hxy,ih g y z hyz⟩

def extend {a i j : I} (p : Word G X a i) (P : Letter G X i j) : Word G X a j :=
  p.append (.cons P (.nil j))
theorem eval_extend {a i j : I} (p : Word G X a i) (P : Letter G X i j) :
    (p.extend P).eval = compose p.eval P.relation := by
  change TypedWord.eval Letter.relation (TypedWord.append p (.cons P (.nil j))) = _
  rw [TypedWord.eval_append]
  simp only [TypedWord.eval,TRel.comp_ident]
  rfl

end Word

namespace Return
variable {a : I} (E : InvEq G (X a))
variable (trans : ∀ i, ∀ x y : X i, ∃ g : G, g • x = y)

def Bound {i : I} (p : Word G X a i) (s : Word G X i a) : Prop :=
  ∀ x z, compose p.eval s.eval x z → E x z

/-- C16: ONE suffix witness gives the prefix kernel condition. -/
theorem prefixTransport (trans : ∀ i, ∀ x y : X i, ∃ g : G, g • x = y) {i : I} (p : Word G X a i) (s : Word G X i a) (h : Bound E p s) :
    Transport E p.eval where
  serial := (p.serial_coserial trans).1
  coserial := (p.serial_coserial trans).2
  invariant := p.invariant
  kernel x x' y hx hx' := by
    obtain ⟨z,hz⟩ := (s.serial_coserial trans).1 y
    exact E.val.trans (h x z ⟨y,hx,hz⟩) (E.val.symm (h x' z ⟨y,hx',hz⟩))

theorem next_bound {i j : I} (p : Word G X a i) (P : Letter G X i j)
    (s : Word G X j a) (h : Bound E p (.cons P s)) : Bound E (p.extend P) s := by
  rintro x z ⟨y,hxy,hyz⟩
  rw [Word.eval_extend] at hxy
  obtain ⟨b,hxb,hby⟩ := hxy
  exact h x z ⟨b,hxb,y,hby,hyz⟩

/-- C19: EVERY actual factor edge has equal canonical original labels. -/
theorem edge_label {i j : I} (p : Word G X a i) (P : Letter G X i j)
    (s : Word G X j a) (h : Bound E p (.cons P s))
    {y : X i} {z : X j} (hyz : P.relation y z) :
    (prefixTransport E trans p (.cons P s) h).label y =
      (prefixTransport E trans (p.extend P) s (next_bound E p P s h)).label z := by
  obtain ⟨x,hx⟩ := (p.serial_coserial trans).2 y
  rw [(prefixTransport E trans p (.cons P s) h).label_edge hx]
  symm
  apply Transport.label_edge
  rw [Word.eval_extend]
  exact ⟨y,hx,hyz⟩

/-- C20: the factor kernel is DERIVED from the closed word. -/
theorem factor {i j : I} (p : Word G X a i) (P : Letter G X i j)
    (s : Word G X j a) (h : Bound E p (.cons P s)) :
    Transport (prefixTransport E trans p (.cons P s) h).target P.relation where
  serial := (serial_coserial_of_invariant P.relation P.invariant P.nonempty (trans i) (trans j)).1
  coserial := (serial_coserial_of_invariant P.relation P.invariant P.nonempty (trans i) (trans j)).2
  invariant := P.invariant
  kernel y y' z hy hy' :=
    (edge_label E trans p P s h hy).trans (edge_label E trans p P s h hy').symm

theorem factor_target {i j : I} (p : Word G X a i) (P : Letter G X i j)
    (s : Word G X j a) (h : Bound E p (.cons P s)) :
    (factor E trans p P s h).target =
      (prefixTransport E trans (p.extend P) s (next_bound E p P s h)).target := by
  apply InvEq.ext
  intro z z'
  rw [(factor E trans p P s h).target_iff]
  constructor
  · rintro ⟨y,y',hy,he,hy'⟩
    change (prefixTransport E trans (p.extend P) s (next_bound E p P s h)).label z = _
    rw [← edge_label E trans p P s h hy,← edge_label E trans p P s h hy']
    exact he
  · intro he
    obtain ⟨y,hy⟩ := (factor E trans p P s h).coserial z
    obtain ⟨y',hy'⟩ := (factor E trans p P s h).coserial z'
    refine ⟨y,y',hy,?_,hy'⟩
    change (prefixTransport E trans p (.cons P s) h).label y = _
    rw [edge_label E trans p P s h hy,edge_label E trans p P s h hy']
    exact he

/-- The actual factor bijection, with only the proved literal kernel equality
used to identify the next quotient. -/
noncomputable def step {i j : I} (p : Word G X a i) (P : Letter G X i j)
    (s : Word G X j a) (h : Bound E p (.cons P s)) :
    Quotient (prefixTransport E trans p (.cons P s) h).target.val ≃
      Quotient (prefixTransport E trans (p.extend P) s (next_bound E p P s h)).target.val :=
  (factor E trans p P s h).quotientEquiv.trans
    (InvEq.quotientCongr (factor_target E trans p P s h))

theorem step_edge {i j : I} (p : Word G X a i) (P : Letter G X i j)
    (s : Word G X j a) (h : Bound E p (.cons P s)) {y : X i} {z : X j}
    (hyz : P.relation y z) : step E trans p P s h (Quotient.mk'' y) = Quotient.mk'' z := by
  change InvEq.quotientCongr _ ((factor E trans p P s h).quotientEquiv _) = _
  rw [(factor E trans p P s h).quotientEquiv_edge hyz,InvEq.quotientCongr_mk]

/-- C21: the canonical label conjugation on EVERY quotient class. -/
theorem step_label {i j : I} (p : Word G X a i) (P : Letter G X i j)
    (s : Word G X j a) (h : Bound E p (.cons P s))
    (q : Quotient (prefixTransport E trans p (.cons P s) h).target.val) :
    (prefixTransport E trans (p.extend P) s (next_bound E p P s h)).labelEquiv
      (step E trans p P s h q) = (prefixTransport E trans p (.cons P s) h).labelEquiv q := by
  induction q using Quotient.inductionOn with
  | _ y =>
    obtain ⟨z,hz⟩ := (factor E trans p P s h).serial y
    rw [step_edge E trans p P s h hz,Transport.labelEquiv_mk,Transport.labelEquiv_mk]
    exact (edge_label E trans p P s h hz).symm

theorem final_label (p : Word G X a a) (h : Bound E p (.nil a)) (y : X a) :
    (prefixTransport E trans p (.nil a) h).label y = Quotient.mk'' y := by
  let T := prefixTransport E trans p (.nil a) h
  exact Quotient.sound (h (T.predecessor y) y ⟨y,T.predecessor_spec y,rfl⟩)

theorem final_target (p : Word G X a a) (h : Bound E p (.nil a)) :
    (prefixTransport E trans p (.nil a) h).target = E := by
  apply InvEq.ext
  intro y z
  change ((prefixTransport E trans p (.nil a) h).label y = (prefixTransport E trans p (.nil a) h).label z) ↔ E y z
  rw [final_label E trans p h y,final_label E trans p h z]
  exact Quotient.eq

/-- Compose each actual consecutive transport, stopping in the literal
original quotient. This is not defined by selecting unrelated edge charts. -/
noncomputable def run : {i : I} → (p : Word G X a i) → (s : Word G X i a) →
    (h : Bound E p s) → Quotient (prefixTransport E trans p s h).target.val → Quotient E.val
  | _,p,.nil _,h,q => InvEq.quotientCongr (final_target E trans p h) q
  | _,p,.cons P s,h,q => run (p.extend P) s (next_bound E p P s h)
      (step E trans p P s h q)

/-- C23: literal telescoping through the ONE common original quotient. -/
theorem run_label {i : I} (p : Word G X a i) (s : Word G X i a) (h : Bound E p s)
    (q : Quotient (prefixTransport E trans p s h).target.val) :
    run E trans p s h q = (prefixTransport E trans p s h).labelEquiv q := by
  induction s with
  | nil a =>
    induction q using Quotient.inductionOn with
    | _ y =>
      rw [run,InvEq.quotientCongr_mk,Transport.labelEquiv_mk,final_label E trans p h y]
  | cons P s ih =>
    rw [run,ih,step_label E trans p P s h]

theorem initial_label (s : Word G X a a) (h : Bound E (.nil a) s) (y : X a) :
    (prefixTransport E trans (.nil a) s h).label y = Quotient.mk'' y :=
  (prefixTransport E trans (.nil a) s h).label_edge rfl

theorem initial_target (s : Word G X a a) (h : Bound E (.nil a) s) :
    (prefixTransport E trans (.nil a) s h).target = E := by
  apply InvEq.ext
  intro y z
  change ((prefixTransport E trans (.nil a) s h).label y = (prefixTransport E trans (.nil a) s h).label z) ↔ E y z
  rw [initial_label E trans s h y,initial_label E trans s h z]
  exact Quotient.eq

noncomputable def holonomy (s : Word G X a a) (h : Bound E (.nil a) s) :
    Quotient E.val → Quotient E.val :=
  run E trans (.nil a) s h ∘ InvEq.quotientCongr (initial_target E trans s h).symm

theorem holonomy_identity (s : Word G X a a) (h : Bound E (.nil a) s) :
    holonomy E trans s h = id := by
  funext q
  induction q using Quotient.inductionOn with
  | _ y =>
    change run E trans (.nil a) s h (InvEq.quotientCongr _ (Quotient.mk'' y)) = Quotient.mk'' y
    rw [InvEq.quotientCongr_mk,run_label,Transport.labelEquiv_mk,initial_label E trans s h y]

/-- C24: every coarser invariant J works by the SAME actual closed word;
its canonical prefix label is exactly the coarsening of the E label. -/
theorem coarser_bound {J : InvEq G (X a)} (hEJ : E ≤ J) {i : I}
    (p : Word G X a i) (s : Word G X i a) (h : Bound E p s) : Bound J p s :=
  fun x y hxy => hEJ (h x y hxy)

theorem coarser_label {J : InvEq G (X a)} (hEJ : E ≤ J) {i : I}
    (p : Word G X a i) (s : Word G X i a) (h : Bound E p s) (y : X i) :
    (prefixTransport J trans p s (coarser_bound E hEJ p s h)).label y =
      Quot.mapRight hEJ ((prefixTransport E trans p s h).label y) := by
  let T := prefixTransport E trans p s h
  rw [(prefixTransport J trans p s (coarser_bound E hEJ p s h)).label_edge (T.predecessor_spec y)]
  rfl

theorem all_coarser_holonomy (s : Word G X a a) (h : Bound E (.nil a) s)
    (J : InvEq G (X a)) (hEJ : E ≤ J) :
    holonomy J trans s (coarser_bound E hEJ (.nil a) s h) = id := holonomy_identity J trans s _
end Return
end CCO.QuotientTransport
