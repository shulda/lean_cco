import CCO.SimultaneousQuotients.Boundaries.PhaseExact
import CCO.SimultaneousQuotients.Boundaries.PhaseKernel

/-! The C56 full-group calculation is a genuine presentation of ACTUAL
full-exact quotients of the infinite original clone source. The carrier
bijections from literal classes, exact cut presentations, and original-group
orbital characterizations prove this conservative presentation directly. -/

namespace CCO.SimultaneousQuotients.Boundaries.PhasePresentation
open PhaseKernel
abbrev Original := Phase.Aut Bool

def delta (g : Original) : Bool := (g.val false ⟨false,0⟩).phase

theorem phase_action (g : Original) (i : Bool) (x : Phase.Point Bool i) :
    (g.val i x).phase = (delta g ^^ x.phase) := by
  have h := congrArg (fun c : Option Bool => c.getD false)
    (g.property i false x ⟨false,0⟩)
  simp only [Phase.read_phase] at h
  change ((g.val i x).phase ^^ delta g) = (x.phase ^^ false) at h
  cases hx : (g.val i x).phase <;> cases hd : delta g <;>
    cases hp : x.phase <;> simp_all

@[simp] theorem delta_one : delta 1 = false := rfl

theorem delta_mul (g h : Original) : delta (g*h) = (delta g ^^ delta h) :=
  phase_action g false (h.val false ⟨false,0⟩)

instance fineAction : MulAction Original FinePoint where
  smul g p := (p.1,delta g ^^ p.2)
  one_smul p := by cases p with | mk s b => cases b <;> rfl
  mul_smul g h p := by
    change (p.1,delta (g*h) ^^ p.2) = (p.1,delta g ^^ (delta h ^^ p.2))
    rw [delta_mul,Bool.xor_assoc]

instance coarseAction : MulAction Original CoarsePoint where
  smul g p := p.map (fun b => delta g ^^ b)
  one_smul p := by cases p with
    | none => rfl
    | some b => cases b <;> rfl
  mul_smul g h p := by
    cases p with
    | none => rfl
    | some b =>
      change some (delta (g*h) ^^ b) = some (delta g ^^ (delta h ^^ b))
      rw [delta_mul,Bool.xor_assoc]

def fineProjection (p : Phase.Tagged Bool) : FinePoint := (p.1,p.2.phase)
def collapse : FinePoint → CoarsePoint
  | (false,_) => none
  | (true,b) => some b

def coarseProjection (p : Phase.Tagged Bool) : CoarsePoint := collapse (fineProjection p)

theorem fineProjection_onto : Function.Surjective fineProjection := by
  rintro ⟨i,b⟩
  exact ⟨⟨i,⟨b,0⟩⟩,rfl⟩

theorem coarseProjection_onto : Function.Surjective coarseProjection := by
  intro p
  cases p with
  | none => exact ⟨⟨false,⟨false,0⟩⟩,rfl⟩
  | some b => exact ⟨⟨true,⟨b,0⟩⟩,rfl⟩

theorem fineProjection_equivariant (g : Original) (p : Phase.Tagged Bool) :
    fineProjection (g • p) = g • fineProjection p := by
  exact Prod.ext rfl (phase_action g p.1 p.2)

theorem coarseProjection_equivariant (g : Original) (p : Phase.Tagged Bool) :
    coarseProjection (g • p) = g • coarseProjection p := by
  rw [coarseProjection,fineProjection_equivariant]
  cases p with
  | mk s x => cases s <;> rfl

def fineCarrierEquiv :
    (Sigma fun i => Quotient (Phase.phaseKernel Bool i)) ≃ FinePoint where
  toFun p := (p.1,Phase.phaseQuotientEquiv Bool p.1 p.2)
  invFun p := ⟨p.1,(Phase.phaseQuotientEquiv Bool p.1).symm p.2⟩
  left_inv p := by cases p; simp
  right_inv p := by cases p; simp

theorem fineCarrierEquiv_projection (i : Bool) (x : Phase.Point Bool i) :
    fineCarrierEquiv ⟨i,Quotient.mk'' x⟩ = fineProjection ⟨i,x⟩ := rfl

def coarseKernel : (i : Bool) → Setoid (Phase.Point Bool i)
  | false => ⊤
  | true => Phase.phaseKernel Bool true

def coarseExact : (i : Bool) → RawExact.NonemptyExact (Phase.source Bool) i i
  | false => RawExact.NonemptyExact.top _ false false
  | true => Phase.phaseExact Bool true

theorem coarseExact_spec (i : Bool) :
    RawExact.evaluate (Phase.source Bool) (coarseExact i).words = (coarseKernel i).r := by
  cases i with
  | false => exact RawExact.evaluate_nil _
  | true => exact Phase.phaseExact_spec Bool true

noncomputable def coarseCarrierEquiv :
    (Sigma fun i => Quotient (coarseKernel i)) ≃ CoarsePoint where
  toFun p := match p with
    | ⟨false,_⟩ => none
    | ⟨true,q⟩ => some (Phase.phaseQuotientEquiv Bool true q)
  invFun p := match p with
    | none => ⟨false,Quotient.mk'' ⟨false,0⟩⟩
    | some b => ⟨true,(Phase.phaseQuotientEquiv Bool true).symm b⟩
  left_inv p := by
    rcases p with ⟨s,q⟩
    cases s with
    | false =>
      apply congrArg (Sigma.mk false)
      induction q using Quotient.inductionOn with
      | _ x => exact Quotient.sound trivial
    | true =>
      apply congrArg (Sigma.mk true)
      exact (Phase.phaseQuotientEquiv Bool true).symm_apply_apply q
  right_inv p := by cases p <;> simp

theorem coarseCarrierEquiv_projection (i : Bool) (x : Phase.Point Bool i) :
    coarseCarrierEquiv ⟨i,Quotient.mk'' x⟩ = coarseProjection ⟨i,x⟩ := by
  cases i <;> rfl

@[simp] theorem delta_motion (d : Bool) :
    delta (Phase.motion Bool d (fun _ _ => 1)) = d := by cases d <;> rfl

/-- Every named typed fine pair orbital is exactly its XOR relation. Hence
`PhaseKernel.fine` names the complete actual old-group orbital language. -/
theorem fine_orbital (p q p' q' : FinePoint) :
    GroupActions.orbital (G := Original) p q p' q' ↔
      p'.1 = p.1 ∧ q'.1 = q.1 ∧
        (p'.2 ^^ q'.2) = (p.2 ^^ q.2) := by
  constructor
  · rintro ⟨g,rfl,rfl⟩
    refine ⟨rfl,rfl,?_⟩
    change ((delta g ^^ p.2) ^^ (delta g ^^ q.2)) = (p.2 ^^ q.2)
    cases hd : delta g <;> cases hp : p.2 <;> cases hq : q.2 <;> rfl
  · rintro ⟨hp,hq,hxor⟩
    let d := p'.2 ^^ p.2
    refine ⟨Phase.motion Bool d (fun _ _ => 1), ?_, ?_⟩
    · change (p.1,delta _ ^^ p.2) = p'
      rw [delta_motion]
      refine Prod.ext hp.symm ?_
      dsimp only [d]
      cases p.2 <;> cases p'.2 <;> rfl
    · change (q.1,delta _ ^^ q.2) = q'
      rw [delta_motion]
      refine Prod.ext hq.symm ?_
      dsimp only [d]
      cases h0 : p.2 <;> cases h1 : p'.2 <;>
        cases h2 : q.2 <;> cases h3 : q'.2 <;> simp_all

/-- Matching all unary and binary names in the finite presentation is
EXACTLY belonging to one original-group pair orbit, not merely invariance. -/
theorem fine_complete_orbitals (p q p' q' : FinePoint) :
    GroupActions.orbital (G := Original) p q p' q' ↔
      (∀ s, fine.unary s p ↔ fine.unary s p') ∧
      (∀ s, fine.unary s q ↔ fine.unary s q') ∧
      (∀ c, fine.binary c p q ↔ fine.binary c p' q') := by
  rw [fine_orbital]
  constructor
  · rintro ⟨hp,hq,hb⟩
    exact ⟨fun s => by change p.1=s ↔ p'.1=s; rw [hp],
      fun s => by change q.1=s ↔ q'.1=s; rw [hq],
      fun c => by change (p.2 ^^ q.2)=c ↔ (p'.2 ^^ q'.2)=c; rw [hb]⟩
  · rintro ⟨hp,hq,hb⟩
    exact ⟨(hp p.1).mp rfl,(hq q.1).mp rfl,(hb (p.2 ^^ q.2)).mp rfl⟩

theorem coarse_move (x y : Bool) :
    Phase.motion Bool (y ^^ x) (fun _ _ => 1) • (some x : CoarsePoint) = some y := by
  change some (delta _ ^^ x) = some y
  rw [delta_motion]
  cases x <;> cases y <;> rfl

/-- Every named coarse pair type is one ACTUAL original-group orbital. In
particular coarsening U destroys the cross-phase distinction, while the V
axis retains its two phases. No proper subgroup of full coarse Aut is used
in the subsequent kernel calculation. -/
theorem coarse_complete_orbitals (p q p' q' : CoarsePoint) :
    GroupActions.orbital (G := Original) p q p' q' ↔
      (∀ s, coarse.unary s p ↔ coarse.unary s p') ∧
      (∀ s, coarse.unary s q ↔ coarse.unary s q') ∧
      (∀ c, coarse.binary c p q ↔ coarse.binary c p' q') := by
  constructor
  · rintro ⟨g,rfl,rfl⟩
    refine ⟨?_,?_,?_⟩
    · intro s
      cases p <;> exact Iff.rfl
    · intro s
      cases q <;> exact Iff.rfl
    · intro c
      cases p with
      | none => exact Iff.rfl
      | some x =>
        cases q with
        | none => exact Iff.rfl
        | some y =>
          change (x ^^ y) = c ↔ ((delta g ^^ x) ^^ (delta g ^^ y)) = c
          have hh : ((delta g ^^ x) ^^ (delta g ^^ y)) = (x ^^ y) := by
            cases hd : delta g <;> cases x <;> cases y <;> rfl
          rw [hh]
  · rintro ⟨hU,hV,hB⟩
    have hp : p'.isSome = p.isSome := (hU p.isSome).mp rfl
    have hq : q'.isSome = q.isSome := (hV q.isSome).mp rfl
    cases p with
    | none =>
      cases p' with
      | some x' => cases hp
      | none =>
        cases q with
        | none =>
          cases q' with
          | some y' => cases hq
          | none => exact ⟨1,rfl,rfl⟩
        | some y =>
          cases q' with
          | none => cases hq
          | some y' => exact ⟨Phase.motion Bool (y' ^^ y) (fun _ _ => 1),rfl,coarse_move y y'⟩
    | some x =>
      cases p' with
      | none => cases hp
      | some x' =>
        cases q with
        | none =>
          cases q' with
          | some y' => cases hq
          | none => exact ⟨Phase.motion Bool (x' ^^ x) (fun _ _ => 1),coarse_move x x',rfl⟩
        | some y =>
          cases q' with
          | none => cases hq
          | some y' =>
            have hb : (x' ^^ y') = (x ^^ y) := (hB (x ^^ y)).mp rfl
            obtain ⟨g,hgx,hgy⟩ := (fine_orbital (true,x) (true,y) (true,x') (true,y')).mpr
              ⟨rfl,rfl,hb⟩
            exact ⟨g,congrArg some (congrArg Prod.snd hgx),congrArg some (congrArg Prod.snd hgy)⟩

/-- The true fine/coarse quotient map commutes with every FULL fine
binary automorphism. This is the homomorphism whose pointwise kernel the
C56 calculation proves trivial. -/
theorem full_descent_commutes (g : FineAut) (p : FinePoint) :
    (descent g).val (collapse p) = collapse (g.val p) := by
  rcases p with ⟨s,b⟩
  rw [fine_action_diagonal]
  cases s <;> rfl

end CCO.SimultaneousQuotients.Boundaries.PhasePresentation
