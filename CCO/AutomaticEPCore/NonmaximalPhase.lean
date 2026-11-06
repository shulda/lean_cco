import CCO.AutomaticEPCore.NonmaximalBoundary
import CCO.ParityHasse.Original.ParitySeed
import CCO.ParityHasse.Relative.Gate
import CCO.RigidGroupoid.Geometry.Bridge
import CCO.RigidGroupoid.Geometry.QuotientBijection
import CCO.RigidGroupoid.Geometry.RootedGroupoid
import CCO.RigidGroupoid.Phase.AbstractCharacter

/-! The literal parity interval and complete phase correspondences of the
nonmaximal counterexample. All statements concern the actual infinite source;
no automatic-core or maximal-phase source theorem is used. -/

namespace CCO.AutomaticEPCore.NonmaximalBoundary
open CCO.ParityHasse.Original CCO.ParityHasse.Relative

def bRel (x y : Point) : Prop := source.atomRel (i := ()) (j := ()) (true,true) x y

theorem bRel_iff (x y : Point) : bRel x y ↔ x.block = y.block ∧ x.bit ≠ y.bit := by
  change colour x y = some (true,true) ↔ _
  have hn : x.bit ≠ y.bit → x ≠ y := fun h he => h (congrArg Point.bit he)
  cases hx : x.bit <;> cases hy : y.bit <;> by_cases hb : x.block = y.block <;>
    simp [colour_some,pattern,hx,hy,hb,hn]

private def gain : Nat → Bool
  | 0 => false
  | n+1 => true ^^ gain n

private theorem gain_add (n m : Nat) : gain (n+m) = (gain n ^^ gain m) := by
  induction n with
  | zero => simp [gain]
  | succ n ih => simp only [Nat.succ_add,gain,ih,Bool.xor_assoc]

private theorem gain_even {n : Nat} (hn : Even n) : gain n = false := by
  obtain ⟨k,rfl⟩ := hn
  rw [gain_add,Bool.xor_self]

private theorem gain_odd {n : Nat} (hn : Odd n) : gain n = true := by
  obtain ⟨k,rfl⟩ := hn
  rw [show 2*k+1 = (k+k)+1 by omega,gain,gain_add,Bool.xor_self]
  rfl

private theorem bPow (n : Nat) (x y : Point) (h : relPow bRel n x y) :
    x.block = y.block ∧ (x.bit ^^ y.bit) = gain n := by
  induction n generalizing x with
  | zero =>
    change x = y at h
    subst y
    exact ⟨rfl,Bool.xor_self _⟩
  | succ n ih =>
    obtain ⟨z,hxz,hzy⟩ := h
    have hb := (bRel_iff x z).mp hxz
    have hi := ih z hzy
    refine ⟨hb.1.trans hi.1,?_⟩
    change (x.bit ^^ y.bit) = (true ^^ gain n)
    rw [← hi.2]
    exact (show ∀ a b c : Bool, a ≠ b → (a ^^ c) = (true ^^ (b ^^ c)) by decide)
      x.bit z.bit y.bit hb.2

theorem b_no_odd_closed (x : Point) (n : Nat) (hn : Odd n) :
    ¬ relPow bRel n x x := by
  intro h
  have hh := (bPow n x x h).2
  rw [Bool.xor_self,gain_odd hn] at hh
  exact Bool.false_ne_true hh

theorem b_even_iff (x y : Point) : EvenWalk bRel x y ↔ cloneEq x y := by
  constructor
  · rintro ⟨n,hn,hxy⟩
    have hh := bPow n x y hxy
    rw [gain_even hn] at hh
    have hp : x.bit = y.bit :=
      (show ∀ a b : Bool, (a ^^ b) = false → a = b by decide) _ _ hh.2
    exact Prod.ext hh.1 hp
  · intro hxy
    let z : Point := ⟨x.block,!x.bit,0⟩
    have hb : x.block = y.block := congrArg Prod.fst hxy
    have hp : x.bit = y.bit := congrArg Prod.snd hxy
    refine ⟨2,by decide,z,(bRel_iff x z).mpr ⟨rfl,?_⟩,
      y,(bRel_iff z y).mpr ⟨hb,?_⟩,rfl⟩
    · change x.bit ≠ !x.bit
      cases x.bit <;> decide
    · change (!x.bit) ≠ y.bit
      rw [← hp]
      cases x.bit <;> decide

theorem b_connected_iff (x y : Point) : ConnectedWalk bRel x y ↔ blockEq x y := by
  constructor
  · rintro ⟨n,hxy⟩
    exact (bPow n x y hxy).1
  · intro hb
    by_cases hp : x.bit = y.bit
    · obtain ⟨n,_,hn⟩ := (b_even_iff x y).mpr (Prod.ext hb hp)
      exact ⟨n,hn⟩
    · exact ⟨1,(relPow_one bRel x y).mpr ((bRel_iff x y).mpr ⟨hb,hp⟩)⟩

theorem b_even_eq : evenColourEq source homogeneous (true,true) = cloneEq := by
  apply ColourEq.ext
  exact b_even_iff

theorem b_connected_eq : connectivityColourEq source homogeneous (true,true) = blockEq := by
  apply ColourEq.ext
  exact b_connected_iff

theorem b_index_two (x : Point) : relativeIndex cloneEq.val blockEq.val x = 2 := by
  rw [← b_even_eq,← b_connected_eq]
  exact parity_seed_index_two source homogeneous (true,true) b_no_odd_closed x

theorem b_cover : cloneEq ⋖ blockEq := by
  rw [← b_even_eq,← b_connected_eq]
  exact parity_seed_cover source homogeneous (true,true) b_no_odd_closed

/-- These are literal FULL exact candidates in the accepted gate API. -/
theorem clone_candidate : Candidate source cloneEq blockEq cloneEq :=
  ⟨clone_exact,le_rfl,inf_eq_left.mpr clone_lt_block.le⟩

theorem sheet_candidate : Candidate source cloneEq blockEq sheetEq :=
  ⟨sheet_exact,clone_lt_sheet.le,sheet_inf_block⟩

theorem clone_not_maximal : ¬ Maximal (Candidate source cloneEq blockEq) cloneEq := by
  intro hm
  exact clone_lt_sheet.not_ge (hm.2 sheet_candidate clone_lt_sheet.le)

/-- Maximality is over all FULL exact equivalences, not a selected family. -/
theorem sheet_maximal : Maximal (Candidate source cloneEq blockEq) sheetEq := by
  refine ⟨sheet_candidate,?_⟩
  intro E hE hSE
  rcases complement_classification E hE.2.1 hE.2.2 with h | h
  · rw [h] at hSE
    exact False.elim (clone_lt_sheet.not_ge hSE)
  · exact h ▸ le_rfl

theorem b_odd_iff (x y : Point) : OddWalk bRel x y ↔ bRel x y := by
  constructor
  · rintro ⟨n,hn,hxy⟩
    have h := bPow n x y hxy
    rw [gain_odd hn] at h
    exact (bRel_iff x y).mpr ⟨h.1,
      (show ∀ a b : Bool, (a ^^ b) = true → a ≠ b by decide) _ _ h.2⟩
  · intro h
    exact ⟨1,odd_one,(relPow_one bRel x y).mpr h⟩

theorem b_odd_exact : Exact source (i := ()) (odd cloneEq.val blockEq.val) := by
  obtain ⟨_,O,_,hO⟩ := parity_profiles_nonempty_exact source homogeneous (i := ()) (true,true)
  refine ⟨O,?_⟩
  funext x y
  apply propext
  rw [hO x y]
  change OddWalk bRel x y ↔ blockEq x y ∧ ¬cloneEq x y
  rw [b_odd_iff,bRel_iff]
  simp only [cloneEq_apply,blockEq_apply,owner,Prod.mk.injEq]
  tauto

/-- A genuine maximal gate certificate, on the displayed original interval. -/
noncomputable def firstMaximalGate : MaximalGate source homogeneous cloneEq blockEq :=
  Classical.choice (exists_maximalGate source homogeneous semanticCCO cloneEq blockEq
    clone_exact clone_lt_block.le b_odd_exact default (b_index_two default))

theorem firstMaximalGate_kernel : firstMaximalGate.kernel = sheetEq := by
  have hm := firstMaximalGate.maximal
  rcases complement_classification firstMaximalGate.kernel hm.1.2.1 hm.1.2.2 with h | h
  · rw [h] at hm
    exact False.elim (clone_not_maximal hm)
  · exact h

open CCO.RigidGroupoid.Geometry

/-- The actual full-exact clone quotient kernel. -/
def cloneKernel : Kernel source () := ⟨cloneEq.val,clone_exact⟩

/-- These are relations on the entire infinite source, not a finite control. -/
def cloneArrowRel (d : Bool) (x y : Point) : Prop :=
  x.block = y.block ∧ (x.bit ^^ y.bit) = d

theorem cloneArrowRel_zero : cloneArrowRel false = cloneKernel.rel := by
  funext x y
  apply propext
  change (x.block = y.block ∧ (x.bit ^^ y.bit) = false) ↔ owner x = owner y
  simp only [owner,Prod.mk.injEq]
  exact and_congr_right (fun _ => by cases x.bit <;> cases y.bit <;> decide)

theorem cloneArrowRel_one : cloneArrowRel true = bRel := by
  funext x y
  apply propext
  rw [bRel_iff]
  exact and_congr_right (fun _ => by cases x.bit <;> cases y.bit <;> decide)

theorem cloneArrowRel_exact (d : Bool) : FullExact source (i := ()) (j := ()) (cloneArrowRel d) := by
  cases d with
  | false => rw [cloneArrowRel_zero]; exact cloneKernel.exact
  | true =>
    rw [cloneArrowRel_one]
    exact ⟨RawExact.exactDiversityAtom source (i := ()) (j := ()) (true,true),
      RawExact.exactDiversityAtom_relation source (i := ()) (j := ()) (true,true)⟩

theorem cloneArrowRel_converse (d : Bool) :
    TRel.converse (X := fun _ : Unit => Point) (i := ()) (j := ()) (cloneArrowRel d) = cloneArrowRel d := by
  funext x y
  apply propext
  simp only [TRel.converse,cloneArrowRel,eq_comm,Bool.xor_comm]

theorem cloneArrowRel_comp (d e : Bool) :
    TRel.comp (X := fun _ : Unit => Point) (i := ()) (j := ()) (k := ())
      (cloneArrowRel d) (cloneArrowRel e) = cloneArrowRel (d ^^ e) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z,hxz,hzy⟩
    refine ⟨hxz.1.trans hzy.1,?_⟩
    calc
      (x.bit ^^ y.bit) = ((x.bit ^^ z.bit) ^^ (z.bit ^^ y.bit)) := by
        cases x.bit <;> cases z.bit <;> cases y.bit <;> rfl
      _ = _ := by rw [hxz.2,hzy.2]
  · intro h
    let z : Point := ⟨x.block,x.bit ^^ d,0⟩
    refine ⟨z,⟨rfl,?_⟩,⟨h.1,?_⟩⟩
    · change (x.bit ^^ (x.bit ^^ d)) = d
      cases x.bit <;> cases d <;> rfl
    · change ((x.bit ^^ d) ^^ y.bit) = e
      exact (show ∀ a b d e : Bool, (a ^^ b) = (d ^^ e) → ((a ^^ d) ^^ b) = e
        by decide) _ _ _ _ h.2

def cloneArrow (d : Bool) : Arrow source cloneKernel cloneKernel where
  rel := cloneArrowRel d
  exact := cloneArrowRel_exact d
  left := by rw [← cloneArrowRel_zero,cloneArrowRel_comp,Bool.false_xor]
  right := by rw [← cloneArrowRel_zero,cloneArrowRel_comp,Bool.xor_false]
  source := by rw [cloneArrowRel_converse,cloneArrowRel_comp,Bool.xor_self,cloneArrowRel_zero]
  target := by rw [cloneArrowRel_converse,cloneArrowRel_comp,Bool.xor_self,cloneArrowRel_zero]

/-- No full functional correspondence can send a clone quotient class to
another block. This quantifies over every FULL exact Arrow. -/
theorem cloneArrow_same_block (R : Arrow source cloneKernel cloneKernel)
    (x y : Point) (hxy : R.rel x y) : x.block = y.block := by
  by_contra hb
  let z : Point := ⟨(max x.block.1 y.block.1+1,false),y.bit,0⟩
  have hxz : x.block ≠ z.block := by
    intro he
    have hh := congrArg Prod.fst he
    change x.block.1 = max x.block.1 y.block.1+1 at hh
    omega
  have hyz : y.block ≠ z.block := by
    intro he
    have hh := congrArg Prod.fst he
    change y.block.1 = max x.block.1 y.block.1+1 at hh
    omega
  have hne : x ≠ y := fun he => hb (congrArg Point.block he)
  have hne' : x ≠ z := fun he => hxz (congrArg Point.block he)
  have hc : colour x y = colour x z := by
    simp only [colour,hne,hne',ite_false]
    simp [pattern,hb,hxz,z]
  have hi := Exact.colourInvariant source homogeneous R.exact
  have hxz' : R.rel x z := (hi x y x z hc).mp hxy
  have hk : cloneKernel.rel y z := by
    rw [← R.target]
    exact ⟨x,hxy,hxz'⟩
  exact hyz (congrArg Prod.fst hk)

/-- Exhaustive identification of the full first quotient functional group.
The two arrows are identity and the actual old b correspondence. -/
theorem cloneArrow_exhaustive (R : Arrow source cloneKernel cloneKernel) :
    ∃ d : Bool, R = cloneArrow d := by
  let x : Point := default
  obtain ⟨y,hxy⟩ := R.exact.serial source homogeneous x
  refine ⟨x.bit ^^ y.bit,?_⟩
  apply R.eq_of_common_real_pair homogeneous
    (cloneArrow (x.bit ^^ y.bit)) hxy
  exact ⟨cloneArrow_same_block R x y hxy,rfl⟩

theorem cloneArrow_injective : Function.Injective cloneArrow := by
  intro d e he
  let x : Point := ⟨(0,false),false,0⟩
  let y : Point := ⟨(0,false),d,0⟩
  have hd : (cloneArrow d).rel x y := ⟨rfl,by cases d <;> rfl⟩
  rw [he] at hd
  simpa using (show (false ^^ d) = e from hd.2)

noncomputable def fullCloneArrowEquiv : Bool ≃ Arrow source cloneKernel cloneKernel :=
  Equiv.ofBijective cloneArrow ⟨cloneArrow_injective,fun R => by
    obtain ⟨d,hd⟩ := cloneArrow_exhaustive R
    exact ⟨d,hd.symm⟩⟩

theorem calculus : ExactCalculus source := exactCalculus_of_homogeneous_CCO source homogeneous semanticCCO

theorem cloneArrow_comp (d e : Bool) :
    (cloneArrow d).comp calculus (cloneArrow e) = cloneArrow (d ^^ e) :=
  Arrow.ext (cloneArrowRel_comp d e)

/-- The exhaustive character reads the common bit difference. -/
noncomputable def cloneCharacter (R : Arrow source cloneKernel cloneKernel) : Bool :=
  fullCloneArrowEquiv.symm R

@[simp] theorem cloneCharacter_arrow (d : Bool) : cloneCharacter (cloneArrow d) = d :=
  fullCloneArrowEquiv.symm_apply_apply d

theorem cloneCharacter_comp (R T : Arrow source cloneKernel cloneKernel) :
    cloneCharacter (R.comp calculus T) = (cloneCharacter R ^^ cloneCharacter T) := by
  obtain ⟨d,rfl⟩ := cloneArrow_exhaustive R
  obtain ⟨e,rfl⟩ := cloneArrow_exhaustive T
  rw [cloneArrow_comp,cloneCharacter_arrow,cloneCharacter_arrow,cloneCharacter_arrow]

theorem cloneCharacter_id : cloneCharacter (Arrow.id cloneKernel) = false := by
  have h : Arrow.id cloneKernel = cloneArrow false := Arrow.ext cloneArrowRel_zero.symm
  rw [h,cloneCharacter_arrow]

theorem cloneCharacter_b : cloneCharacter (cloneArrow true) = true := cloneCharacter_arrow true

/-- Literal quotient readout: a clone class is its actual (block,bit). -/
def cloneQuotientEquiv : cloneKernel.Class ≃ Block × Bool where
  toFun := Quotient.lift owner (fun _ _ h => h)
  invFun o := cloneKernel.project ⟨o.1,o.2,0⟩
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x => exact Quotient.sound rfl
  right_inv := by intro o; rfl

theorem cloneArrow_quotient (d : Bool) (q : cloneKernel.Class) :
    cloneQuotientEquiv ((cloneArrow d).quotientMap homogeneous q) =
      ((cloneQuotientEquiv q).1,(cloneQuotientEquiv q).2 ^^ d) := by
  induction q using Quotient.inductionOn with
  | _ x =>
    let y : Point := ⟨x.block,x.bit ^^ d,0⟩
    have h : (cloneArrow d).rel x y := ⟨rfl,by
      change (x.bit ^^ (x.bit ^^ d)) = d
      cases x.bit <;> cases d <;> rfl⟩
    change cloneQuotientEquiv ((cloneArrow d).quotientMap homogeneous (cloneKernel.project x)) = _
    rw [(cloneArrow d).quotientMap_eq_iff homogeneous x y |>.mpr h]
    rfl

/-- Exhaustion of ALL original-equivariant quotient permutations, without
an exactness premise on their graphs. Thus the full functional group itself,
and not merely a chosen exact subgroup, consists of the displayed two maps. -/
theorem clone_functional_exhaustive :
    letI := cloneKernel.action homogeneous
    ∀ e : Equiv.Perm cloneKernel.Class,
      (∀ (g : Aut) q, e (g • q) = g • e q) →
      ∃ d : Bool, e = (cloneArrow d).quotientEquiv homogeneous := by
  letI := cloneKernel.action homogeneous
  intro e he
  let x : Point := default
  obtain ⟨y,hy⟩ := Quotient.mk_surjective (e (cloneKernel.project x))
  change cloneKernel.project y = e (cloneKernel.project x) at hy
  have hb : x.block = y.block := by
    by_contra hbad
    let z : Point := ⟨(max x.block.1 y.block.1+1,false),y.bit,0⟩
    have hxz : x.block ≠ z.block := by
      intro h
      have hh := congrArg Prod.fst h
      change x.block.1 = max x.block.1 y.block.1+1 at hh
      omega
    have hyz : y.block ≠ z.block := by
      intro h
      have hh := congrArg Prod.fst h
      change y.block.1 = max x.block.1 y.block.1+1 at hh
      omega
    have hne : x ≠ y := fun h => hbad (congrArg Point.block h)
    have hne' : x ≠ z := fun h => hxz (congrArg Point.block h)
    have hc : source.colour (i := ()) (j := ()) x y = source.colour x z := by
      change colour x y = colour x z
      simp [colour,pattern,hne,hne',hbad,hxz,z]
    obtain ⟨g,hgx,hgy⟩ := source.pair_homogeneous_of_homogeneous homogeneous x x y z hc
    have hqx : g • cloneKernel.project x = cloneKernel.project x :=
      congrArg cloneKernel.project hgx
    have hqy : g • cloneKernel.project y = cloneKernel.project z :=
      congrArg cloneKernel.project hgy
    have hh := he g (cloneKernel.project x)
    rw [hqx,← hy,hqy] at hh
    exact hyz (congrArg Prod.fst (Quotient.exact hh))
  let d := x.bit ^^ y.bit
  have hArrow : (cloneArrow d).rel x y := ⟨hb,rfl⟩
  refine ⟨d,?_⟩
  apply Equiv.ext
  intro q
  obtain ⟨g,hg⟩ := cloneKernel.class_transitive homogeneous (cloneKernel.project x) q
  rw [← hg,he]
  change g • e (cloneKernel.project x) =
    (cloneArrow d).quotientMap homogeneous (g • cloneKernel.project x)
  rw [(cloneArrow d).quotientMap_equivariant homogeneous]
  exact congrArg (fun r : cloneKernel.Class => g • r)
    (hy.symm.trans ((cloneArrow d).quotientMap_eq_iff homogeneous x y |>.mpr hArrow).symm)

/-- The concrete lambda is equivariant for the character on ALL first
quotient arrows. Independent block seeds are retained. -/
theorem lambda_character (R : Arrow source cloneKernel cloneKernel)
    (x y : Point) (h : R.rel x y) :
    ((label x).1 ^^ (label y).1) = cloneCharacter R := by
  obtain ⟨d,rfl⟩ := cloneArrow_exhaustive R
  rw [cloneCharacter_arrow]
  change (x.bit ^^ x.block.2 ^^ (y.bit ^^ y.block.2)) = d
  have hb := congrArg Prod.snd h.1
  rw [← hb]
  calc
    _ = (x.bit ^^ y.bit) := by cases x.bit <;> cases y.bit <;> cases x.block.2 <;> rfl
    _ = d := h.2

/-- Legal first markings are exactly bit plus an arbitrary block seed. -/
theorem legal_lambda_iff (ell : Point → Bool) :
    (∀ (R : Arrow source cloneKernel cloneKernel) x y, R.rel x y →
      (ell x ^^ ell y) = cloneCharacter R) ↔
      ∃ seed : Block → Bool, ∀ x, ell x = (x.bit ^^ seed x.block) := by
  constructor
  · intro h
    refine ⟨fun b => ell ⟨b,false,0⟩,?_⟩
    intro x
    let y : Point := ⟨x.block,false,0⟩
    have he : (cloneArrow x.bit).rel x y := ⟨rfl,by simp [y]⟩
    have hh := h (cloneArrow x.bit) x y he
    rw [cloneCharacter_arrow] at hh
    exact (show ∀ a b c : Bool, (a ^^ b) = c → a = (c ^^ b) by decide) _ _ _ hh
  · rintro ⟨seed,hseed⟩ R x y h
    obtain ⟨d,rfl⟩ := cloneArrow_exhaustive R
    rw [cloneCharacter_arrow,hseed x,hseed y,h.1]
    calc
      _ = (x.bit ^^ y.bit) := by
        cases x.bit <;> cases y.bit <;> cases seed y.block <;> rfl
      _ = d := h.2

@[instance_reducible] def isotropyGroupoid (K : Kernel source ()) : CategoryTheory.Groupoid Unit where
  Hom _ _ := Arrow source K K
  id _ := Arrow.id K
  comp R T := R.comp calculus T
  id_comp R := Arrow.id_comp calculus R
  comp_id R := Arrow.comp_id calculus R
  assoc R T U := Arrow.comp_assoc calculus R T U
  inv R := R.inv
  inv_comp R := Arrow.inv_comp calculus R
  comp_inv R := Arrow.comp_inv calculus R

/-- The whole first quotient character in the standard character API. -/
noncomputable def cloneFullCharacter :
    letI := isotropyGroupoid cloneKernel
    CCO.RigidGroupoid.Phase.Abstract.Character Unit := by
  letI := isotropyGroupoid cloneKernel
  exact {
    value := fun R => if cloneCharacter R then 1 else 0
    map_id := fun _ => by change (if cloneCharacter (Arrow.id cloneKernel) then _ else _) = 0; rw [cloneCharacter_id]; rfl
    map_comp := by
      intro p q r R T
      change (if cloneCharacter (R.comp calculus T) then _ else _) = _
      rw [cloneCharacter_comp]
      cases cloneCharacter R <;> cases cloneCharacter T <;> decide }

theorem lambda_fullCharacter (R : Arrow source cloneKernel cloneKernel)
    (x y : Point) (h : R.rel x y) :
    letI := isotropyGroupoid cloneKernel
    (if (label y).1 then (1 : ZMod 2) else 0) =
      (if (label x).1 then 1 else 0) + cloneFullCharacter.value (a := ()) (b := ()) R := by
  change (if (label y).1 then (1 : ZMod 2) else 0) =
    (if (label x).1 then 1 else 0) + (if cloneCharacter R then 1 else 0)
  rw [← lambda_character R x y h]
  cases (label x).1 <;> cases (label y).1 <;> decide

theorem cloneFullCharacter_b :
    letI := isotropyGroupoid cloneKernel
    cloneFullCharacter.value (a := ()) (b := ()) (cloneArrow true) = 1 := by
  change (if cloneCharacter (cloneArrow true) then _ else _) = 1
  rw [cloneCharacter_arrow]
  rfl

namespace LambdaPhase

abbrev parentSort (p : Bool) : Prefix.child .first := ⟨(),p⟩
abbrev Carrier (p : Bool) := Prefix.carrier .first (parentSort p)
noncomputable abbrev S := Prefix.source .first

/-- Every parent contains both actual global bits and infinitely many blocks. -/
def point (p : Bool) (n : Nat) (b : Bool) (k : Nat := 0) : Carrier p :=
  ⟨⟨(n,p ^^ b),b,k⟩,by change (b ^^ (p ^^ b)) = p; cases p <;> cases b <;> rfl⟩

/-- Each old r/s relation occurs between every pair of lambda parents. -/
def atom (p q d : Bool) : S.Atom (parentSort p) (parentSort q) :=
  ⟨(false,d),point p 0 false,point q 1 d,by
    simp only [source_colour]
    cases p <;> cases q <;> cases d <;> rfl⟩

theorem atom_iff (p q d : Bool) (x : Carrier p) (y : Carrier q) :
    S.atomRel (atom p q d) x y ↔ x.val.block ≠ y.val.block ∧ (x.val.bit ^^ y.val.bit) = d := by
  change S.colour x y = some (atom p q d) ↔ _
  rw [Prefix.colour_some]
  change colour x.val y.val = some (false,d) ↔ _
  have hn : x.val.block ≠ y.val.block → x.val ≠ y.val :=
    fun h he => h (congrArg Point.block he)
  simp only [colour_some,pattern,Prod.mk.injEq,decide_eq_false_iff_not]
  constructor
  · rintro ⟨_,hb,hd⟩
    exact ⟨hb,hd⟩
  · rintro ⟨hb,hd⟩
    exact ⟨hn hb,hb,hd⟩

def phaseRel (p q d : Bool) : TRel (Prefix.carrier .first) (parentSort p) (parentSort q) :=
  fun x y => (x.val.bit ^^ y.val.bit) = d

/-- A literal length-two RAW word represents each entire bit correspondence. -/
theorem phaseRel_word (p q d : Bool) :
    TRel.comp (S.atomRel (atom p p d)) (S.atomRel (atom p q false)) = phaseRel p q d := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z,hxz,hzy⟩
    have hh := ((atom_iff p p d x z).mp hxz).2
    have hz := ((atom_iff p q false z y).mp hzy).2
    have hp : z.val.bit = y.val.bit :=
      (show ∀ a b : Bool, (a ^^ b) = false → a = b by decide) _ _ hz
    change (x.val.bit ^^ y.val.bit) = d
    rwa [hp] at hh
  · intro h
    let z := point p (max x.val.block.1 y.val.block.1+1) y.val.bit
    have hxz : x.val.block ≠ z.val.block := by
      intro he
      have hh := congrArg Prod.fst he
      change x.val.block.1 = max x.val.block.1 y.val.block.1+1 at hh
      omega
    have hzy : z.val.block ≠ y.val.block := by
      intro he
      have hh := congrArg Prod.fst he
      change max x.val.block.1 y.val.block.1+1 = y.val.block.1 at hh
      omega
    exact ⟨z,(atom_iff p p d x z).mpr ⟨hxz,h⟩,
      (atom_iff p q false z y).mpr ⟨hzy,Bool.xor_self _⟩⟩

theorem phaseRel_exact (p q d : Bool) : FullExact S (phaseRel p q d) := by
  rw [← phaseRel_word]
  exact (exactCalculus_of_homogeneous_CCO S (Prefix.homogeneous .first)
    (Prefix.semanticCCO .first)).comp
    ⟨RawExact.exactDiversityAtom S (atom p p d),RawExact.exactDiversityAtom_relation S (atom p p d)⟩
    ⟨RawExact.exactDiversityAtom S (atom p q false),RawExact.exactDiversityAtom_relation S (atom p q false)⟩

/-- The actual S restriction at every lambda parent, with RAW exactness proved. -/
def kernel (p : Bool) : Kernel S (parentSort p) where
  setoid := Setoid.ker (fun x : Carrier p => x.val.bit)
  exact := by
    have he := phaseRel_exact p p false
    convert he using 1
    funext x y
    apply propext
    change (x.val.bit = y.val.bit) ↔ (x.val.bit ^^ y.val.bit) = false
    cases x.val.bit <;> cases y.val.bit <;> decide

theorem phaseRel_zero (p : Bool) : phaseRel p p false = (kernel p).rel := by
  funext x y
  apply propext
  change (x.val.bit ^^ y.val.bit) = false ↔ x.val.bit = y.val.bit
  cases x.val.bit <;> cases y.val.bit <;> decide

theorem phaseRel_converse (p q d : Bool) :
    TRel.converse (phaseRel p q d) = phaseRel q p d := by
  funext x y
  apply propext
  change ((y.val.bit ^^ x.val.bit) = d) ↔ (x.val.bit ^^ y.val.bit) = d
  rw [Bool.xor_comm y.val.bit x.val.bit]

theorem phaseRel_comp (p q r d e : Bool) :
    TRel.comp (phaseRel p q d) (phaseRel q r e) = phaseRel p r (d ^^ e) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z,hxz,hzy⟩
    change (x.val.bit ^^ y.val.bit) = (d ^^ e)
    calc
      _ = ((x.val.bit ^^ z.val.bit) ^^ (z.val.bit ^^ y.val.bit)) := by
        cases x.val.bit <;> cases z.val.bit <;> cases y.val.bit <;> rfl
      _ = _ := by rw [hxz,hzy]
  · intro h
    let z := point q 0 (x.val.bit ^^ d)
    refine ⟨z,?_,?_⟩
    · change (x.val.bit ^^ (x.val.bit ^^ d)) = d
      cases x.val.bit <;> cases d <;> rfl
    · change ((x.val.bit ^^ d) ^^ y.val.bit) = e
      exact (show ∀ a b d e : Bool, (a ^^ b) = (d ^^ e) → ((a ^^ d) ^^ b) = e
        by decide) _ _ _ _ h

def arrow (p q d : Bool) : Arrow S (kernel p) (kernel q) where
  rel := phaseRel p q d
  exact := phaseRel_exact p q d
  left := by rw [← phaseRel_zero,phaseRel_comp,Bool.false_xor]
  right := by rw [← phaseRel_zero,phaseRel_comp,Bool.xor_false]
  source := by rw [phaseRel_converse,phaseRel_comp,Bool.xor_self,phaseRel_zero]
  target := by rw [phaseRel_converse,phaseRel_comp,Bool.xor_self,phaseRel_zero]

/-- Exhaustion of EVERY full exact Arrow between EVERY pair of lambda
parents: the complete transported groupoid, with no selected-arrow premise. -/
theorem arrow_exhaustive (p q : Bool) (R : Arrow S (kernel p) (kernel q)) :
    ∃ d : Bool, R = arrow p q d := by
  let x := point p 0 false
  obtain ⟨y,hxy⟩ := R.exact.serial S (Prefix.homogeneous .first) x
  exact ⟨x.val.bit ^^ y.val.bit,
    R.eq_of_common_real_pair (Prefix.homogeneous .first) _ hxy rfl⟩

theorem arrow_injective (p q : Bool) : Function.Injective (arrow p q) := by
  intro d e he
  have hd : (arrow p q d).rel (point p 0 false) (point q 0 d) := by
    change (false ^^ d) = d
    simp
  rw [he] at hd
  simpa [arrow,phaseRel,point] using hd

noncomputable def fullArrowEquiv (p q : Bool) : Bool ≃ Arrow S (kernel p) (kernel q) :=
  Equiv.ofBijective (arrow p q) ⟨arrow_injective p q,fun R => by
    obtain ⟨d,hd⟩ := arrow_exhaustive p q R
    exact ⟨d,hd.symm⟩⟩

theorem calculus : ExactCalculus S := exactCalculus_of_homogeneous_CCO S
  (Prefix.homogeneous .first) (Prefix.semanticCCO .first)

theorem arrow_comp (p q r d e : Bool) :
    (arrow p q d).comp calculus (arrow q r e) = arrow p r (d ^^ e) :=
  Arrow.ext (phaseRel_comp p q r d e)

noncomputable def character {p q : Bool} (R : Arrow S (kernel p) (kernel q)) : Bool :=
  (fullArrowEquiv p q).symm R

@[simp] theorem character_arrow (p q d : Bool) : character (arrow p q d) = d :=
  (fullArrowEquiv p q).symm_apply_apply d

theorem character_comp {p q r : Bool} (R : Arrow S (kernel p) (kernel q))
    (T : Arrow S (kernel q) (kernel r)) :
    character (R.comp calculus T) = (character R ^^ character T) := by
  obtain ⟨d,rfl⟩ := arrow_exhaustive p q R
  obtain ⟨e,rfl⟩ := arrow_exhaustive q r T
  rw [arrow_comp,character_arrow,character_arrow,character_arrow]

theorem character_id (p : Bool) : character (Arrow.id (kernel p)) = false := by
  have hh : Arrow.id (kernel p) = arrow p p false := Arrow.ext (phaseRel_zero p).symm
  rw [hh,character_arrow]

/-- The same global mu=bit reads the character on the ENTIRE full groupoid. -/
theorem mu_character {p q : Bool} (R : Arrow S (kernel p) (kernel q))
    (x : Carrier p) (y : Carrier q) (h : R.rel x y) :
    (x.val.bit ^^ y.val.bit) = character R := by
  obtain ⟨d,rfl⟩ := arrow_exhaustive p q R
  rw [character_arrow]
  exact h

theorem selected_s_odd (p : Bool) : character (arrow p p true) = true :=
  character_arrow p p true

theorem s_is_entire_odd (p : Bool) :
    S.atomRel (atom p p true) = (arrow p p true).rel := by
  funext x y
  apply propext
  rw [atom_iff]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_,h⟩
    intro hb
    have hx : (x.val.bit ^^ x.val.block.2) = p := x.property
    have hy : (y.val.bit ^^ y.val.block.2) = p := y.property
    have hseed := congrArg Prod.snd hb
    rw [← hseed] at hy
    have he : x.val.bit = y.val.bit :=
      (show ∀ a b c p : Bool, (a ^^ c) = p → (b ^^ c) = p → a = b by decide)
        _ _ _ _ hx hy
    change (x.val.bit ^^ y.val.bit) = true at h
    rw [he,Bool.xor_self] at h
    exact Bool.false_ne_true h

@[instance_reducible] noncomputable def fullGroupoid : CategoryTheory.Groupoid Bool where
  Hom p q := Arrow S (kernel p) (kernel q)
  id p := Arrow.id (kernel p)
  comp R T := R.comp calculus T
  id_comp R := Arrow.id_comp calculus R
  comp_id R := Arrow.comp_id calculus R
  assoc R T U := Arrow.comp_assoc calculus R T U
  inv R := R.inv
  inv_comp R := Arrow.inv_comp calculus R
  comp_inv R := Arrow.comp_inv calculus R

/-- The standard character API, on the complete actual cross-parent groupoid. -/
noncomputable def fullCharacter :
    letI := fullGroupoid
    CCO.RigidGroupoid.Phase.Abstract.Character Bool := by
  letI := fullGroupoid
  exact {
    value := fun {p q} R => if character (p := p) (q := q) R then 1 else 0
    map_id := fun p => by change (if character (Arrow.id (kernel p)) then _ else _) = 0; rw [character_id]; rfl
    map_comp := by
      intro p q r R T
      change (if character (R.comp calculus T) then _ else _) = _
      rw [character_comp]
      cases character R <;> cases character T <;> decide }

theorem fullCharacter_selected_s (p : Bool) :
    letI := fullGroupoid
    fullCharacter.value (arrow p p true) = 1 := by
  change (if character (arrow p p true) then _ else _) = 1
  rw [character_arrow]
  rfl

theorem mu_fullCharacter {p q : Bool} (R : Arrow S (kernel p) (kernel q))
    (x : Carrier p) (y : Carrier q) (h : R.rel x y) :
    letI := fullGroupoid
    (if y.val.bit then (1 : ZMod 2) else 0) =
      (if x.val.bit then 1 else 0) + fullCharacter.value R := by
  change (if y.val.bit then (1 : ZMod 2) else 0) =
    (if x.val.bit then 1 else 0) + (if character R then 1 else 0)
  rw [← mu_character R x y h]
  cases x.val.bit <;> cases y.val.bit <;> decide

def sheet (p : Bool) : ColourEq S (parentSort p) :=
  ⟨(kernel p).setoid,Exact.colourInvariant S (Prefix.homogeneous .first) (kernel p).exact⟩

private theorem sPow (p : Bool) (n : Nat) (x y : Carrier p)
    (h : relPow (S.atomRel (atom p p true)) n x y) :
    (x.val.bit ^^ y.val.bit) = gain n := by
  induction n generalizing x with
  | zero =>
    change x = y at h
    subst y
    exact Bool.xor_self _
  | succ n ih =>
    obtain ⟨z,hxz,hzy⟩ := h
    rw [s_is_entire_odd] at hxz
    have hi := ih z hzy
    change (x.val.bit ^^ y.val.bit) = (true ^^ gain n)
    rw [← hi]
    exact (show ∀ a b c : Bool, (a ^^ b) = true → (a ^^ c) = (true ^^ (b ^^ c))
      by decide) _ _ _ hxz

theorem s_no_odd_closed (p : Bool) (x : Carrier p) (n : Nat) (hn : Odd n) :
    ¬ relPow (S.atomRel (atom p p true)) n x x := by
  intro h
  have hh := sPow p n x x h
  rw [gain_odd hn,Bool.xor_self] at hh
  exact Bool.false_ne_true hh

theorem s_even_iff (p : Bool) (x y : Carrier p) :
    EvenWalk (S.atomRel (atom p p true)) x y ↔ sheet p x y := by
  constructor
  · rintro ⟨n,hn,hxy⟩
    have hh := sPow p n x y hxy
    rw [gain_even hn] at hh
    exact (show ∀ a b : Bool, (a ^^ b) = false → a = b by decide) _ _ hh
  · intro hxy
    let z := point p 0 (!x.val.bit)
    have hxz : S.atomRel (atom p p true) x z := by
      rw [s_is_entire_odd]
      change (x.val.bit ^^ !x.val.bit) = true
      cases x.val.bit <;> rfl
    have hzy : S.atomRel (atom p p true) z y := by
      rw [s_is_entire_odd]
      change ((!x.val.bit) ^^ y.val.bit) = true
      change x.val.bit = y.val.bit at hxy
      rw [← hxy]
      cases x.val.bit <;> rfl
    exact ⟨2,by decide,z,hxz,y,hzy,rfl⟩

theorem s_connected_iff (p : Bool) (x y : Carrier p) :
    ConnectedWalk (S.atomRel (atom p p true)) x y ↔ True := by
  constructor
  · exact fun _ => trivial
  · intro _
    by_cases hp : x.val.bit = y.val.bit
    · obtain ⟨n,_,hn⟩ := (s_even_iff p x y).mpr hp
      exact ⟨n,hn⟩
    · refine ⟨1,(relPow_one _ _ _).mpr ?_⟩
      rw [s_is_entire_odd]
      exact (show ∀ a b : Bool, a ≠ b → (a ^^ b) = true by decide) _ _ hp

theorem s_even_eq (p : Bool) :
    evenColourEq S (Prefix.homogeneous .first) (atom p p true) = sheet p := by
  apply ColourEq.ext
  exact s_even_iff p

theorem s_connected_eq (p : Bool) :
    connectivityColourEq S (Prefix.homogeneous .first) (atom p p true) = ⊤ := by
  apply ColourEq.ext
  exact s_connected_iff p

theorem s_index_two (p : Bool) (x : Carrier p) :
    relativeIndex (sheet p).val (⊤ : ColourEq S (parentSort p)).val x = 2 := by
  rw [← s_even_eq,← s_connected_eq]
  exact parity_seed_index_two S (Prefix.homogeneous .first) (atom p p true) (s_no_odd_closed p) x

theorem sheet_maximal (p : Bool) :
    Maximal (Candidate S (sheet p) ⊤) (sheet p) := by
  refine ⟨⟨(kernel p).exact,le_rfl,inf_top_eq _⟩,?_⟩
  intro E hE _
  have he : E = sheet p := (inf_top_eq E).symm.trans hE.2.2
  exact he ▸ le_rfl

/-- The next s-pivot gate is ACTUALLY maximal at every lambda parent. -/
noncomputable def maximalGate (p : Bool) :
    MaximalGate S (Prefix.homogeneous .first) (sheet p) ⊤ := by
  have hOdd : Exact S (i := parentSort p) (odd (sheet p).val (⊤ : ColourEq S (parentSort p)).val) := by
    have hRel : odd (sheet p).val (⊤ : ColourEq S (parentSort p)).val = phaseRel p p true := by
      funext x y
      apply propext
      change (True ∧ ¬ x.val.bit = y.val.bit) ↔ (x.val.bit ^^ y.val.bit) = true
      cases x.val.bit <;> cases y.val.bit <;> decide
    rw [hRel]
    exact phaseRel_exact p p true
  exact Classical.choice (exists_maximalGate S (Prefix.homogeneous .first)
    (Prefix.semanticCCO .first) (sheet p) ⊤ (kernel p).exact le_top hOdd
      (point p 0 false) (s_index_two p (point p 0 false)))

theorem maximalGate_kernel (p : Bool) : (maximalGate p).kernel = sheet p :=
  (inf_top_eq _).symm.trans (maximalGate p).maximal.1.2.2

def reached (p : Bool) : Reached S (kernel false) :=
  ⟨parentSort p,⟨(arrow false p false).toBridge⟩⟩

/-- All actual named parents are reached; there are no omitted components. -/
def reachedEquiv : Reached S (kernel false) ≃ Bool where
  toFun b := b.val.2
  invFun := reached
  left_inv := by
    rintro ⟨⟨i,p⟩,h⟩
    cases i
    rfl
  right_inv := fun _ => rfl

/-- Every full bridge to the parent has exactly the displayed S target
kernel. Thus the full groupoid above exhausts the actual reached geometry. -/
theorem every_bridge_kernel (p q : Bool) (R : Bridge S (kernel p) (parentSort q)) :
    R.targetKernel (Prefix.homogeneous .first) calculus = kernel q := by
  have hh := bridge_targetKernel_unique S (Prefix.homogeneous .first) calculus
    R (arrow p q false).toBridge
  refine hh.trans ?_
  apply kernel_ext S
  apply Setoid.ext
  intro x y
  exact Iff.of_eq (congrFun (congrFun (arrow p q false).target x) y)

theorem reached_kernel (p : Bool) :
    Reached.kernel (Prefix.homogeneous .first) calculus (reached p) = kernel p :=
  every_bridge_kernel false p (Reached.bridge (reached p))

/-- The actual S quotient of every lambda parent has exactly its two bits. -/
noncomputable def quotientEquiv (p : Bool) : (kernel p).Class ≃ Bool where
  toFun := Quotient.lift (fun x : Carrier p => x.val.bit) (fun _ _ h => h)
  invFun b := (kernel p).project (point p 0 b)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x => exact Quotient.sound rfl
  right_inv := fun _ => rfl

theorem arrow_quotient (p q d : Bool) (x : (kernel p).Class) :
    quotientEquiv q ((arrow p q d).quotientMap (Prefix.homogeneous .first) x) =
      (quotientEquiv p x ^^ d) := by
  induction x using Quotient.inductionOn with
  | _ x =>
    let y := point q 0 (x.val.bit ^^ d)
    have h : (arrow p q d).rel x y := by
      change (x.val.bit ^^ (x.val.bit ^^ d)) = d
      cases x.val.bit <;> cases d <;> rfl
    change quotientEquiv q ((arrow p q d).quotientMap (Prefix.homogeneous .first)
      ((kernel p).project x)) = _
    rw [(arrow p q d).quotientMap_eq_iff (Prefix.homogeneous .first) x y |>.mpr h]
    rfl

/-- There is no omitted functional bijection between the two-point actual
S quotients: even every set bijection is one of the full exact arrows. -/
theorem every_quotient_bijection (p q : Bool) (e : (kernel p).Class ≃ (kernel q).Class) :
    ∃ d : Bool, e = (arrow p q d).quotientEquiv (Prefix.homogeneous .first) := by
  let f : Equiv.Perm Bool := (quotientEquiv p).symm.trans (e.trans (quotientEquiv q))
  have hf (b : Bool) : f b = (b ^^ f false) := by
    have hi : f true ≠ f false := fun h => Bool.false_ne_true (f.injective h).symm
    cases b
    · simp
    · exact (show ∀ a b : Bool, a ≠ b → a = (true ^^ b) by decide) _ _ hi
  refine ⟨f false,?_⟩
  apply Equiv.ext
  intro x
  apply (quotientEquiv q).injective
  change quotientEquiv q (e x) =
    quotientEquiv q ((arrow p q (f false)).quotientMap (Prefix.homogeneous .first) x)
  rw [arrow_quotient]
  simpa only [f,Equiv.trans_apply,Equiv.symm_apply_apply] using hf (quotientEquiv p x)

end LambdaPhase

namespace FirstMaximal

def kernel : Kernel source () := ⟨sheetEq.val,sheet_exact⟩
def rel (d : Bool) (x y : Point) : Prop := (x.bit ^^ y.bit) = d

theorem rel_zero : rel false = kernel.rel := by
  funext x y
  apply propext
  change (x.bit ^^ y.bit) = false ↔ x.bit = y.bit
  cases x.bit <;> cases y.bit <;> decide

theorem rel_one_gate : rel true = gate source sheetEq blockEq cloneEq := by
  funext x y
  apply propext
  constructor
  · intro h
    let v : Point := ⟨x.block,!x.bit,0⟩
    have hp : (!x.bit) = y.bit :=
      (show ∀ a b : Bool, (a ^^ b) = true → (!a) = b by decide) _ _ h
    refine ⟨v,⟨x,rfl,⟨rfl,?_⟩⟩,hp⟩
    intro hk
    have hh := congrArg Prod.snd hk
    change x.bit = !x.bit at hh
    exact (show ∀ b : Bool, b ≠ !b by decide) x.bit hh
  · rintro ⟨v,⟨u,hxu,huv⟩,hvy⟩
    have hn : u.bit ≠ v.bit := by
      intro hp
      exact huv.2 (Prod.ext huv.1 hp)
    change x.bit = u.bit at hxu
    change v.bit = y.bit at hvy
    change (x.bit ^^ y.bit) = true
    rw [hxu,← hvy]
    exact (show ∀ a b : Bool, a ≠ b → (a ^^ b) = true by decide) _ _ hn

theorem rel_exact (d : Bool) : FullExact source (i := ()) (j := ()) (rel d) := by
  cases d with
  | false => rw [rel_zero]; exact kernel.exact
  | true =>
    rw [rel_one_gate]
    have hh := firstMaximalGate.exact
    rw [firstMaximalGate_kernel] at hh
    exact hh

theorem rel_converse (d : Bool) :
    TRel.converse (X := fun _ : Unit => Point) (i := ()) (j := ()) (rel d) = rel d := by
  funext x y
  apply propext
  exact congrArg (· = d) (Bool.xor_comm y.bit x.bit) |>.to_iff

theorem rel_comp (d e : Bool) :
    TRel.comp (X := fun _ : Unit => Point) (i := ()) (j := ()) (k := ())
      (rel d) (rel e) = rel (d ^^ e) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z,hxz,hzy⟩
    change (x.bit ^^ y.bit) = (d ^^ e)
    calc
      _ = ((x.bit ^^ z.bit) ^^ (z.bit ^^ y.bit)) := by
        cases x.bit <;> cases z.bit <;> cases y.bit <;> rfl
      _ = _ := by rw [hxz,hzy]
  · intro h
    let z : Point := ⟨(0,false),x.bit ^^ d,0⟩
    refine ⟨z,?_,?_⟩
    · change (x.bit ^^ (x.bit ^^ d)) = d
      cases x.bit <;> cases d <;> rfl
    · change ((x.bit ^^ d) ^^ y.bit) = e
      exact (show ∀ a b d e : Bool, (a ^^ b) = (d ^^ e) → ((a ^^ d) ^^ b) = e
        by decide) _ _ _ _ h

def arrow (d : Bool) : Arrow source kernel kernel where
  rel := rel d
  exact := rel_exact d
  left := by rw [← rel_zero,rel_comp,Bool.false_xor]
  right := by rw [← rel_zero,rel_comp,Bool.xor_false]
  source := by rw [rel_converse,rel_comp,Bool.xor_self,rel_zero]
  target := by rw [rel_converse,rel_comp,Bool.xor_self,rel_zero]

theorem arrow_exhaustive (R : Arrow source kernel kernel) : ∃ d : Bool, R = arrow d := by
  let x : Point := default
  obtain ⟨y,hxy⟩ := R.exact.serial source homogeneous x
  exact ⟨x.bit ^^ y.bit,R.eq_of_common_real_pair homogeneous _ hxy rfl⟩

theorem arrow_injective : Function.Injective arrow := by
  intro d e h
  let x : Point := ⟨(0,false),false,0⟩
  let y : Point := ⟨(0,false),d,0⟩
  have hd : (arrow d).rel x y := by change (false ^^ d) = d; simp
  rw [h] at hd
  simpa [arrow,rel,x,y] using hd

noncomputable def fullArrowEquiv : Bool ≃ Arrow source kernel kernel :=
  Equiv.ofBijective arrow ⟨arrow_injective,fun R => by
    obtain ⟨d,hd⟩ := arrow_exhaustive R
    exact ⟨d,hd.symm⟩⟩

noncomputable def character (R : Arrow source kernel kernel) : Bool := fullArrowEquiv.symm R

@[simp] theorem character_arrow (d : Bool) : character (arrow d) = d :=
  fullArrowEquiv.symm_apply_apply d

theorem arrow_comp (d e : Bool) :
    (arrow d).comp calculus (arrow e) = arrow (d ^^ e) := Arrow.ext (rel_comp d e)

theorem character_comp (R T : Arrow source kernel kernel) :
    character (R.comp calculus T) = (character R ^^ character T) := by
  obtain ⟨d,rfl⟩ := arrow_exhaustive R
  obtain ⟨e,rfl⟩ := arrow_exhaustive T
  rw [arrow_comp,character_arrow,character_arrow,character_arrow]

/-- The actual first-maximal bit marking uses the whole quotient character. -/
theorem bit_character (R : Arrow source kernel kernel) (x y : Point) (h : R.rel x y) :
    (x.bit ^^ y.bit) = character R := by
  obtain ⟨d,rfl⟩ := arrow_exhaustive R
  rw [character_arrow]
  exact h

theorem selected_gate_odd : character (arrow true) = true := character_arrow true

theorem character_id : character (Arrow.id kernel) = false := by
  have h : Arrow.id kernel = arrow false := Arrow.ext rel_zero.symm
  rw [h,character_arrow]

noncomputable def fullCharacter :
    letI := isotropyGroupoid kernel
    CCO.RigidGroupoid.Phase.Abstract.Character Unit := by
  letI := isotropyGroupoid kernel
  exact {
    value := fun R => if character R then 1 else 0
    map_id := fun _ => by change (if character (Arrow.id kernel) then _ else _) = 0; rw [character_id]; rfl
    map_comp := by
      intro p q r R T
      change (if character (R.comp calculus T) then _ else _) = _
      rw [character_comp]
      cases character R <;> cases character T <;> decide }

theorem bit_fullCharacter (R : Arrow source kernel kernel) (x y : Point) (h : R.rel x y) :
    letI := isotropyGroupoid kernel
    (if y.bit then (1 : ZMod 2) else 0) =
      (if x.bit then 1 else 0) + fullCharacter.value (a := ()) (b := ()) R := by
  change (if y.bit then (1 : ZMod 2) else 0) =
    (if x.bit then 1 else 0) + (if character R then 1 else 0)
  rw [← bit_character R x y h]
  cases x.bit <;> cases y.bit <;> decide

end FirstMaximal

namespace MaximalSplit

abbrev β (_ : Unit) := Bool
abbrev Child := APCharacter.Rank.Child β
abbrev Carrier := APCharacter.Rank.Point β (fun _ (x : Point) => x.bit)
abbrev parentSort (p : Bool) : Child := ⟨(),p⟩

def point (p : Bool) (b : Block) (k : Nat) : Carrier (parentSort p) := ⟨⟨b,p,k⟩,rfl⟩

theorem inhabited (c : Child) : Nonempty (Carrier c) := by
  rcases c with ⟨i,p⟩
  cases i
  exact ⟨point p (0,false) 0⟩

/-- The actual first-maximal S expansion of the SAME original source. -/
noncomputable def source : AtomicSource Child Carrier :=
  APCharacter.Rank.source NonmaximalBoundary.source β (fun _ (x : Point) => x.bit) inhabited

theorem label_kernel : Setoid.ker Point.bit = firstMaximalGate.kernel.val := by
  rw [firstMaximalGate_kernel]
  rfl

theorem colour_map {c d : Child} (x : Carrier c) (y : Carrier d) :
    (source.colour x y).map Subtype.val = colour x.val y.val :=
  APCharacter.Rank.colour_map NonmaximalBoundary.source β (fun _ (x : Point) => x.bit) x y

/-- Exact support of the actual two-label source, with real old witnesses. -/
theorem table_iff_actual (a : Atom) (p q : Bool) : maximalTable a p q ↔
    ∃ x : Carrier (parentSort p), ∃ y : Carrier (parentSort q), colour x.val y.val = some a := by
  constructor
  · intro h
    let x := point p (0,false) 0
    let y := point q (if a.1 then 0 else 1,false) 1
    refine ⟨x,y,(NonmaximalBoundary.colour_some _ _ a).mpr ⟨?_,?_⟩⟩
    · intro he
      have hh := congrArg Point.clone he
      change (0 : Nat) = 1 at hh
      cases hh
    · apply Prod.ext
      · change decide ((0,false) = (if a.1 then 0 else 1,false)) = a.1
        exact (show ∀ b : Bool, decide (((0 : Nat),false) = (if b then 0 else 1,false)) = b
          by decide) a.1
      · exact h
  · rintro ⟨x,y,h⟩
    have hh := congrArg Prod.snd ((NonmaximalBoundary.colour_some _ _ a).mp h).2
    change (x.val.bit ^^ y.val.bit) = a.2 at hh
    change (p ^^ q) = a.2
    have hx : x.val.bit = p := x.property
    have hy : y.val.bit = q := y.property
    simpa only [hx,hy] using hh

/-- The core assertion concerns the ACTUAL old-atom support table. -/
theorem endomorphism_injective (f : Bool → Bool)
    (hf : ∀ a p q, (∃ x : Carrier (parentSort p), ∃ y : Carrier (parentSort q),
      colour x.val y.val = some a) →
      ∃ x : Carrier (parentSort (f p)), ∃ y : Carrier (parentSort (f q)),
        colour x.val y.val = some a) : Function.Injective f := by
  apply maximal_endomorphism_injective f
  intro a p q h
  exact (table_iff_actual a (f p) (f q)).mpr (hf a p q ((table_iff_actual a p q).mp h))

noncomputable def blockCode : Block ≃ Nat := by
  letI := Denumerable.ofEncodableOfInfinite Block
  exact Denumerable.eqv Block

/-- Actual bit-parent points form infinitely many infinite clone fibres. -/
noncomputable def fixedEquiv (p : Bool) : Carrier (parentSort p) ≃ Nat × Nat where
  toFun x := (blockCode x.val.block,x.val.clone)
  invFun q := point p (blockCode.symm q.1) q.2
  left_inv := by
    intro x
    apply Subtype.ext
    apply (point_eq_iff _ _).mpr
    exact ⟨blockCode.symm_apply_apply _,x.property.symm,rfl⟩
  right_inv := by intro q; simp only [point,blockCode.apply_symm_apply]

private theorem fixed_colour (p : Bool) (x y : Nat × Nat) :
    colour ((fixedEquiv p).symm x).val ((fixedEquiv p).symm y).val =
      (Prefix.partitionColour x y).map (fun b => (b,false)) := by
  rcases x with ⟨n,k⟩
  rcases y with ⟨m,l⟩
  have hcode : blockCode.symm n = blockCode.symm m ↔ n = m := blockCode.symm.injective.eq_iff
  by_cases hn : n = m <;> by_cases hk : k = l <;>
    simp [colour,pattern,fixedEquiv,point,Prefix.partitionColour,Point.mk.injEq,
      Prod.mk.injEq,hcode,hn,hk]

theorem full_equivalence_trichotomy (p : Bool) (E : ColourEq source (parentSort p)) :
    (∀ x y, E x y ↔ x = y) ∨
      (∀ x y, E x y ↔ (fixedEquiv p x).1 = (fixedEquiv p y).1) ∨ (∀ x y, E x y) := by
  let R : Setoid (Nat × Nat) := {
    r x y := E ((fixedEquiv p).symm x) ((fixedEquiv p).symm y)
    iseqv := ⟨fun _ => E.val.refl _,fun h => E.val.symm h,fun h k => E.val.trans h k⟩ }
  have hi : ∀ x y x' y', Prefix.partitionColour x y = Prefix.partitionColour x' y' →
      (R x y ↔ R x' y') := by
    intro x y x' y' h
    apply E.property
    apply Option.map_injective Subtype.val_injective
    rw [colour_map,colour_map,fixed_colour,fixed_colour,h]
  rcases Prefix.partition_classification R hi with he | he | he
  · left
    intro x y
    have hh := he (fixedEquiv p x) (fixedEquiv p y)
    change E ((fixedEquiv p).symm (fixedEquiv p x))
      ((fixedEquiv p).symm (fixedEquiv p y)) ↔ fixedEquiv p x = fixedEquiv p y at hh
    simpa only [Equiv.symm_apply_apply,(fixedEquiv p).injective.eq_iff] using hh
  · right; left
    intro x y
    have hh := he (fixedEquiv p x) (fixedEquiv p y)
    change E ((fixedEquiv p).symm (fixedEquiv p x))
      ((fixedEquiv p).symm (fixedEquiv p y)) ↔ (fixedEquiv p x).1 = (fixedEquiv p y).1 at hh
    simpa only [Equiv.symm_apply_apply] using hh
  · right; right
    intro x y
    have hh := he (fixedEquiv p x) (fixedEquiv p y)
    change E ((fixedEquiv p).symm (fixedEquiv p x))
      ((fixedEquiv p).symm (fixedEquiv p y)) at hh
    simpa only [Equiv.symm_apply_apply] using hh

theorem strict_index_infinite (p : Bool) (E F : ColourEq source (parentSort p))
    (hEF : E < F) (x : Carrier (parentSort p)) : Infinite (RelativeClass E.val F.val x) := by
  classical
  have fromSequence (f : Nat → Carrier (parentSort p))
      (hf : ∀ n, F x (f n)) (hsep : ∀ m n, E (f m) (f n) → m = n) :
      Infinite (RelativeClass E.val F.val x) := by
    let code : Nat → RelativeClass E.val F.val x := fun n => Quotient.mk _ ⟨f n,hf n⟩
    apply Infinite.of_injective code
    intro m n h
    have hh : (Setoid.comap (fun y : {y // F x y} => y.val) E.val)
        ⟨f m,hf m⟩ ⟨f n,hf n⟩ := Quotient.exact h
    exact hsep m n hh
  let clones (n : Nat) := (fixedEquiv p).symm ((fixedEquiv p x).1,n)
  let blocks (n : Nat) := (fixedEquiv p).symm (n,0)
  rcases full_equivalence_trichotomy p E with he | he | he
  · have hsep : ∀ m n, E (clones m) (clones n) → m = n := by
      intro m n h
      have hh := congrArg (fun y => (fixedEquiv p y).2) ((he _ _).mp h)
      simpa only [clones,Equiv.apply_symm_apply] using hh
    rcases full_equivalence_trichotomy p F with hf | hf | hf
    · exact False.elim (hEF.not_ge (fun a b hab => (he a b).mpr ((hf a b).mp hab)))
    · exact fromSequence clones (fun n => (hf _ _).mpr (by simp only [clones,Equiv.apply_symm_apply])) hsep
    · exact fromSequence clones (fun n => hf x (clones n)) hsep
  · rcases full_equivalence_trichotomy p F with hf | hf | hf
    · exact False.elim (hEF.not_ge (fun a b hab =>
        (he a b).mpr (congrArg (fun y => (fixedEquiv p y).1) ((hf a b).mp hab))))
    · exact False.elim (hEF.not_ge (fun a b hab => (he a b).mpr ((hf a b).mp hab)))
    · apply fromSequence blocks (fun n => hf x (blocks n))
      intro m n h
      simpa only [blocks,Equiv.apply_symm_apply] using (he _ _).mp h
  · exact False.elim (hEF.not_ge (fun a b _ => he a b))

/-- The ACTUAL first-maximal two-label source is already FULL-terminal. -/
theorem terminal (c : Child) (E F : ColourEq source c) (h : E ⋖ F) (x : Carrier c) :
    Infinite (RelativeClass E.val F.val x) := by
  rcases c with ⟨i,p⟩
  cases i
  exact strict_index_infinite p E F h.lt x

end MaximalSplit

end CCO.AutomaticEPCore.NonmaximalBoundary
