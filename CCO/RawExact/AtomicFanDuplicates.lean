import CCO.RawExact.AtomicFanCycles
import Mathlib.Tactic

/-!
# B002 C13: eliminate repeated centres in atomic RAW ball families

The actual semantic-CCO fan lemma requires its formal marked centres
to be injective. For an arbitrary finite family, choose the least
representative of each equality-class of actual TAGGED centres.
Pairwise intersections imply that any two requested atoms with the
same actual centre coincide: there is no fake equality edge and no
assumption of different original-sort labels. Thus deleting repeated
centres preserves exactly every requested ball. The finite
representative family has distinct centres and is handled by the
previous genuine semantic-CCO theorem.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Actual tagged centre and its requested, correctly typed diversity
atom. Logical equality is not an atom in this structure. -/
abbrev AtomicBallRequest (root : ι) :=
  Σ c : Sigma X, S.Atom root c.1

def requestSatisfied {root : ι} (x : X root)
    (r : AtomicBallRequest S root) : Prop :=
  S.colour x r.1.2 = some r.2

/-- If two atom balls have the same ACTUAL tagged centre and their
intersection contains a point, the atoms must literally coincide.
Consequently both requested labelled-centre pairs are equal. -/
theorem request_eq_of_same_centre_and_common_point
    {root : ι} (r s : AtomicBallRequest S root)
    (hCentre : r.1 = s.1)
    (hPair : ∃ x : X root,
      requestSatisfied S x r ∧ requestSatisfied S x s) :
    r = s := by
  rcases r with ⟨c, a⟩
  rcases s with ⟨d, b⟩
  cases hCentre
  obtain ⟨x, hxA, hxB⟩ := hPair
  change S.colour x c.2 = some a at hxA
  change S.colour x c.2 = some b at hxB
  have hab : a = b := Option.some.inj (hxA.symm.trans hxB)
  subst b
  rfl

/-- Genuine finite RAW atomic-ball Helly for an ARBITRARY finite
family, allowing repeated actual centres, repeated original sorts,
and an empty index family. Pairwise intersections include equal
indices, ensuring singleton balls are nonempty. The original
source supplies homogeneity and semantic CCO, nothing stronger. -/
theorem heterogeneous_atomic_ball_helly_with_repeats_of_CCO
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {I : Type (max u v)} [Finite I]
    (root : ι) (sort : I → ι)
    (centres : ∀ t : I, X (sort t))
    (atoms : ∀ t : I, S.Atom root (sort t))
    (hPair : ∀ a b : I, ∃ x : X root,
      S.atomRel (atoms a) x (centres a) ∧
      S.atomRel (atoms b) x (centres b)) :
    ∃ x : X root, ∀ t : I,
      S.atomRel (atoms t) x (centres t) := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  letI : LinearOrder I := LinearOrder.lift' e e.injective
  let tagged : I → Sigma X := fun t => ⟨sort t, centres t⟩
  let fibre (t : I) : Finset I :=
    Finset.univ.filter (fun k => tagged k = tagged t)
  have hfibre (t : I) : (fibre t).Nonempty := by
    refine ⟨t, ?_⟩
    simp [fibre]
  let rep (t : I) : I := (fibre t).min' (hfibre t)
  have hrep_tagged (t : I) : tagged (rep t) = tagged t := by
    have hmem := Finset.min'_mem (fibre t) (hfibre t)
    simpa only [fibre, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
  have hrep_const (a b : I) (hab : tagged a = tagged b) :
      rep a = rep b := by
    have hf : fibre a = fibre b := by
      unfold fibre
      rw [hab]
    have hInA : (fibre b).min' (hfibre b) ∈ fibre a := by
      rw [hf]
      exact Finset.min'_mem _ _
    have hInB : (fibre a).min' (hfibre a) ∈ fibre b := by
      rw [← hf]
      exact Finset.min'_mem _ _
    change (fibre a).min' (hfibre a) =
      (fibre b).min' (hfibre b)
    exact le_antisymm
      (Finset.min'_le _ _ hInA)
      (Finset.min'_le _ _ hInB)
  have hrep_idem (t : I) : rep (rep t) = rep t :=
    hrep_const (rep t) t (hrep_tagged t)
  let J : Type (max u v) := { t : I // rep t = t }
  have hInjective : Function.Injective
      (fun j : J => (⟨sort j.val, centres j.val⟩ : Sigma X)) := by
    intro j k hTagged
    apply Subtype.ext
    have hEq : rep j.val = rep k.val :=
      hrep_const j.val k.val hTagged
    exact j.property.symm.trans (hEq.trans k.property)
  have hPairJ : ∀ j k : J,
      ∃ x : X root,
        S.atomRel (atoms j.val) x (centres j.val) ∧
        S.atomRel (atoms k.val) x (centres k.val) := by
    intro j k
    exact hPair j.val k.val
  obtain ⟨x, hx⟩ :=
    heterogeneous_atomic_ball_helly_of_CCO S H cco
      root (fun j : J => sort j.val)
      (fun j : J => centres j.val)
      (fun j : J => atoms j.val)
      hInjective hPairJ
  refine ⟨x, ?_⟩
  intro t
  let j : J := ⟨rep t, hrep_idem t⟩
  obtain ⟨z, hzt, hzrep⟩ := hPair t (rep t)
  let request (t : I) : AtomicBallRequest S root :=
    ⟨tagged t, atoms t⟩
  have hRequestPair : ∃ z : X root,
      requestSatisfied S z (request t) ∧
      requestSatisfied S z (request (rep t)) :=
    ⟨z, hzt, hzrep⟩
  have hReq : request t = request (rep t) :=
    request_eq_of_same_centre_and_common_point S
      (request t) (request (rep t))
      (hrep_tagged t).symm hRequestPair
  have hSat : requestSatisfied S x (request (rep t)) := hx j
  rw [← hReq] at hSat
  exact hSat

end CCO.RawExact
