import CCO.StrongExact.SourceExactCalculus
import CCO.StrongExact.PathSupport

/-!
# C13: zero-free finite PC domains belong to the original exact family

A nonempty final domain witnesses nonemptiness at every earlier iterate.
Initial singleton/typed-Top domains are exact. Each update is a FINITE
intersection of an old domain and strong products of old exact domains;
C08 gives product closure and the nonempty evaluated result gives meet
closure. This route does not presume the C12 simple-path formula or the
reverse survivor inclusion it is intended to help support.
-/

universe u v w z
namespace CCO.StrongExact
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- Finite nonempty-evaluation meets remain in the ORIGINAL exact
family. The empty restriction list is retained as typed diversity Top. -/
theorem exact_meetMenus_of_nonempty (menus : List (S.Menu i j))
    (hExact : ∀ A ∈ menus, Exact S A)
    (hNonempty : (meetMenus S menus).Nonempty) :
    Exact S (meetMenus S menus) := by
  classical
  let words := menus.flatMap (wordsOfExact S)
  refine ⟨hNonempty,words,?_⟩
  ext a
  constructor
  · intro ha word hword
    obtain ⟨A,hA,hwA⟩ := List.mem_flatMap.mp hword
    have hMember : a ∈ A := ha A hA
    rw [wordsOfExact_spec S (hExact A hA)] at hMember
    exact hMember word hwA
  · intro ha A hA
    have hMember : a ∈ present S (wordsOfExact S A) := by
      intro word hword
      exact ha word (List.mem_flatMap.mpr ⟨A,hA,hword⟩)
    rw [← wordsOfExact_spec S (hExact A hA)] at hMember
    exact hMember

end CCO.StrongExact

namespace CCO.StrongPC
variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X} {V : Type z}
variable (D : PartialDiagram S V)

/-- The old initial domains are original singleton or typed-Top exact
menus, including source pairs with repeated named sorts. -/
theorem initial_exact_of_SAP
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S) (p : DistinctPair V) :
    StrongExact.Exact S (initial D p) := by
  cases he : D.edge p.src p.dst p.ne with
  | none =>
      change StrongExact.Exact S (match D.edge p.src p.dst p.ne with
        | none => Set.univ
        | some a => {a})
      rw [he]
      exact StrongExact.exact_top_of_SAP S H sap
  | some a =>
      change StrongExact.Exact S (match D.edge p.src p.dst p.ne with
        | none => Set.univ
        | some a => {a})
      rw [he]
      exact StrongExact.exact_singleton S a

/-- One synchronous finite PC update preserves original exactness
whenever its EVALUATED output domain is nonempty. -/
theorem step_exact_of_nonempty_of_SAP_CCO
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S)
    (N : Network D) (hN : ∀ p : DistinctPair V, StrongExact.Exact S (N p))
    (p : DistinctPair V) (hResult : (step D N p).Nonempty) :
    StrongExact.Exact S (step D N p) := by
  classical
  let : Finite V := D.finite_type
  let : Fintype V := Fintype.ofFinite V
  let Middle := {t : V // p.src ≠ t ∧ t ≠ p.dst}
  let thirds : List Middle := (Finset.univ : Finset Middle).toList
  let productAt (t : Middle) : S.Menu (D.vertexSort p.src) (D.vertexSort p.dst) :=
    S.product (N ⟨p.src,t.val,t.property.1⟩) (N ⟨t.val,p.dst,t.property.2⟩)
  let menus := N p :: thirds.map productAt
  have hExact : ∀ A ∈ menus, StrongExact.Exact S A := by
    intro A hA
    rcases List.mem_cons.mp hA with hEq | hRest
    · subst A
      exact hN p
    · obtain ⟨t,_ht,hEq⟩ := List.mem_map.mp hRest
      rw [← hEq]
      exact StrongExact.exact_product_of_SAP_CCO S H sap cco
        (hN ⟨p.src,t.val,t.property.1⟩) (hN ⟨t.val,p.dst,t.property.2⟩)
  have hEvaluate : StrongExact.meetMenus S menus = step D N p := by
    ext a
    constructor
    · intro ha
      refine ⟨ha (N p) (List.mem_cons_self),?_⟩
      intro t hst htd
      let mid : Middle := ⟨t,hst,htd⟩
      have hmid : mid ∈ thirds := by simp [thirds]
      exact ha (productAt mid)
        (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨mid,hmid,rfl⟩))
    · intro ha A hA
      rcases List.mem_cons.mp hA with hEq | hRest
      · subst A
        exact ha.1
      · obtain ⟨t,_ht,hEq⟩ := List.mem_map.mp hRest
        rw [← hEq]
        exact ha.2 t.val t.property.1 t.property.2
  have hMeetNonempty : (StrongExact.meetMenus S menus).Nonempty := by
    rw [hEvaluate]
    exact hResult
  have hMeet := StrongExact.exact_meetMenus_of_nonempty S menus hExact hMeetNonempty
  rw [hEvaluate] at hMeet
  exact hMeet

/-- Every stationary survivor already occurs in every earlier iterate. -/
theorem fixedNetwork_refines_each_iterate (n : Nat) :
    Refines D (fixedNetwork D) (iterate D (initial D) n) :=
  stable_refines_iterate D (fixedNetwork D) (initial D)
    (fixedNetwork_stable D) (fixedNetwork_refines_initial D) n

/-- A zero-free final fixed network provides actual witnesses of
nonemptiness of EVERY factor and evaluated result at EVERY earlier step. -/
theorem iterate_nonempty_of_nonempty_fixedNetwork
    (hAll : ∀ p : DistinctPair V, (fixedNetwork D p).Nonempty)
    (n : Nat) (p : DistinctPair V) :
    (iterate D (initial D) n p).Nonempty := by
  obtain ⟨a,ha⟩ := hAll p
  exact ⟨a,fixedNetwork_refines_each_iterate D n p ha⟩

/-- All earlier iterates are exact when the final network has no zero.
No path formula or actual survivor reverse inclusion is assumed. -/
theorem iterate_exact_of_nonempty_fixedNetwork
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S)
    (hAll : ∀ p : DistinctPair V, (fixedNetwork D p).Nonempty)
    (n : Nat) (p : DistinctPair V) :
    StrongExact.Exact S (iterate D (initial D) n p) := by
  induction n generalizing p with
  | zero => exact initial_exact_of_SAP D H sap p
  | succ n ih =>
      exact step_exact_of_nonempty_of_SAP_CCO D H sap cco
        (iterate D (initial D) n) ih p
        (iterate_nonempty_of_nonempty_fixedNetwork D hAll (n + 1) p)

/-- C13 forward original-family inclusion for every nonempty fixed
domain. All source providers are discharged from homogeneous SAP+CCO. -/
theorem fixedNetwork_exact_of_nonempty
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S)
    (hAll : ∀ p : DistinctPair V, (fixedNetwork D p).Nonempty)
    (p : DistinctPair V) : StrongExact.Exact S (fixedNetwork D p) :=
  iterate_exact_of_nonempty_fixedNetwork D H sap cco hAll (fixedIndex D) p

/-- In particular every canonical fixed domain of a genuinely strongly
completable finite diagram is an original exact menu. -/
theorem fixedNetwork_exact_of_strongCompletion
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S) (hD : D.HasStrongCompletion)
    (p : DistinctPair V) : StrongExact.Exact S (fixedNetwork D p) := by
  obtain ⟨f,hf⟩ := hD
  exact fixedNetwork_exact_of_nonempty D H sap cco
    (fixedNetwork_nonempty_of_completion D f hf) p

end CCO.StrongPC
