import CCO.OwnerTransversal.ClosedWalkFinite
import CCO.RawExact.QuotientExpansionWholeCycleClassification
import CCO.RawExact.QuotientExpansionCycleRealization
import CCO.RawExact.DiagramReindex

/-! One private word per marked pair.  The complete existing cycle
classification applies, while its two-distinct-path alternative is
impossible for singleton menus.  This is the combinatorial bridge used
by the anchored owner construction. -/
universe v w t
namespace CCO.OwnerTransversal
open ParityHasse.Original RawExact RawExact.QuotientExpansion

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable {n : Nat}

def networkSort : Fin n → Unit := fun _ => ()
def networkMenus (W : Edge n → Option (RawWord S () ())) :
    Menus S (networkSort (n := n)) := fun e => (W e).toList

def networkWord (W : Edge n → Option (RawWord S () ())) (e : Edge n) :
    RawWord S () () := (W e).getD (.nil ())

theorem network_word_mem (W : Edge n → Option (RawWord S () ()))
    (e : Edge n) (h : W e ≠ none) : networkWord S W e ∈ networkMenus S W e := by
  cases he : W e with
  | none => exact (h he).elim
  | some w => simp only [networkWord,networkMenus,he,Option.getD_some,Option.toList_some,
      List.mem_singleton]

theorem network_mem_eq (W : Edge n → Option (RawWord S () ()))
    (e : Edge n) (w : RawWord S () ()) (h : w ∈ networkMenus S W e) :
    W e ≠ none ∧ w = networkWord S W e := by
  cases he : W e with
  | none => simp only [networkMenus,he,Option.toList_none,List.not_mem_nil] at h
  | some u =>
      have hw : w = u := by simpa only [networkMenus,he,Option.toList_some,List.mem_singleton] using h
      exact ⟨by simp [he],by simpa only [networkWord,he,Option.getD_some] using hw⟩

theorem network_nonempty (W : Edge n → Option (RawWord S () ()))
    (h : ∀ e, W e ≠ none → TRel.Nonempty (RawWord.relation S (networkWord S W e))) :
    ∀ e, TRel.Nonempty (evaluate S (networkMenus S W e)) := by
  intro e
  by_cases he : W e = none
  · obtain ⟨x⟩ := S.nonemptySort ()
    refine ⟨x,x,?_⟩
    simp only [networkMenus,he,Option.toList_none,evaluate,List.not_mem_nil,false_implies,
      implies_true]
  · obtain ⟨x,y,hxy⟩ := h e he
    refine ⟨x,y,?_⟩
    intro w hw
    rw [(network_mem_eq S W e w hw).2]
    exact hxy

variable (W : Edge n → Option (RawWord S () ()))
variable (hne : ∀ e, W e ≠ none → TRel.Nonempty (RawWord.relation S (networkWord S W e)))
noncomputable abbrev networkDiagram := diagram S networkSort (networkMenus S W) (network_nonempty S W hne)

theorem network_used_nonempty (C : SimpleCycle (networkDiagram S W hne)) (e : Edge n)
    (h : CycleUsesEdge S networkSort (networkMenus S W) (network_nonempty S W hne) C e) :
    W e ≠ none := by
  obtain ⟨k,o,p,q,hpq,hp,hq,ho⟩ := h
  have hh := (network_mem_eq S W o.1 _ (List.get_mem _ o.2)).1
  simpa only [ho] using hh

theorem network_used_label (C : SimpleCycle (networkDiagram S W hne)) (e : Edge n) :
    CycleUsesEdge S networkSort (networkMenus S W) (network_nonempty S W hne) C e ↔
      CyclicSuppression.LabelOn
        (initialCycle S networkSort (networkMenus S W) (network_nonempty S W hne) C) e := by
  constructor
  · rintro ⟨k,o,p,q,hpq,hp,hq,ho⟩
    exact ⟨k,(initial_label_of_path_witness S networkSort (networkMenus S W)
      (network_nonempty S W hne) C k o p q hpq hp hq).trans ho⟩
  · rintro ⟨k,hk⟩
    obtain ⟨p,q,hpq,hp,hq⟩ := cycleOccurrence_spec S networkSort (networkMenus S W)
      (network_nonempty S W hne) C k
    exact ⟨k,_,p,q,hpq,hp,hq,hk⟩

/-- C06's whole-cycle bridge: there are no two distinct occurrences
on one marked pair; every expanded simple cycle has a genuine marked
simple cycle, retaining ALL used edge labels. -/
theorem network_cycle_projection (C : SimpleCycle (networkDiagram S W hne)) :
    Nonempty (MarkedProjection S networkSort (networkMenus S W)
      (network_nonempty S W hne) C) := by
  rcases cycle_two_whole_paths_or_marked_projection S networkSort (networkMenus S W)
      (network_nonempty S W hne) C with hTwo | hProjection
  · obtain ⟨e,a,b,ha,hb,hab,_⟩ := hTwo
    apply False.elim
    apply hab
    obtain ⟨ea,ia⟩ := a
    obtain ⟨eb,ib⟩ := b
    dsimp only at ha hb
    subst ea
    subst eb
    have hlen : (networkMenus S W e).length ≤ 1 := by
      cases he : W e <;> simp [networkMenus,he]
    have hi : ia.val = ib.val := by
      have hi := ia.isLt
      have hj := ib.isLt
      omega
    exact congrArg (Sigma.mk e) (Fin.ext hi)
  · exact hProjection

include H in
theorem network_word_invariant (e : Edge n) :
    ColourInvariant S () (RawWord.relation S (networkWord S W e)) :=
  groupInvariant_colourInvariant S H (word_invariant_of_homogeneous S H _)

include H in
/-- Actual owner data realise every marked cycle: a cycle containing an
E-word uses saturated owner walking; all remaining cycles use the single
raw base homomorphism. No triangle-only check occurs here. -/
theorem network_marked_realization (E : ColourEq S ())
    (owner base : Fin n → M)
    (hOwner : ∀ e, W e ≠ none →
      ownerSaturate E.val (RawWord.relation S (networkWord S W e))
        (owner (left e)) (owner (right e)))
    (hBase : ∀ e, W e ≠ none → RawWord.relation S (networkWord S W e) ≠ E.val.r →
      RawWord.relation S (networkWord S W e) (base (left e)) (base (right e)))
    (C : SimpleCycle (networkDiagram S W hne)) :
    ∃ b : Fin n → M, ∀ e,
      CycleUsesEdge S networkSort (networkMenus S W) (network_nonempty S W hne) C e →
      evaluate S (networkMenus S W e) (b (left e)) (b (right e)) := by
  classical
  obtain ⟨P⟩ := network_cycle_projection S W hne C
  let R : Fin P.length → Relation M := fun k => RawWord.relation S (networkWord S W (P.edges k))
  have used (k : Fin P.length) :
      CycleUsesEdge S networkSort (networkMenus S W) (network_nonempty S W hne) C (P.edges k) :=
    (network_used_label S W hne C _).mpr ((P.labels_iff _).mpr ⟨k,rfl⟩)
  have inv (k : Fin P.length) : ColourInvariant S () (R k) :=
    network_word_invariant S H W (P.edges k)
  have hs (k : Fin P.length) : ∀ x y, R k x y → R k y x :=
    colourInvariant_symmetric S (inv k)
  by_cases hasE : ∃ k, R k = E.val.r
  · have hInv : ∀ T ∈ List.ofFn R, ColourInvariant S () T := by
      intro T hT
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hT
      exact inv k
    have hE : E.val.r ∈ List.ofFn R := by
      obtain ⟨k,hk⟩ := hasE
      exact List.mem_ofFn.mpr ⟨k,hk⟩
    let own : Fin P.length → M := fun k => owner (P.vertices k)
    have hCycle : ∀ k, ownerSaturate E.val (R k) (own k)
        (own (cyclicNext P.length_pos k)) := by
      intro k
      have hh := hOwner (P.edges k) (network_used_nonempty S W hne C _ (used k))
      rcases P.endpoints k with ⟨hl,hr⟩ | ⟨hl,hr⟩
      · simpa only [own,R,hl,hr] using hh
      · change ownerSaturate E.val (R k) (owner (P.vertices k))
          (owner (P.vertices (cyclicNext P.length_pos k)))
        rw [hl,hr]
        obtain ⟨z,⟨u,hlu,hur⟩,hzr⟩ := hh
        exact ⟨u,⟨z,E.val.symm hzr,hs k _ _ hur⟩,E.val.symm hlu⟩
    have hProd : relationProduct (List.ofFn (fun k => ownerSaturate E.val (R k)))
        (own ⟨0,P.length_pos⟩) (own ⟨0,P.length_pos⟩) :=
      product_of_cyclic_points P.length_pos _ own hCycle
    have hSat : saturatedProduct E.val (List.ofFn R)
        (own ⟨0,P.length_pos⟩) (own ⟨0,P.length_pos⟩) := by
      apply product_le_saturatedProduct E.val (List.ofFn R)
      simpa only [List.map_ofFn,Function.comp_def] using hProd
    have hLoop := closed_owner_walk S H E (List.ofFn R) hInv hE _ hSat
    obtain ⟨p,hp⟩ := cyclic_points_of_product P.length_pos R _
      (hLoop (Classical.choice (S.nonemptySort ())))
    let b : Fin n → M := fun m =>
      if hm : ∃ k, P.vertices k = m then p hm.choose else base m
    have hb (k : Fin P.length) : b (P.vertices k) = p k := by
      dsimp only [b]
      rw [dif_pos ⟨k,rfl⟩]
      congr 1
      apply P.vertices.injective
      exact (Exists.choose_spec (p := fun j => P.vertices j = P.vertices k) ⟨k,rfl⟩)
    refine ⟨b,?_⟩
    intro e he w hw
    obtain ⟨k,hk⟩ := (P.labels_iff e).mp ((network_used_label S W hne C e).mp he)
    have hw' := (network_mem_eq S W e w hw).2
    rw [hw',← hk]
    rcases P.endpoints k with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · rw [← hl,← hr,hb,hb]
      exact hp k
    · rw [← hr,← hl,hb,hb]
      exact hs k _ _ (hp k)
  · refine ⟨base,?_⟩
    intro e he w hw
    have hw' := (network_mem_eq S W e w hw).2
    rw [hw']
    apply hBase e (network_used_nonempty S W hne C e he)
    intro hEq
    obtain ⟨k,hk⟩ := (P.labels_iff e).mp ((network_used_label S W hne C e).mp he)
    exact hasE ⟨k,by simpa only [R,hk] using hEq⟩

include H in
/-- CCO completes the WHOLE private expansion, after its genuine simple
cycles have all been realised. -/
theorem network_completion (cco : SemanticCCO.{0,v,0,w} S)
    (E : ColourEq S ()) (owner base : Fin n → M)
    (hPositive : ∀ e, W e ≠ none → 0 < diversityLength S (networkWord S W e))
    (hOwner : ∀ e, W e ≠ none → ownerSaturate E.val
      (RawWord.relation S (networkWord S W e)) (owner (left e)) (owner (right e)))
    (hBase : ∀ e, W e ≠ none → RawWord.relation S (networkWord S W e) ≠ E.val.r →
      RawWord.relation S (networkWord S W e) (base (left e)) (base (right e))) :
    Nonempty (DiagramHom (networkDiagram S W hne)) := by
  apply semanticCCO_change_universe S cco
  intro C
  obtain ⟨b,hb⟩ := network_marked_realization S H W hne E owner base hOwner hBase C
  apply cycleHom_of_marked_edge_realization S networkSort (networkMenus S W)
    (network_nonempty S W hne) C b hb
  intro o
  obtain ⟨hne,heq⟩ := network_mem_eq S W o.1 _ (List.get_mem _ o.2)
  change 0 < diversityLength S ((networkMenus S W o.1).get o.2)
  rw [heq]
  exact hPositive o.1 hne

end CCO.OwnerTransversal
