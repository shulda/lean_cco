import CCO.RealHull.Geometry.FibreSource

/-! The original square intersection is the EXACT actually occurring fibre
palette. A second point is built over the same complete actual anchor plus
the first real point. No globalisation or SAP is involved. -/

universe v w t
namespace CCO.RealHull.Geometry

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable [DecidableEq M] (A : Finset M) (q : ↥A → Atom S)
variable {G : Type t} [Group G] [MulAction G M]

theorem fibre_pair_realize (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,0,w} S)
    [Nonempty (FibreSet S A q)] (c : Atom S) (hc : ∀ a : ↥A, c ∈ square S (q a)) :
    ∃ x y : FibreSet S A q, col S x.val y.val = some c := by
  classical
  obtain ⟨x⟩ := ‹Nonempty (FibreSet S A q)›
  have hx : x.val ∉ A := fibre_not_anchor S A q x
  let B := insert x.val A
  let r : ↥B → Atom S := fun b => if h : b.val = x.val then c
    else q ⟨b.val,(Finset.mem_insert.mp b.property).resolve_left h⟩
  have hrx (b : ↥B) (hb : b.val = x.val) : r b = c := dif_pos hb
  have hra (b : ↥B) (hb : b.val ≠ x.val) :
      r b = q ⟨b.val,(Finset.mem_insert.mp b.property).resolve_left hb⟩ := dif_neg hb
  have htri : ∀ a b : ↥B, a ≠ b → ∀ d : Atom S,
      col S a.val b.val = some d → S.Triangle (r a) d (r b) := by
    intro a b hab d hd
    by_cases ha : a.val = x.val
    · by_cases hb : b.val = x.val
      · exact False.elim (hab (Subtype.ext (ha.trans hb.symm)))
      · let bA : ↥A := ⟨b.val,(Finset.mem_insert.mp b.property).resolve_left hb⟩
        have hdq : d = q bA := Option.some.inj
          (hd.symm.trans (ha ▸ x.property bA))
        rw [hrx a ha,hra b hb,hdq]
        simpa only [S.symmetricLoop] using S.triangle_rotate ((mem_row S _ _ _).mp (hc bA))
    · let aA : ↥A := ⟨a.val,(Finset.mem_insert.mp a.property).resolve_left ha⟩
      by_cases hb : b.val = x.val
      · have hdq : d = q aA := Option.some.inj
          (hd.symm.trans ((col_symm S _ _).trans (hb ▸ x.property aA)))
        rw [hra a ha,hrx b hb,hdq]
        exact (mem_row S _ _ _).mp (hc aA)
      · let bA : ↥A := ⟨b.val,(Finset.mem_insert.mp b.property).resolve_left hb⟩
        rw [hra a ha,hra b hb]
        exact ⟨x.val,a.val,b.val,x.property aA,hd,x.property bA⟩
  obtain ⟨y,_,hy⟩ := onePointExtension S H cco B r htri
  have hyA : y ∈ FibreSet S A q := by
    intro a
    let aB : ↥B := ⟨a.val,Finset.mem_insert_of_mem a.property⟩
    have ha : a.val ≠ x.val := fun he => hx (he ▸ a.property)
    exact (hy aB).trans (congrArg some (hra aB ha))
  have hyx : col S y x.val = some c :=
    (hy ⟨x.val,Finset.mem_insert_self _ _⟩).trans
      (congrArg some (hrx _ rfl))
  exact ⟨x,⟨y,hyA⟩,(col_symm S _ _).trans hyx⟩

theorem fibre_palette_iff (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,0,w} S)
    [Nonempty (FibreSet S A q)] (c : Atom S) :
    (∃ x y : FibreSet S A q, col S x.val y.val = some c) ↔
      ∀ a : ↥A, c ∈ square S (q a) := by
  constructor
  · rintro ⟨x,y,hxy⟩ a
    exact ⟨x.val,a.val,y.val,x.property a,(col_symm S _ _).trans (y.property a),hxy⟩
  · exact fibre_pair_realize S A q H cco c

end CCO.RealHull.Geometry
