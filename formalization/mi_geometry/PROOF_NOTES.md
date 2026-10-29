# Canonical normalized MI geometry — proof notes

Source pin: `490c3f36d85db5a0b3ced0598e6c431825254ec5`. These are human-expanded proof obligations for OTHER Lean projects, not Lean statements, compiled imports, or formal certification. The human TeX remains unchanged. The claim identifiers C01–C31 below refer to this module; provider names refer to their existing preparation contracts.

## N00: Scope, actions, and hypothesis boundaries

The selected source consists of `maximal_cores/02_complementary_owner_spectrum.tex` through `05_joint_owner_minima.tex`, together with `lem:acf-hat-pseudocomplement` and `lem:acf-hat-normalised` from `01_maximal_hat_normalisation.tex`. Algebraicity projection, finite closed preimages, rectangle closure, the harmless-owner criterion, original correspondence geometry, and finite-action avoidance belong to the shared `acl_owner_geometry` foundation. Reuse those contracts; do not create an independent second proof tree for them here.

Unless a claim is explicitly finite order theory, work in the standing countable, inhabited, homogeneous, transitive original source M with a finite complete symmetric binary orbital language, age AP, and semantic homomorphic CCO. All relations and products are represented relations on actual carriers. Equality is retained in RAW atoms. “Exact” means FULL RAW word exactness. An exact equivalence is an equivalence as well as an exact relation; the equivalence hypothesis is essential below. The full invariant-equivalence lattice and its exact sublattice remain distinct. Normalize by excluding every nonidentity finite-class exact equivalence, not merely by assuming that the largest finite equivalence F has thin atoms.

List ALL distinct inclusion-minimal infinite-class original invariant equivalences E_1,...,E_r. An arbitrary selected subfamily is insufficient for intersections, normalization, or ancestor conclusions. Use r≥2 where stated. Let R_i be the original correspondence equivalence associated with E_i, and retain the older notation C_i=κ(R_i). The maximal exact core is a different object, denoted Ĉ_i. Never silently identify the two.

An actual quotient is named by its old Aut(M)-pair orbitals. The `raw_exact` source-inheritance theorem supplies its countable homogeneous AP+CCO source instance. Joint lifting supplies individual finite partial-map lifts; neither theorem supplies a functorial lift or a global group section. Retain countability at these applications. The safety conclusions additionally require an original diversity palette S with strong amalgamation on finite ABSOLUTELY real-acl-closed spans. The output need not be closed. Pure lattice, normalization, and acl-reconstruction claims do not require S.

## N01: Maximal exact pseudocomplements — C01–C03

**C01.** Let H be an invariant EXACT EQUIVALENCE. We prove

`H ≤ R_i  iff  H ∩ E_i = Id`.

If H≤R_i, then H∩E_i≤R_i∩E_i=F∩E_i, using the shared global correspondence theorem. This intersection is an exact equivalence: exact meet closure applies because equality witnesses a nonempty intersection. It has finite classes, so normalization makes it Id. Conversely suppose H∩E_i=Id. For each actual atomic support a≤H, including equality, transitivity of H gives a;a≤H. Nonempty symmetric atomic orbitals are serial, so Id≤a;a. Consequently E_i∩a²=Id. The definition of R_i therefore puts a below R_i. Taking the union of all atoms of H proves H≤R_i. This argument would fail for a general exact relation H: the inference a²≤H uses equivalence transitivity.

**C02.** The finite exact lattice contains Id and is closed under joins. The join of all exact equivalences below R_i is therefore an actual exact equivalence Ĉ_i still below R_i. By C01 it is the greatest exact equivalence whose meet with E_i is Id, namely the pseudocomplement of the exact atom E_i. The normalized E_i is an exact atom: every nonidentity exact equivalence below it is infinite-class, and minimality of E_i then gives equality. If j≠i, E_i∩E_j is finite-class by minimality and exact by meet closure, hence Id. Applying C01 gives E_j≤Ĉ_i. This also recovers the source proof through E_j≤R_i.

**C03.** The meet of all Ĉ_i is exact and lies below the meet of all R_i, which the shared original-coordinate theorem identifies as F. Normalization forces this meet to be Id. When r≥2, choose j≠i; E_j≤Ĉ_i shows Ĉ_i>Id and that it has infinite classes. Also E_i∩Ĉ_i=Id prevents Ĉ_i=Top. Thus Q_i=M/Ĉ_i is an actual nontrivial exact quotient, strictly smaller in diversity rank. The counting argument is elementary: quotient pair orbitals group old pair orbitals, and quotient equality contains old equality together with at least one old diversity atom. Distinct quotient diversity atoms have disjoint nonempty old supports. Hence there are fewer quotient diversity atoms. Quotient source inheritance, a separate provider application, makes Q_i an admissible standing source.

## N02: Residual directions and normalized factors — C04–C08

**C04.** For a nonempty I⊂[r], set K_I=⋂_{i∈I}Ĉ_i. Suppose an exact equivalence on M/K_I is a nonidentity finite-class relation. Its old pullback is an invariant exact equivalence H>K_I, with finite relative index [H:K_I]. For i∈I, E_i∩K_I=Id because K_I≤Ĉ_i. Fix an actual class of E_i∩H. Sending each point in that class to its K_I-class is injective: two points with the same image are both E_i- and K_I-related, hence equal. Its images lie among the finitely many K_I-classes in one H-class. Thus E_i∩H has finite classes. It is an original exact equivalence, so equals Id by normalization. C01 gives H≤Ĉ_i for every i∈I, hence H≤K_I, a contradiction. No quotient has acquired a nonidentity finite exact kernel.

**C05.** The exact-interval identification used here has two directions. An exact quotient equivalence pulls back to an old exact equivalence above K_I by the converse exact-pullback contract in `exact_crt`. Conversely an old exact equivalence H≥K_I is K_I-saturated by equivalence transitivity, so exact descent makes H/K_I exact. The full invariant-equivalence correspondence is the ordinary relation correspondence for an actual quotient: preimage and quotient image are inverse on invariant equivalences above K_I. This does not assert distributivity of that full lattice. Naming the actual old orbital language ensures that the invariant relations concerned are unions of precisely those pair orbitals. Invoke `raw_exact` for the homogeneous quotient source before applying source theorems to it.

In a normalized source, minimal nonidentity exact equivalences coincide with minimal infinite invariant equivalences. Indeed, every nonidentity exact equivalence is infinite-class. Every infinite invariant equivalence contains a minimal infinite one by finiteness of the full invariant lattice; the minimal-cut theorem makes that one exact. These two observations prove both directions of the assertion. This is the bridge from the exact interval computation to the FULL invariant minimal directions; the bridge is not an unsupported identification of the two lattices.

**C06.** Use the prepared finite Birkhoff representation of the exact lattice as Down(P), with P the nonzero join-irreducibles. The exact atoms E_i correspond to singleton downsets of ALL minimal points p_i of P. Their pseudocomplements are P\↑p_i, so

`K_I = P \ ⋃_{i∈I} ↑p_i`.

The upper interval above K_I is isomorphic to the downset lattice of the induced residual poset U_I=⋃_{i∈I}↑p_i, by removing K_I and adjoining it back. This is valid because K_I is a downset. Every q∈U_I lies above a selected p_i, and each selected p_i belongs to U_I and is minimal there. No other point can be minimal there. Distinct selected p_i remain distinct. Therefore the exact atoms in the quotient interval are exactly (E_i∨K_I)/K_I for i∈I. By C04–C05 these are precisely its minimal infinite invariant directions, with no additional directions. This includes I=[r], where K_I=Id, and singleton I, which gives a unique direction.

**C07.** The old packet-core data give C_i≤Ĉ_i≤R_i, [R_i:C_i]<∞, and Σ(C_i)=R_i. Thus both [R_i:Ĉ_i] and [Ĉ_i:C_i] are finite. Since R_i/Ĉ_i is finite-class, R_i≤Σ(Ĉ_i). Conversely, for ANY invariant equivalence H≥Ĉ_i with finite [H:Ĉ_i], the tower law gives

`[H:C_i] = [H:Ĉ_i] [Ĉ_i:C_i] < ∞`.

Hence H≤Σ(C_i)=R_i. Taking the greatest finite-index extension proves Σ(Ĉ_i)=R_i. Under actual quotient correspondence, F_i=R_i/Ĉ_i is exactly the greatest finite-class invariant equivalence of Q_i. The proof uses finite indices in the full invariant lattice; it does not place the potentially nonexact packet R_i into the exact lattice or infer equality Ĉ_i=C_i.

**C08.** By C06, Q_i has exactly one minimal infinite direction. Apply the existing `real_closure` C11 singleton/rank-one theorem to its inherited infinite source instance. It yields acl_{Q_i}(A)=F_i[A] for every finite real A, including A=empty. The source is infinite because its surviving minimal direction is infinite. This application needs no SAP premise and no harmless-owner conclusion. Naming owner imaginaries requires the separate shared harmlessness theorem. This shorter provider route supplies the unary closure conclusion without importing all owner-union conclusions of the longer direct-unary-closure source lemma.

## N03: Closure providers and complete complementary spectrum — C09–C12

**C09.** Reuse the foundation's three selected exports. APJ says π_E(acl(A))⊂acl(π_E A) for finite real A and actual full exact E. Its proof uses nested mixed orbitals and finite joint lifting, not a global automorphism section. FPCL says that an intersection of full inverse images of finite absolutely closed quotient sets is finite and closed when the common exact kernel has finite real classes. Rectangle closure specializes it to C∩K=Id: finite absolutely closed D⊂Y and P⊂X surjecting onto the same nonempty finite owner set B give a finite absolutely closed full rectangle D×_B P. B need not itself be closed for rectangle closure. It will be closed in the helper construction for a different reason.

**C10.** Fix finite actual B⊂T. For each ordered pair (t,t')∈B² and each X-atomic orbital b realized by some actual pair above exactly these two owners, select such a witnessing pair. There are finitely many incidences because both B and the named X-palette are finite. Include an Id_X witness for every t=t', and at least one point above every owner. Their finite union P_0 projects exactly onto B and contains a complete owner-pair spectrum. If B is absolutely acl_T-closed, close P_0 absolutely in X. APJ for X→T puts every new owner's value in acl_T(B)=B. Since P_0 already covers B, the resulting finite closed P projects onto exactly B. No harmlessness assumption in X occurs in this construction.

**C11.** Let y≠y' be actual Y-points with owners t,t'∈B and Y-orbital q. Fix any old fine atom a in the actual saturated pullback of q. Choose a real a-edge u,v; its projected Y-pair has orbital q. Its T-owner pair and (t,t') have the same actual old-Aut(M) T-pair orbital, because both are projections of q. By the definition of that orbital, ONE old automorphism moves the two owners simultaneously to t,t'. Apply it to obtain an a-edge u_1,v_1 with precisely these owners. This use of an actual pair orbital is weaker than, and independent of, a global lifting section for Aut(T).

Let b be the X-orbital of their K-classes. The helper spectrum supplies p,p'∈P with owners exactly t,t' and orbital b. Two-factor CRT supplies the real points (y,p),(y',p'). Their Y-block is the block of a and their X-block is the block of a. The prepared fine-colour meet identity says that those saturated blocks intersect in (C∩K);a=a. Thus the pair has literal fine colour a. Its real endpoints are distinct because y≠y', even if p=p'. Varying witnesses proves realization of EVERY fine lift of q, not merely one safe representative. The spectrum lemma itself requires neither harmlessness nor closure of P; those properties support its later application.

**C12.** The phase pair table is a diagnostic of these boundaries. In the established Cartesian-phase source M_*=N²×F2, use C=same row and phase, K=same column and phase. Then Y-points are (r,g), X-points are (c,g), and common owners are phases. For different rows r,r', one common column c, and phase g, the two real points (r,c,g),(r',c,g) are distinct but their X-coordinates coincide. Their fine atom has flags (rowEqual=0,columnEqual=1,phaseDifference=0); it requires an X-diagonal witness. Removing X-diagonals deletes a genuine fine lift.

For Y-points (r,0),(r,1), choosing equal columns gives the thin phase-flip atom (1,1,1), whereas different columns give (1,0,1). For the palette of atoms having different row OR different column, the second is safe and the first unsafe. Thus existential projected safety differs from full support. These computations need only the stated coordinate pair table. This diagnostic does not independently certify the whole example's homogeneity, CCO, exact-lattice classification, or closed safe amalgamation. Use the existing `real_closure` example proof contracts for their established source properties, and treat further maximal-core assertions about the example as separately proved obligations if exported.

## N04: Harmless owner avoidance and helper preparation — C13–C16

**C13.** Suppose the actual owner map Y→T has the harmlessness property for every finite named owner set B: for finite real A,

`acl_Y^eq(A∪B) ∩ Y = acl_Y(A)`.

Let A be finite and absolutely closed, L⊃A finite induced, and Z⊂Y\A finite. For each x∈L\A, x∉acl_Y(A), hence x∉acl_Y^eq(A,B). Its orbit under G=Aut(Y/A,B) is infinite. The shared finite-action avoidance theorem produces ONE g∈G with g(L\A)∩Z=empty. All named owners are fixed individually, so original owner assignments are retained. No closure of L or Z is required. The avoidance provider proves a simultaneous group statement; choosing separate automorphisms for individual x would not suffice. The foundation owns the finite-coset-cover/Neumann proof behind this provider.

**C14.** Start with an arbitrary closed Y-span A→L,R. By quotient homogeneity realize its common base literally and realize both factors over it. Choose B to be the absolute acl_T of the union of their owner images. This is finite by oligomorphy. If both are empty, first add one actual owner and then close. Quotient sorts are inhabited, so the choice exists. B is always finite, nonempty, absolutely closed, and contains all owner labels needed by the span. The extra owner in the empty case is a common helper parameter; it does not alter the input vertices.

**C15.** Apply C10 to this B and close all chosen X witnesses. This produces a finite absolutely X-closed P, with full owner-pair spectrum and owner image EXACTLY B. The two assertions have different justifications: existence of old witnesses gives the spectrum and initial surjectivity; APJ and acl_T(B)=B prevent new owners during closure. Do not replace the latter argument by unassumed harmlessness in X.

**C16.** Choose finitely many actual Y-points meeting every owner in B, adjoin A, and take absolute Y-acl to obtain D. Again APJ keeps all owner images in B, while the selected representatives cover B. Thus D is finite, absolutely closed, contains A, and projects exactly onto B. Its real points later anchor all owner names: any automorphism fixing D pointwise fixes each named owner in B.

## N05: Closed padding and one-sided full-support safety — C17–C23

**C17.** Use C13 first on A⊂L to avoid D\A. Replace L by that owner-preserving copy. Next use C13 on A⊂R to avoid (D\A)∪(L\A). The forbidden sets are finite and outside A. The resulting copies satisfy L∩D=R∩D=L∩R=A, and every original vertex retains its literal actual owner label. This step requires A absolutely closed and harmlessness in Y. It makes no relative-closure assumption over the newly introduced helper D.

**C18.** Let Lhat=acl_Y(D∪L), Rhat=acl_Y(D∪R). They are finite absolutely closed extensions of D; APJ keeps their owners exactly B. Closing may create additional overlap, so do not assert that the intersections already equal D. Instead use finite-action avoidance for Aut(Y/D) on the finite set Rhat\D, avoiding Lhat\D. All these point orbits are infinite because D is absolutely closed. One automorphism fixes D and makes Lhat∩Rhat=D. It fixes B because D represents every owner. Move the entire Rhat and its original R together. The original R still meets D in A, and its intersection with original L is exactly A. This ordinary closed SAP argument has no S-colour conclusion and assumes no harmlessness in X.

**C19.** By full exact CRT, the three full rectangles D×_B P, Lhat×_B P, Rhat×_B P are actual finite induced M-substructures. Shared rectangle closure makes all three absolutely real-acl-closed. Their real intersection is the base rectangle. The original strong closed S-amalgamation premise now applies to this closed span. Embed its finite age output into M and align its base rectangle with the original actual rectangle by old homogeneity. This permits us to regard every base point as fixed. No assertion that the S-amalgam itself is closed is needed.

**C20.** For t∈B choose d_t∈D above t. For every p∈P above t, the base contains (d_t,p). In either factor, every (y,p) is K-equivalent to this base point. The two real factor embeddings preserve these K-relations, so their induced X-coordinate is the SAME actual X-class p, anchored by the fixed base. For two p,p' with possibly different owners, base points (d_t,p),(d_t',p') fix their complete X-pair orbital as well. Thus the amalgamation cannot independently change or identify the complementary coordinates. This is why full owner-complete padding precedes S-amalgamation; no subsequent selection of independently matching representatives is allowed.

**C21.** Each real rectangle embedding induces an embedding of its Y-factor. All real points with one original Y-coordinate are C-equivalent, and points with distinct Y-coordinates are not; the embedding preserves both facts. Original pair colours project to the same actual quotient orbitals, so the induced map preserves the full Y-language. If opposite off-D Y-points had the same image, their owners would agree, say t. Choose one p∈P above t. Their corresponding real points have equal C-coordinates by assumption and equal K-coordinates by C20, hence are equal because C∩K=Id. Both are outside the common real rectangle, contradicting strongness. Within-factor injectivity also prevents an off-D point from becoming a base quotient point. Therefore the projected padded factors form a strong Y-amalgam over D. Restriction to the original copies of L,R yields a strong amalgam over A, since their intersections with D were exactly A.

**C22.** Fix any new cross Y-edge yy' of the padded projected amalgam, so y≠y', y lies outside D on the left and y' outside D on the right. Their actual owners t,t' lie in B, including the possibility t=t'. The fixed actual complementary helper P satisfies C11. Hence for EVERY old fine atom a over q=col_Y(y,y'), some p,p' over those exact owners gives a real pair (y,p),(y',p') of colour a. These are points in opposite embedded rectangles, both outside their common real base. Original strong S-amalgamation forces a∈S. Therefore every fine lift of q lies in S, which is exactly q∈S_Y. This is a full-matrix argument, including all complementary diagonal witnesses; it is stronger than showing that one selected real representative pair is safe.

The displayed CRT points after amalgamation are justified by C20 and actual CRT uniqueness: the images of the original rectangle vertices are precisely the real points with the asserted Y and anchored X coordinates. They are not independently introduced vertices whose cross colours could escape the original amalgamation guarantee.

**C23.** For a distinct projected pair coming from old real x,x', its actual old atom is among the fine lifts of its Y-colour. Thus if the old atom is unsafe, the Y-colour cannot belong to S_Y. For a total RAW formulation declare equality outside the diversity palettes. Then the implication “old colour outside S implies projected colour outside S_Y” also covers x=x' and distinct real points with coincident Y-coordinates: the projected colour is simply Id_Y. Do not claim that distinct old unsafe points necessarily have distinct quotient images. Conversely, an unsafe quotient colour need only have SOME unsafe fine lift; other fine lifts may be safe.

The entire Y construction used harmlessness only in Y. Closing P was controlled by APJ and the absolute closure of B. Interchange C,K to prove the corresponding X result, now requiring harmlessness only in X. Both harmlessness hypotheses imply both safe palettes, but neither should be added unnecessarily to the one-sided theorem contract. The proof depends on shared closure and avoidance providers independently of the desired safe-descent conclusion, so there is no circularity.

## N06: Joint owners and minimum ancestors — C24–C26

**C24.** This paragraph is pure finite order theory. Let a finite distributive lattice be Down(P), with ALL distinct minimal points p_1,...,p_r, r≥2. For q∈P define Anc(q)={i:p_i≤q}. Every such set is nonempty: the finite nonempty lower cone of q has a minimal element, which is minimal in P. Let Ĉ_i=P\↑p_i. Joins and meets are literal unions and intersections. Hence

- J_ij=Ĉ_i∨Ĉ_j consists of q for which {i,j} is not contained in Anc(q).
- H_i=⋂_{j≠i}J_ij consists of q for which i is absent from Anc(q), OR Anc(q)={i}.
- H_*=⋂_{i<j}J_ij consists of q with |Anc(q)|=1.

For the middle formula, if i is present, membership requires every other j to be absent. For the last formula, no distinct pair may be present; nonemptiness then forces cardinality exactly one. These descriptions also show that all displayed sets are downsets, already guaranteed by their lattice definitions.

**C25.** Each minimal p_i has Anc(p_i)={i}, so belongs to H_*; consequently H_*>0. A point belongs to every H_i exactly when its ancestor set is a singleton, giving ⋂_iH_i=H_*. For i≠j, failure of membership in BOTH H_i and H_j is equivalent to i,j both belonging to Anc(q): if one index were absent its H-set would contain q, and if both occur both ancestor sets have size at least two. Thus H_i∨H_j=J_ij. This is not a Boolean-lattice argument: ancestor sets may have multiple elements, and P may have comparable nonminimal points.

**C26.** Apply this order result to the original exact lattice, identifying Ĉ_i by C02. Bottom is Id, so H_*>Id is an actual nonidentity exact equivalence. Equivalently each E_i lies below every pairwise join J_jk, since one of the two complementary cores contains it. The quotient Ω=M/H_* is actual and has lower diversity rank by C03's counting argument. Invoke `raw_exact` separately for its standing source properties. These conclusions use no amalgamation assumption beyond those required by the exact-lattice provider, and no safe palette S.

## N07: Canonical factor assembly — C27–C30

**C27.** For fixed i put K=⋂_{j≠i}Ĉ_j and J=Ĉ_i∨K. C03 gives Ĉ_i∩K=Id. The join J contains every original minimal E_k: when k=i, E_i lies below every core in K; when k≠i, E_k≤Ĉ_i. Harmlessness in original M follows from the shared criterion, but that alone is not the required quotient harmlessness. Check each factor explicitly.

In Q_i=M/Ĉ_i the sole minimal infinite direction is (E_i∨Ĉ_i)/Ĉ_i by C06. Since E_i≤K≤J, its owner kernel J/Ĉ_i contains this direction. In X=M/K the minimal directions are exactly (E_j∨K)/K for j≠i, again by C06, and all lie below J/K because E_j≤Ĉ_i. Both quotient factors are normalized standing infinite sources by C04 and inheritance. The shared harmless-owner criterion, instantiated separately in these sources, proves that finite actual J-owners are harmless in BOTH factors. This validates both applications without inferring quotient harmlessness merely from original harmlessness.

**C28.** Assuming original strong closed S-amalgamation, apply C23's one-sided theorem to each recipient Q_i, using C27. Define S_i by universal old fine support, globally on its whole quotient source. The resulting S_i has strong closed amalgamation. For unsafe cliques, reuse the shared original unsafe-concentration theorem: for each pair i≠j, a finite unsafe clique lies wholly in one R_i-class or one R_j-class. Thus at most one index can fail to contain the entire clique in a single R_i-class; otherwise choose two failing indices. For every other index, projection through Ĉ_i places the clique in one finite F_i=R_i/Ĉ_i packet. Singleton cliques automatically meet this condition. No new concentration proof or Boolean-coordinate hypothesis is required.

**C29.** Reuse the shared finite-common-kernel acl identity with the finite family Ĉ_i, whose meet is Id by C03. For finite real A it gives

`acl_M(A) = ⋂_i π_i^{-1}(acl_{Q_i}(π_i A))`.

For clarity, its forward inclusion is APJ separately in every coordinate. For the reverse inclusion, the Aut(M/A)-orbit of x projects into finitely many algebraic coordinate classes; there are finitely many joint tuples, and each tuple has at most one real preimage because the common kernel is Id. The orbit is finite. This counting argument needs no independent automorphisms on the coordinates and no lifting section. Substituting C08 gives the intersection of π_i^{-1}(F_i[π_i A]). Each inverse image is exactly R_i[A], by the definition F_i=R_i/Ĉ_i and Ĉ_i≤R_i. This remains valid for A empty: quotient rank-one closure is empty and the source has no algebraic real points over empty.

**C30.** Assemble the corollary with its premises visibly separated. Under the normalized standing source assumptions and r≥2, the exact ancestor relations, strict owner quotient, normalized one-direction factors, finite bottoms, and closure identity hold independently of S. Under the ADDITIONAL premise that S strongly amalgamates finite absolutely closed original spans, the global full-support S_i palettes are strongly closed-safe and unsafe cliques have at most one exceptional packet projection. The source corollary's phrase “as in Lemma quotient-safety” must carry this conditional premise into any standalone receiving statement. The proof of the safety and clique branches cannot discharge it from AP alone. This clarification changes no structural branch.

## N08: Finite controls and their scope — C31

The executable `tools/check_mi_geometry_controls.py` independently exhausts
all 243 labelled posets through four points, all downsets and nonempty
selected-root intervals. It checks full-minimum ancestor identities/JOG,
including shared-ancestor non-Boolean cases. Its 24 finite partitions give
class-injection and uniform nested-index checks. Deliberately nonmaximal
cores, an incomplete minimum list and the nondistributive M3 lattice fail
the proposed strengthenings. These finite tests do not prove the absence of
finite exact kernels in an infinite source. The companion
`tools/check_acl_owner_controls.py` supplies the rook/phase-pair diagnostics
below; both are included and run in the complete handoff preflight.


C31 records controls, not general source certification. On a finite phase-coordinate matrix with three rows, three columns and two phases, take P to be two columns in both phases. For every ordered distinct Y-pair compute all fine colours using the full three-column coordinate range, and compare with the helper's colours. All 30 ordered distinct pairs agree. Removing X-diagonal witnesses deletes (0,1,0) for different rows and equal phases. For equal rows and opposite phases the lift set is {(1,0,1),(1,1,1)}, demonstrating existential/full-support separation. These are exact finite pair-table checks inside the established infinite example. Finite truncations are not asserted to satisfy semantic CCO.

Useful negative boundary controls also have direct source interpretations. In the phase owner quotient T=F2, B={0} is not absolutely closed; closing (c,0) in X adds (c,1), so helper owners escape B. With B=F2, D={r}×F2 and nonclosed P={(c_0,0),(c_1,1)}, c_0≠c_1, the rectangle omits the two opposite phase corners in its absolute real acl. Owner surjectivity does not replace factor closure.

In Y=N², naming a second-coordinate owner 1 together with A={(0,0)} makes x=(0,1) algebraic although x∉acl(A). The owner-preserving avoidance conclusion fails with forbidden set {x}. Also A={(0,0),(1,1)} is not closed: its corner is definable, preventing disjoint copies of extensions adjoining that corner. These controls distinguish harmlessness and absolute base closure from ordinary AP. Dropping finite common kernel likewise destroys FPCL finiteness: a singleton quotient by Top has infinite full preimage in an infinite source.

Finally M=N² with S=empty is a control against omitting C30's safety premise. Its normalized coordinate factors are N with F_i=Id; their empty full-support palettes cannot amalgamate two singletons safely over empty. Two diagonal grid points also form an unsafe clique with two nonconstant projections. These examples test specific claimed implications; none is evidence that the audited correctly conditioned descent proof fails.

## N09: Packaging and queued article feedback

Direct prepared providers are `acl_owner_geometry`, `raw_exact`, `exact_crt`, `finite_packets`, and `real_closure`. Their status remains human proof preparation. Keep source inheritance, RAW colour reconstruction, joint lifting, finite order algebra, finite-index packet algebra, and owner avoidance as separate interfaces. Standard finite-orbit algebraicity, oligomorphy, monotonicity/idempotence of acl, and actual quotient action bookkeeping must have explicit implementations or support contracts in the receiving project.

Queue three exposition clarifications without editing the pinned human article: list ALL minimal infinite directions/minimal points; retain “H is an exact EQUIVALENCE” in the pseudocomplement statement; make the inherited original strong closed S-premise explicit on the final safety/clique clauses. The one-sided safety theorem deliberately does not require opposite-factor harmlessness. No global theorem repair, independent factor action, arbitrary imaginary CCO, or new SAP axiom is asserted. Source fingerprint validation, graph validation, and finite controls remain distinct from mathematical proof verification.
