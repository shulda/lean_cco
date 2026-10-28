# B003 C13 forward: actual exactness of canonical PC domains

Proof checkpoint `8a4ad606b73b4468785585da3906b35919fe3c35` on local
`work/b003-pcexact`, extending C09 checkpoint `872367e` and preserving
all inherited work. Source pin, mathematical contracts, toolchain and
manifest are unchanged. New implementation actor: `strong_bridge`.

`PCExactness.fixedNetwork_exact_of_nonempty` proves from original
homogeneous SAP+CCO and zero-free final fixed domains that EVERY canonical
fixed domain belongs to the ORIGINAL nonempty finite-meet strong exact
family. `fixedNetwork_exact_of_strongCompletion` supplies the source-facing
corollary for any actual strongly completable diagram. No conditional path,
Helly, fixed-point or reverse-survivor provider is a premise.

The route is independent of the outstanding C12 path formula:

1. The final stable refinement is included in EVERY iterate, so one actual
   final atom witnesses nonemptiness of every earlier evaluated domain.
2. Initial domains are literal original atomic singletons or typed diversity
   Top; Top nonemptiness is derived from original homogeneity and SAP.
3. A PC step is a FINITE meet of its old domain and the actual strong
   products through every third formal vertex distinct from both endpoints.
   Source C08 exact-product closure applies to all factors. Finite-meet
   presentation closure retains the explicitly nonempty evaluated output.
4. Induction proves exactness of all iterate domains; the stationary index
   gives the canonical fixed domains. Actual completions provide zero-free
   final domains by the independently proved survivor induction.

The finite meet includes the no-third-vertex case without adding an
identity colour. Repeated named sorts are retained in the dependent atom
palettes; the network still ranges only over distinct FORMAL pairs. Empty
Boolean domains remain legal during general PC iteration; no exactness is
claimed for an empty evaluated output.

Local verification: **1022** full-root Lake jobs, green; `import CCO` exposes
both the new exactness theorem and the C09 theorem through explicit
`#check`. The same environment's transitive audit checks **1710** CCO
declarations including private names and permits only `propext`,
`Classical.choice`, `Quot.sound`. `#print axioms` on the new source theorem
confirms the same list. Root generated outputs were freshly materialized
with artifact restoration enabled before the audit.

C07/C08/C09 and C13 forward exactness are proved in this candidate. C12
chosen-survivor/simple-path equality and C13 converse canonical-family and
three-root canonical classification still need their actual source proofs.
The independent triangle-fullness sibling is not counted in this head.
B003 remains **IN_PROGRESS**. Remote exact-head CI, non-author exact-SHA
review, locked integration and green resulting main audit remain required.
