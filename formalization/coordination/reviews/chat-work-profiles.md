# Independent control of reversible Chat/Work profiles

Actual registered reader: `/root/reviewer_recovery_control`.

I authored or directed none of this migration, broker, validators, generators,
tests, repairs or its implementation design. I personally read the complete
32-file diff and the actual old policy/STATE/catalogue. I used no helper reader
and ran no tests, Lean builds or axiom audits. Concrete findings below are
review findings, not implementation contributions.

## Read scope and exact initial binding

Baseline: main `700c12f7e6e8476eb0100a6be37d5f619ade3c0a`.
Initial native freeze: `d5d63756ff77969a2607f4489db17ab096c6ba15`.
Public PR65 initial head: `a2748fb7f6ac2c972c848ff3c111e4701d7da462`.
The public commit has the exact native tree
`bdebb2cb4fb351470ecb31e7921e2b802b225670` and baseline main as sole parent.

I personally read all broker/profile/configurator code, the entire queue delta
against the existing complete validator, all new broker/profile test bodies,
workflow, preparation/handoff generator changes, policy/manifest, protocol,
runbook, queue/request/profile/return documentation, all generated startup
prompts and project instructions. Repeated generated project bodies were read
once in full and their complete identity/path deltas inspected; Work's two
instruction copies are identical. No unreviewed implementation helper supplied
this review.

Actual coordination `7210346655e453aa37536ab916e3a323324dc673` contains STATE396:
48 ACCEPTED packages, no active claim, policy12 and no lock. I fetched the whole
public STATE and verified the saved old snapshot equals that exact Git object;
canonical SHA256 is
`11a23eef3ae5158bc3f17ca0a8f7e5750945a6bd487881661a9e27139a05cddc`.
The old BOARD/policy snapshots equal baseline main bytes, the migration's saved
previous policy is exact, and current BOARD is unchanged.

## Findings

**R1 — P2, CLOSED by the personally reviewed repair: malformed checkpoint can poison the inbox.**
In `tools/coordination_broker.py`262–264, `observed_ci.run_id` is interpolated
into a URL before integer validation. A syntactically valid checkpoint request
with `run_id: {"bad": 1}` creates a path containing `{'bad': 1}`. The space causes
Python's HTTP client to raise `InvalidURL`, an `HTTPException`; it is outside
the narrow exceptions caught by `process()`379. The request receives no durable
rejected receipt, and the whole drain aborts before later workers. Every later
drain revisits the same immutable unreceipted request. This contradicts the
documented malformed-request isolation. I reported the concrete source path
and inspected the standard-library exception definition; I did not execute a
reproducer or implement the fix.

The author independently reproduced the escaping `InvalidURL` before repair.
I personally read the complete two-file repair at native
`f679dac6adb3da28e67597a31608a1847558d88c`, public
`f2c279a0d03ebbfce4ddde4bd1b05a680d2ec58b`, tree
`d3e16578f8432422be3102d654af52ef28d429b3`. Checkpoint evidence is now checked
for dict shape, a positive exact-int run ID, exact SHA and completed conclusion
before URL construction. Its behavioral regression covers an actual owned
claim, the malformed checkpoint, a subsequent different worker, rejected/no-change
receipts and the unchanged whole STATE. R1 is closed on this repaired source;
I did not rerun the test. Initial-head green CI does not certify this new head.

**R2 — P2, CLOSED by the personally reviewed repair: adding a worker clears a live claim pause.**
`coordination_profiles.promote()`232–233 unconditionally writes
`claims_paused=False`. A supported later append-worker deployment during a
paused handover therefore silently resumes new claims, despite no explicit
user-authorized `resume_claims` or mode-switch event. The old live pause should
remain a distinct preserved control on this advertised unchanged-mode/live-work
deployment path. STATE396's initial unpaused deployment is unaffected, but the
later worker-addition path breaks this guard. This was reported as a source
finding, without executing a reproducer or participating in repair design.

The author independently reproduced the lost pause with a real paused fixture
and live claim before repair. I personally read the entire two-file delta at
native `a027a58880278e8c3380da49501dc12cd6beb72d`, public
`67304ffa21ecfad31fe6c54cdf69818424615c41`, tree
`8c74196b997cf45fc341fe20f1dc31c496117782`. Promotion now preserves the actual
old pause flag. The regression performs append-worker promotion under a live
paused Chat pool, checks unchanged package records/mode and retained true pause,
then verifies a new otherwise eligible worker claim remains rejected as paused.
The small fixture extraction retains the prior live-worker-addition checks.
R2 is closed on this repaired source; I did not rerun tests.

The author subsequently found and reproduced a related empty-pool mode-change
edge in a later worker addition. I personally read the complete two-file
`+10/-2` delta and behavioral test at native
`623933bd44fa4173c6914bf2780d9a20cf3eb272`, public
`865119c5261601c6ef56b4db9a231ab824cc2bc4`, tree
`ce7202ad7a4e92b53c8da74c0ef2cfaa88ea021e`. All later additions now retain
the current mode even with no active claims; changing mode requires its
explicit runtime event. Initial reviewed profile installation still may select
its target. This related issue was found and repaired by the author, not by me;
I only independently read its actual delta. No source blocker remains.

Other reviewed invariants at this checkpoint are consistent: fresh Chat
identities4/5/6, all old actors/roles preserved, one unresolved batch per Chat,
real per-package and historical non-authorship, original Work capacity,
accepted-dependency ancestry, single lock and exact PR/main CI, strict policy
revision, manifest-bound deployment, explicit user-authorized reversible modes,
complete stopped-worker WIP handover with old records/history preserved and
effective approvals cleared. These source observations do not establish final
approval while exact final-head evidence remains outstanding.

## Reviewed prior-head CI

I personally fetched successful then-current-head CI41169070408/job124442885428 and
its complete 3,060,696-character log, then inspected actual checkout, tests,
generators/controls, build/audit and complete source/provider evidence.
Checkout `fabf3e0972f462c9efc8eca7a50faa3489b6e146` has the final approved-source
tree `ce7202ad7a4e92b53c8da74c0ef2cfaa88ea021e` and ordered parents baseline
main700c12f7 and public final head865119c5. All182 tests passed; project build
and audit each completed4293 jobs. The transitive audit checked28723 CCO
declarations with only propext/Classical.choice/Quot.sound. All three project
guards checked1619 actual parts and1619 current sources; all four EPPA guards
checked269 modules at pin`cd358cde844d5419fd43f30c441511927e09142f`, and all four
Ramsey guards checked106 at subtree`374241ce3751715c90b12c0b071f36026819ad4a`.
There were no error annotations and zero rebuilt CCO modules. Earlier-head
green runs were preserved but do not provide approval evidence for this head.

## Actor-relevant STATE projection delta

The author subsequently supplied native
`fca2f212f74a6ab10085249e2616de6cec9358fc`, public
`b8877da8b102bb8c6a174e76914d638bb864b2ae`, tree
`56cdbffb57370600d14a47119366b1503d4f0a3e`. I personally read the entire
eleven-file `+124/-24` delta, including every changed generated instruction and
documentation paragraph and both new/extended test bodies. It exposes an exact
deep-copied actor-relevant `state_view` in a receipt. The canonical ledger and
effective applied event remain authority; AVAILABLE/recommendation/no_change
does not create a claim. Existing work may be resumed from its actual own record.

The bound Git blob SHA uses actual UTF8 byte length and the Git blob header.
New STATE writes use the same serializer for the hash and published bytes;
status/no-write requests hash the original raw STATE text, retaining its actual
formatting. Selection includes own active work, foreign leased review, the
recommended package and the processed package. Whole STATE remains required
for audit, mismatch or full handover. No mutation or ownership rule changes;
no new source finding. This new head needs its own CI41169876583, not the
earlier182-test run above.

## Actual final-head evidence and prospective lock

I personally fetched completed successful final CI41169876583/job124445322368
for public head`b8877da8b102bb8c6a174e76914d638bb864b2ae` and its complete
3,060,809-character log. All183 tests, generators and finite controls passed;
project build and audit each completed4293 jobs. The audit checked28723 CCO
declarations against only propext/Classical.choice/Quot.sound. Three project
guards checked1619 actual parts and current source modules; four EPPA269 and
four Ramsey106 guards retained the exact pins above. No error annotations or
rebuilt CCO modules occurred. Actual checkout
`e809062be971aaaf6aaa2de30977dcffa12266f4` has the exact final native/public tree
`56cdbffb57370600d14a47119366b1503d4f0a3e` and ordered parents baseline main
`700c12f7e6e8476eb0100a6be37d5f619ade3c0a` and this exact final public head.

I personally read actual `profiles-start-draft.json` and complete parsed
`profiles-state397-candidate.json` generated from saved STATE396. All48 package
records, every prior history entry and all other old global STATE fields are
exactly preserved. The only additions are the root-held infrastructure lock,
its event and revision397; policy_revision remains12 until verified promotion.
The actual prospective lock binds this final head/base/PR65, true CI above,
root authorship, my actual reviewer identity and the complete profile manifest.

The complete old/new BOARD canonical digest is unchanged:
`661173fcaa2fcbda1a54f7c8bf484d9b6ce480b8b1b65b4887c0c1942d7bfa8f`.
Old policy12 digest is
`83860e56213ee023c1fd7df3b5a8194a36342ebffb2b7542c03497f35e986be6`;
new policy13 digest is
`5a76a9dd1920abe37006047c8659ce4af808c887103da2209f7f62e8fa2d2561`.
I checked these against actual complete snapshot bytes/objects, not a partial
manifest or private replacement. Fresh GitHub reads confirmed main remains
700c12f7, PR65 OPEN/unmerged at the final head, the same synthetic checkout,
and coordination remains72103466/STATE396 with no lock.

## Actual decision

I, actual registered non-author `/root/reviewer_recovery_control`, approve
exact PR65 head`b8877da8b102bb8c6a174e76914d638bb864b2ae` and the personally
reviewed actual prospective deployment lock. I expressly endorse the proposed
`review.summary` and `review.independence` text in `profiles-start-draft.json`
as my own actual decision. Earlier conditional reports were not approvals.
R1 and R2 are closed; the separately attributed author-found guard and complete
projection delta were personally reviewed. No source, CI or policy blocker
remains. I wrote no implementation, test, repair or design and ran no duplicate
test, build or audit.

Publish this actual report unaltered before CAS. I will personally recheck the
whole actual public STATE397 lock before expected-head history-preserving
merge. Actual resulting-main CI/audit must then pass before manifest-bound
atomic profile promotion. The initial target Chat mode may activate only then;
no old package record, source contract, pin or acceptance is changed. The
request workflow still needs its genuine post-deployment status-only smoke
receipt; none of these review statements pretends that execution already ran.

## Actual public pre-merge recheck

My actual final approval report was published unaltered at coordination
`c0a12547d13bc989fc68318f2720f132d5fceb80`. I personally fetched the whole
actual public STATE397 at `906003afc9f0b8d2dfe0b6ad64b06610136b5883` and
compared it with the approved candidate: the full lock and new event exactly
match; all48 package records, every prior history entry and all other global
fields equal STATE396, and policy_revision remains12. I fetched the published
report and compared its entire text with my own final report: exactly equal.

Fresh independent PR65/main reads before merge confirmed the approved final
headb8877da8, base/current main700c12f7, the same synthetic checkoute809062,
and PR65 OPEN/unmerged. I explicitly confirmed the actual exact-head approval
remained valid under this one public root-held lock. The deployment must retain
that lock until green actual resulting-main CI/audit and atomic promotion.
