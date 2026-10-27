# Pokyny pro pokračování přípravného a koordinačního projektu

Tento dokument je pro nástupce tohoto koordinačního chatu. Přijímací
formalizační projekty mají vlastní číslované instrukce a společný protokol.

## Startup a autoritativní zdroje

1. Načti skutečný aktuální head <https://github.com/shulda/lean_cco> na `main`,
   jeho `formalization/coordination/BOARD.json`, protokol, `DECISIONS.md`
   a tento runbook. Veřejný board je jediná živá evidence přidělení.
2. Pro aktivní balíčky přečti zadání, reporty na pracovních větvích/PR,
   otevřené PR a skutečné výsledky kontrol na jejich přesných heads.
   Rozliš rozpracováno, odevzdáno, integrováno a přijato.
3. V soukromém `shulda/cycle_constrainedness`, větev
   `cco-sym/consolidated-r45-20261017`, adresář
   `cco-symmetric-eppa/papers/consolidated_working`, přečti
   `COORDINATOR_START_HERE.md`, `CURRENT_STATUS.md` a relevantní module JSON,
   proof notes a vlastní důkazy. Matematický source pin prvních modulů je
   `490c3f36d85db5a0b3ced0598e6c431825254ec5`; pozdější změny ověř v GitHubu.
4. Pokračuj v autorizované práci podle aktuálního stavu. Neobnovuj zdroje
   ze srpnových příloh nebo starého přiloženého `main.tex`. Scratch může
   zmizet; lokální cesty a shrnutí minulého chatu nejsou autoritativní.

Zdejší soukromý board ve stavu `PREPARATION` je pouze **startovní šablona**.
Po zveřejnění nepřenášej šablonu přes živý veřejný board, reporty ani Lean
implementaci. `prepare_formalization_launch.py` je nástroj prvního lokálního
sestavení, nikoli synchronizace běžícího repozitáře.

## Role a předávání

Tento projekt připravuje a konsoliduje matematiku, přesná tvrzení, jejich
předpoklady, důkazové podklady a DAG; přiděluje balíčky, řeší matematické
otázky a přijímá výsledky. Lean dokazují **jiné rovnocenné projekty**
v `lean_cco`. V článkovém repozitáři nezakládej Lean projekt ani Lean CI.
Základní infrastrukturu veřejného repozitáře smí připravit koordinátor;
matematická API a důkazy zůstávají úkolem B001 a dalších přijímacích projektů.

Projekty mají unikátní čísla 1, 2, ...; nejvýše jeden aktuální balíček na
projekt. Balíčky mají rozsah několika stran souvislé matematiky. Jednotlivá
lemmata a module `T` úkoly jsou interní mezikroky. Žádný samostatný trvalý
master formalizátor není potřeba.

Projekt pracuje autonomně uvnitř zadání. Po dokončení, při blockeru nebo
potřebě změnit společné API/rozsah uloží stav a řekne Matějovi. Matěj to
přinese sem. Nezaváděj automatické přebírání dalších úkolů ani povinné přímé
zprávy mezi projekty. GitHub se kontroluje při aktivní práci; nepředpokládej
průběžné sledování na pozadí.

## Přidělování a přijetí

Při počátečním zveřejnění je projekt 1 přidělen k B001, report `NOT_STARTED`.
Matěj teprve založí přijímací projekt. Připravená infrastruktura ani zelený
smoke build nejsou matematické dokončení B001. Pozdější stav vždy přečti
z veřejného boardu a reportů.

Po přijetí B001 připrav konkrétní zadání B002 (RAW exact) a B003 (STRONG
exact/PC) podle skutečného Lean API a rozděl je dvěma projektům. Projekt 1
může dostat jeden z nich. Třetí a případně čtvrtý projekt přidávej až po
úspěšné souběžné práci a integraci. B004 jsou selektory, B005 pozitivní SIR
a přímý relativní příklad. B006 spojuje negativní SIR s parity/Hasse;
upstream Hasse zatím nemá úplný předávací modul. Tyto řádky jsou blízký plán,
ne úplné rozdělení všech 342 výsledků. Package DAG plánuje práci; matematické
závislosti jsou v claim DAGu. Selektory například nepotřebují PC fixed-point
theorem, který jen sdílí balíček s exact calculus.

Při přijetí výsledku:

1. Přečti report a diff na přesném PR headu. Ověř mapu source labels → Lean
   deklarace, skutečné kvantifikátory, hypotézy a rozsah zadání.
2. Ověř build, dosažitelnost všech exportovaných modulů, consumer a skutečný
   transitive axiom/dependency audit. Žádné `sorryAx`, dodatečné nedoložené
   axiomy nebo skrytý upstream provider. Běžné Lean foundational axioms
   nejsou mezera. Zelené CI samo nedokládá zamýšlený význam tvrzení.
3. Podmíněný důkaz eviduj jako podmíněný. Zdrojovou instanci přijmi až po
   propojení doložených providerů. Matematické opravy vrať do přípravy se
   seznamem postižených callers; encoding-only lemmata ponech v Leanu.
4. V rámci autorizované koordinace integruj připravený výsledek a zkontroluj
   výsledný `main`. Ulož integrační commit do boardu, balíček `ACCEPTED`,
   projekt `WAITING`, dokud nedostane další balíček.
5. Při dalším přidělení zvyš revizi boardu, napiš větší konkrétní kontrakt,
   urč souborové hranice a aktualizuj generovaný přehled a instrukce.

Při blockeru řeš konkrétní tvrzení nebo předpoklad. Nevyžaduj znovu globální
audit článku. Změny společného API slaď se spotřebiteli a zaznamenej do
`DECISIONS.md`. Běžná práce uvnitř autorizovaného zadání nepotřebuje další
potvrzení uživatele.

## Hranice matematiky a infrastruktury

- RAW je skutečná relační kompozice včetně equality. STRONG používá tři
  různé reálné vrcholy; nepřidávej identity atom do diversity palety.
- Prázdné RAW slovo je Id, prázdný seznam omezení Top. Nonempty exact meet
  znamená neprázdný výsledek, ne pouze neprázdné indexování.
- RAW Helly není provider STRONG Helly. Zachovej oddělené AP/SAP/CCO/NR2
  předpoklady, full original sortwise lattice a podmíněnost pure-tag engine.
- Quotient orbitals/lifts jsou skutečné v původní automorphism group;
  existence liftu není group section. SIR stationarity je prescribed map
  s pointwise fixací; naturality vyžaduje onto celý designated target base.
- Rooted EPPA headline zůstává source-relative candidate se safe/MI
  providery. Detaily a negativní kontroly čti v příslušných proof notes.

Lokální checkout přípravy v minulém chatu měl vybrané soubory a syntetickou
historii. **Nepushuj jeho historii ani neúplný strom přes plný upstream.**
Použij ověřené staré bloby, full remote base tree, kontrolu celého nového
stromu a update ref s očekávaným headem. Z čistého skutečného checkoutu lze
pracovat standardně; nejprve rozliš oba případy.

V soukromém článkovém repozitáři nespouštěj placené Actions; přípravu publikuj
se `[skip ci]`. Veřejné Lean CI je v `lean_cco`. Ostatní dokončené Lean
repozitáře slouží jako inspirace; bez zvláštního zadání je neměň.

`HANDOFF_MANIFEST.json` dokládá **počáteční snapshot**. Plnou hash kontrolu
spusť před prvními změnami. Běžné změny boardu, reportů nebo README původní
snapshot změní; pro průběžnou kontrolu používej module source pins,
koordinační checker a Lean build. Nepřegenerovávej starý manifest, abys
zakryl změnu matematického zdroje, ani jej nepoužívej jako zákaz stavových změn.
