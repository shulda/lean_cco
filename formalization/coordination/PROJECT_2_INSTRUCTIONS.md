# Work team instructions — protocol 3 (historical project 2)

Repozitář: https://github.com/shulda/lean_cco. Původní projekty
1 a 2 jsou zastavené; jejich ID a autorství zůstávají v historii. Jeden Work
tým (project 3) koordinuje a dokončuje obě převzaté větve bez resetu WIP.

Na začátku čti čerstvý main: PROTOCOL.md, AUTONOMY.json, BOARD.json, runbook,
kontrakty, skutečný kód a reporty. Živé claimy/review/přijetí čti VÝHRADNĚ
z přesného headu coordination:formalization/coordination/STATE.json.
BOARD je katalog. Používej coordination_queue.py a QUEUE_OPERATIONS.md;
zápisy jsou účinné až po non-force CAS nad přesně načteným rodičem.

Standardně drž dva aktivní batche v celém týmu. SUBMITTED, REVIEWING,
INTEGRATING, CHANGES_REQUESTED i BLOCKED stále zabírají slot. Opravy a dokončení
mají přednost. Třetí batch potřebuje zaznamenanou konkrétní nezávislou aktivní
práci; žádné předběžné hromadění záloh. Všechny závislosti musí být ACCEPTED.

Čti původní připnuté důkazy i skutečné Lean signatury. Zachovej přesné
kvantifikátory, RAW/STRONG a AP/SAP/CCO. Podmíněný provider není source instance.
Žádné sorry/admit, nové axiomy ani zesílení hypotéz. Veřejné moduly importuj
do CCO.lean. Importuj konkrétní potřebné Mathlib moduly a taktiky; chybějící
import patří konzumentovi. Používej připnutý toolchain/manifest, malé inkrementy
a přesný transitive axiom audit. Ukládej commity a aktuální per-package report.

Celý batch kontroluje skutečně neautorský kontrolní agent. Jiné ID ani
přejmenování původního autora nezávislost nedokazuje. Zaznamenej všechny
původní i nové autory a skutečnou identitu, neautorství a samostatný report
reviewera. Review porovná původní zdroj, hypotézy, všechny provider discharge,
consumer a CI/audit přesného SHA. Kontrolní role nesmí psát implementaci.

Po oprávněném nezávislém schválení integruj automaticky: jediný integrační
zámek i pro infrastrukturu, čerstvý main jako předek, schválený přesný PR head
se zeleným CI/auditem; potom merge se zachováním historie a zelený výsledný
main před ACCEPTED. Změna headu ruší schválení. Při selhání merged-main drž
zámek a vrať konkrétní problém přípravnému projektu. Větev coordination nikdy
nemerguj do main. Otevřené důkazy neoznačuj za dokončené.
