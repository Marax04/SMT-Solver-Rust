# Documento Tecnico Descrittivo — Ricostruzione di un Risolutore SMT in Rust Puro
## Pipeline completa di progettazione, architettura, teorie, tooling e roadmap

> Natura del documento: puramente descrittivo/architetturale. Nessun codice. Copre ogni fase, ogni sottosistema, ogni decisione progettuale necessaria per portare il progetto da zero a un motore SMT production-grade in Rust, con l'obiettivo esplicito di superare (non solo replicare) le capacità pratiche di Z3/cvc5 nei domini target (reverse engineering, binary analysis, verifica leggera).

---

## 0. Visione, obiettivi e vincoli di progetto

### 0.1 Perché "meglio di Z3" è un bersaglio ragionevole se ben definito
Z3 è generalista: deve reggere teoria dei tipi, quantificatori arbitrari, stringhe, floating point, datatypes induttivi, tutto con quindici anni di debito tecnico C++ e un'API enorme. Non è il target realistico "batterlo su tutto". Il target realistico e raggiungibile è: **essere strutturalmente superiore in un sottoinsieme di casi d'uso ben definiti** — bit-vector, EUF, aritmetica lineare, array — con:
- Prestazioni pari o superiori nel caso QF_BV/QF_ABV (il caso dominante in reverse engineering e symbolic execution).
- Sicurezza di memoria totale (niente UAF, niente data race) grazie a Rust, cosa che Z3 in C++ non garantisce.
- Osservabilità nativa (tracing strutturato, statistiche esportabili, replay deterministico) assente in Z3.
- Incrementalità e caching dei risultati progettati fin dal primo giorno, non aggiunti in un secondo momento come in Z3.
- API pensata per l'uso programmatico da motori di symbolic execution (tipo angr/S2E), non per essere un tool CLI generico.

### 0.2 Principi di design non negoziabili
- **Zero unsafe nel core logico.** L'unsafe, se necessario, è confinato a moduli di basso livello isolati e verificati (allocator custom, SIMD), mai nella logica di conflitto/backtracking.
- **Rappresentazione a indici, non a puntatori.** Ogni entità logica (variabile booleana, letterale, clausola, nodo AST, e-class, riga di simplex) è un indice numerico (`newtype` su `u32`/`u64`) dentro arena contigue (`Vec<T>` o `SlotMap`). Questo elimina il bisogno di `Rc<RefCell<>>` e rende le strutture dati cache-friendly e Send/Sync per il parallelismo futuro.
- **Separazione totale fra motore SAT booleano e teorie.** Il core CDCL non conosce alcuna teoria: comunica con le teorie tramite un'interfaccia fissa (trait) di propagazione/spiegazione/backtrack.
- **Determinismo riproducibile.** Ogni sessione di solving deve essere ri-eseguibile bit-per-bit dato lo stesso seed, essenziale per debugging e per confronto regressivo.
- **Incrementalità come primo cittadino.** Push/pop di assunzioni, riuso di clausole apprese fra query correlate, cache di risultati theory-level: non funzionalità aggiuntive, ma vincoli architetturali fin dal design delle strutture dati.
- **Compilazione a più target.** Libreria nativa (crate Rust), libreria C-ABI compatibile a livello concettuale con l'API C di Z3 (per permettere drop-in in progetti esistenti), e target WASM per uso in browser/tooling web.

### 0.3 Non-obiettivi espliciti (per non disperdere risorse)
Quantificatori del prim'ordine general-purpose con instantiation completa, teoria delle stringhe Unicode completa, floating point IEEE-754 completo bit-perfetto e datatypes co-induttivi complessi sono esplicitamente **fuori dal perimetro delle prime fasi**. Vanno pianificati come estensioni successive modulari, non bloccanti per il valore del prodotto (che già con EUF+BV+LIA+Array copre la stragrande maggioranza dei problemi di binary analysis, come confermano le architetture di riferimento CDCL(T) descritte da Nikolaj Bjørner per Z3[web:5] e la panoramica di Barrett e Tinelli sull'architettura DPLL(T)[web:7]).

---

## 1. Architettura generale a strati

La pipeline è organizzata in nove strati, ciascuno con un'interfaccia stabile verso lo strato successivo, per permettere sostituzione/evoluzione indipendente:

1. **Frontend/Parser** — ingestione SMT-LIB2, ingestione di un formato binario proprietario più compatto (per interoperare velocemente con tool di reverse engineering), e ingestione diretta via API Rust (constraint builder programmatico).
2. **Rappresentazione intermedia (IR) tipata** — AST con hash-consing, tipizzazione statica delle sort (Bool, BitVec(n), Int, Real, Array(idx,val), tipi definiti dall'utente).
3. **Preprocessore/Simplifier** — riscritture semanticamente equivalenti prima ancora di toccare il motore SAT.
4. **Bit-blaster / Theory Encoder** — traduzione (parziale o totale a seconda della teoria) verso CNF booleana o verso vincoli theory-level.
5. **Core SAT CDCL** — il motore booleano puro.
6. **Framework di Theory Solving e Theory Combination (CDCL(T)/Nelson-Oppen)** — l'orchestrazione fra SAT core e teorie.
7. **Theory Solvers specifici** — EUF, BV, LIA/LRA, Array, (poi) Datatypes/Strings/FP.
8. **Layer di Model Construction & Proof/Certificate Production** — costruzione del modello finale o della prova di UNSAT.
9. **API, tooling, osservabilità, infrastruttura di test/benchmark.**

Questa impostazione ricalca l'architettura CDCL(T) standard descritta nella letteratura (Nieuwenhuis et al., ripresa nella tesi di Barbosa[web:6] e nelle slide di riferimento di Griggio[web:12] e Tinelli[web:13]), ma con confini di modulo più rigidi, resi possibili dal sistema di trait di Rust, rispetto all'ereditarietà C++ usata in Z3/cvc5.

---

## 2. Strato 1-2: Frontend, IR e sistema dei tipi

### 2.1 Parser SMT-LIB2
Deve implementare lo standard SMT-LIB versione 2.6, inclusi: dichiarazioni di sort, funzioni non interpretate, `let`/`define-fun`, `push`/`pop` per l'incrementalità, `check-sat-assuming`, `get-model`, `get-unsat-core`, `get-proof` (facoltativo in fase iniziale), annotazioni (`!`) per pattern di istanziazione futuri. Il parser deve produrre errori diagnostici precisi (riga/colonna, span) per essere usabile in produzione, non solo per benchmark accademici.

### 2.2 Rappresentazione intermedia con hash-consing
Ogni nodo AST (operatore + figli + sort) viene internato in una tabella hash globale, così che espressioni strutturalmente identiche condividano lo stesso ID. Questo è cruciale per: deduplicazione automatica, memoizzazione di risultati di semplificazione, e per rendere il congruence closure (EUF) immediato sui nodi sintatticamente uguali. Il design a hash-consing con ID stabili è lo stesso principio dietro le e-graph del crate `egg`[web:16][web:29], che verrà eventualmente riusato o preso a riferimento diretto per la componente EUF.

### 2.3 Sistema dei tipi (sort system)
Le sort supportate nel core iniziale: Bool, BitVec(larghezza fissa a livello di tipo, non solo a runtime, per intercettare errori di mismatch a livello di IR), Int, Real, Array(SortIdx, SortIdx), Uninterpreted Sort parametrico. Ogni nodo AST porta con sé la sort risolta staticamente durante la costruzione, non a posteriori: questo elimina intere classi di bug di tipo che in Z3 emergono solo a runtime con assert falliti.

### 2.4 Politica di gestione degli errori
Tre categorie distinte devono essere separate nel design: errori di sintassi (parser), errori di tipo (sort mismatch), ed errori logici di sistema (timeout, memoria esaurita, teoria incompleta incontrata). Ognuna con un proprio canale di reporting strutturato (non semplici stringhe), per permettere a chi integra la libreria di reagire in modo differenziato.

---

## 3. Strato 3: Preprocessore e Simplifier

Prima di generare anche un solo letterale booleano, l'IR passa per una pipeline di trasformazioni equi-satisfacenti, ciascuna come passo indipendente e disattivabile (per permettere ablation testing):

- **Constant folding** ricorsivo su tutte le operazioni aritmetiche e bit-a-bit.
- **Riscrittura algebrica normalizzante**: ordinamento canonico di operatori commutativi, eliminazione di doppie negazioni, `x - x → 0`, `x & x → x`, semplificazioni di shift con costanti note.
- **Propagazione di uguaglianze a livello superficiale** (se `x = 5` appare come asserzione top-level, sostituire `x` con `5` ovunque).
- **Purificazione (Ackermannizzazione parziale)**: per funzioni non interpretate applicate a un numero ridotto di combinazioni di argomenti concreti, sostituzione diretta con variabili fresche più vincoli di uguaglianza, evitando di attivare l'intero motore EUF quando non serve.
- **Bit-vector range analysis**: inferenza statica di range di valori possibili per ridurre la larghezza effettiva di bit-blasting quando la larghezza dichiarata (es. 64 bit) eccede il range realmente raggiungibile.
- **CNF conversion via trasformazione di Tseitin** con introduzione di variabili ausiliarie solo dove necessario (evitando la blow-up esponenziale di una conversione CNF ingenua).
- **Definitional simplification per `let`**: espansione controllata per evitare duplicazione esponenziale di sotto-espressioni condivise (da qui l'importanza dell'hash-consing dello strato 2).

Ogni trasformazione deve essere accompagnata da una funzione di validazione interna (in modalità debug) che verifica l'equisoddisfacibilità su un campione di modelli casuali, per intercettare bug di riscrittura prima che si propaghino silenziosamente.

---

## 4. Strato 5: Il core SAT CDCL

Questo è il fondamento — la parte a "difficoltà media" ma dove ogni dettaglio implementativo incide sulle prestazioni per un ordine di grandezza.

### 4.1 Rappresentazione dati
- Letterali e variabili come interi (`Var(u32)`, `Lit(u32)` con codifica del segno nel bit meno significativo, tecnica standard usata da Minisat/Glucose e ripresa in `splr`[web:14]).
- Clausole in arena contigua con piccola ottimizzazione per clausole binarie (spesso tenute in liste separate, senza passare dal watcher generico).
- **Two-Watched Literals**: per ogni clausola si tracciano solo due letterali "sentinella"; la unit propagation aggiorna solo le clausole i cui watcher sono toccati, invece di scansionare l'intero database clausole.

### 4.2 Motore di decisione e propagazione
- **VSIDS** (Variable State Independent Decaying Sum) come euristica di branching di base, con possibilità di affiancare **LRB (Learning Rate Branching)** o **CHB (Conflict History-Based)**, euristiche più recenti che in molti benchmark superano VSIDS puro — questa è una delle prime aree dove si può "fare meglio dell'esistente" con un'implementazione moderna fin dal principio invece di ereditare VSIDS per compatibilità storica.
- **Trail** (stack delle assegnazioni) con livelli di decisione annotati per permettere backtracking non cronologico efficiente.
- **Restart adattivi** basati su media mobile del LBD (Literal Block Distance) delle clausole apprese, come nei solver moderni ispirati a Glucose.

### 4.3 Analisi dei conflitti
- Algoritmo **1-UIP (First Unique Implication Point)** per la derivazione della clausola di conflitto, standard de facto.
- **Clause minimization** post-1-UIP (ricorsiva e/o binaria) per accorciare le clausole apprese.
- **Clause database management**: eliminazione periodica (garbage collection) delle clausole apprese meno utili, tramite punteggio LBD combinato ad attività recente, per contenere la crescita di memoria.

### 4.4 Funzionalità aggiuntive rispetto a un CDCL "da manuale" (qui inizia il "meglio di")
- **Vivification e subsumption periodici** delle clausole apprese, tecniche presenti in `splr`[web:14] che riducono la ridondanza del database clausole.
- **Trail saving / phase saving avanzato** con rephasing periodico per accelerare la riconvergenza dopo un restart.
- **Interfaccia di propagazione bidirezionale con le teorie** progettata come trait fin dal primo giorno (vedi sezione 6), invece di essere "innestata" successivamente come spesso accade in solver SAT-only convertiti in SMT-only in un secondo tempo.
- **Produzione di un certificato DRAT** (Deletion Resolution Asymmetric Tautology) per ogni derivazione UNSAT, per permettere verifica esterna indipendente della correttezza — funzionalità che rafforza la fiducia nel motore, specialmente critica in un contesto di reverse engineering dove un falso UNSAT porta a conclusioni di sicurezza errate.

---

## 5. Strato 6: CDCL(T) e Theory Combination

### 5.1 Interfaccia teoria-motore
Ogni teoria implementa un'interfaccia comune con responsabilità precise:
- **Assert**: ricevere un letterale theory-atom diventato vero/falso nel trail booleano.
- **Check**: verificare la consistenza dell'insieme corrente di asserzioni theory-level.
- **Explain**: se inconsistente, produrre una clausola di conflitto minimale (in termini dei letterali booleani astratti) da restituire al core SAT.
- **Propagate**: opzionalmente, dedurre e restituire nuovi letterali impliciti prima ancora che il SAT core li scelga per decisione, riducendo lo spazio di ricerca.
- **Push/Pop**: per l'integrazione con il backtracking non cronologico e con l'incrementalità a livello di `check-sat-assuming`.

### 5.2 Combinazione di teorie: Nelson-Oppen
Per teorie con segnatura disgiunta e stabilmente infinite (EUF, LIA/LRA), la combinazione avviene tramite il metodo classico di Nelson-Oppen: purificazione della formula in sotto-formule per teoria, condivisione delle sole uguaglianze implicite fra variabili condivise, iterazione fino a fixpoint[web:1][web:3][web:8]. In alternativa più moderna e meno "a indovinello" del non-deterministic Nelson-Oppen, si adotta l'approccio **model-based theory combination**: ogni teoria produce un modello candidato completo, e solo le uguaglianze realmente in conflitto fra i modelli vengono propagate, riducendo drasticamente le combinazioni da esplorare rispetto al Nelson-Oppen classico a indovinello descritto nelle dispense di riferimento[web:2].

### 5.3 Equality engine centralizzato
Come fanno cvc5 e Z3[web:10], invece di lasciare che ogni teoria gestisca la propria nozione di uguaglianza in modo indipendente, si progetta un **equality engine condiviso**: un unico union-find/congruence-closure centrale a cui tutte le teorie si registrano, notificando ed osservando le uguaglianze rilevanti. Questo evita duplicazione di logica e incoerenze fra teorie diverse che ragionano sulla stessa variabile.

---

## 6. Strato 7: Theory Solvers — dettaglio per teoria

### 6.1 EUF (Equality and Uninterpreted Functions)
- Algoritmo di **congruence closure** su union-find con path compression e union by rank, con code di lavoro per la propagazione delle congruenze indotte (se `f(a)=f(b)` e `a=b`).
- Rappresentazione a **e-graph**: si valuta l'adozione diretta o l'ispirazione architetturale dal crate `egg`[web:16][web:29], che offre già rebuilding ammortizzato delle invarianti di congruenza e "e-class analysis" per integrare analisi custom (ad esempio propagazione di intervalli numerici direttamente dentro l'e-graph)[web:26]. Per un motore SMT servirà una variante specializzata per l'uso incrementale con backtracking, diversa dall'uso batch tipico di equality saturation.
- Generazione di spiegazioni (explanation) minimali per ogni conflitto EUF, necessarie per costruire clausole di conflitto compatte da restituire al SAT core.

### 6.2 Aritmetica Lineare (LRA/LIA) — Simplex incrementale
- Nucleo: **algoritmo di Dutertre e de Moura**, lo standard de facto adottato da praticamente tutti gli SMT solver moderni (Z3, CVC4/cvc5, MathSAT, Yices, OpenSMT, SMTInterpol)[web:19][web:22][web:24][web:28]. Si tratta di una variante del simplex duale pensata specificamente per DPLL(T): variabili partizionate in basiche/non basiche, tableau sparso, bound superiori/inferiori per variabile, pivoting che preserva la fattibilità delle variabili non basiche.
- Supporto nativo per **disuguaglianze strette** tramite l'estensione con infinitesimi simbolici (il parametro delta), come nella formulazione originale[web:21].
- Per **LIA (interi)**: branch-and-bound sopra il layer LRA, con tagli di Gomory/Chvátal per accelerare la convergenza e GCD test per potare rami interi infeasibili in anticipo[web:25].
- Variante avanzata da valutare in fase successiva: **Simplex con Sum-of-Infeasibilities**, che migliora la ricerca euristica del punto di partenza rispetto al Simplex classico Dutertre-de Moura in istanze grandi[web:19] — un'area concreta dove superare le implementazioni "di manuale".
- Incrementalità: il tableau deve supportare push/pop dei bound in tempo costante ammortizzato, mantenendo una history stack dei cambiamenti di bound per il backtracking, non ricostruendo il tableau da zero ad ogni chiamata.

### 6.3 Bit-Vector (QF_BV) — la teoria centrale per il caso d'uso reverse engineering
Due strategie complementari, entrambe da implementare:
1. **Bit-blasting completo**: ogni bit di ogni variabile bit-vector diventa una variabile booleana; operatori (`add`, `sub`, `mul`, `and`, `or`, `xor`, `shl`, `lshr`, `ashr`, confronti) vengono tradotti in circuiti booleani (adder ripple-carry o carry-lookahead per la somma, moltiplicatore shift-and-add o Booth per la moltiplicazione) e poi in CNF via trasformazione di Tseitin. È l'approccio più semplice da rendere corretto e già sufficiente per molti crackme e predicati di reverse engineering.
2. **Word-level reasoning con lazy bit-blasting**: prima di esplodere in bit, si applicano riscritture a livello di parola (constant propagation su interi a precisione arbitraria, riconoscimento di pattern come confronti con maschere, range analysis) e si effettua bit-blasting solo sulle sotto-espressioni che restano non risolte simbolicamente. Questo è l'elemento chiave per "fare meglio" del bit-blasting ingenuo descritto nella richiesta iniziale: mitiga esattamente il problema di esplosione con moltiplicazioni/divisioni ampie, applicando prima semplificazione algebrica e delegando al SAT core solo il residuo davvero necessario.
- **Ottimizzazione mirata al reverse engineering**: cache di sotto-circuiti bit-blasted già codificati (per pattern ricorrenti come CRC, controlli di parità, S-box), dato che nei crackme le stesse sotto-espressioni ricorrono spesso fra chiamate successive al solver durante un'esplorazione simbolica.

### 6.4 Teoria degli Array
- Assiomi di **read-over-write** istanziati lazy (solo quando servono, non tutti a priori), con euristiche di selezione basate sui pattern di accesso osservati nel modello candidato corrente — pattern standard nei solver moderni per evitare la blow-up combinatoria degli assiomi array su array grandi/simbolici.
- Estensione a **array parzialmente concreti** (memoria concreta + regioni simboliche), rilevante per la modellazione di memoria in binary analysis, dove gran parte dello spazio degli indirizzi è concreto e solo poche celle sono simboliche.

### 6.5 Teorie pianificate come estensioni successive (non bloccanti)
- **Datatypes algebrici** (per modellare strutture/enum durante reverse engineering di formati binari).
- **Floating point IEEE-754** tramite bit-blasting dei componenti (segno, esponente, mantissa) più circuiti dedicati per arrotondamento.
- **Stringhe** con automi/lunghezze simboliche, utile per analisi di parser e protocolli.

---

## 7. Strato 8: Costruzione del modello e produzione di prove

- **Model construction**: al termine di un check-sat SAT, assemblare un modello concreto leggibile (valori concreti per ogni variabile bit-vector/intera/reale/array), validato internamente ri-eseguendo la formula originale contro il modello prima di restituirlo all'utente — un controllo di sanità che intercetta bug silenziosi.
- **Unsat core minimization**: dato un insieme di asserzioni etichettate, restituire un sottoinsieme minimale responsabile dell'insoddisfacibilità, fondamentale per il debug di vincoli complessi generati da symbolic execution.
- **Proof production strutturata**: oltre al certificato DRAT per il livello SAT puro, produrre un log strutturato dei passi di deduzione theory-level (in un formato interno ispezionabile), anticipando un formato di proof-export compatibile con verificatori esterni in una fase successiva.

---

## 8. Strato 9: API, osservabilità e tooling di ecosistema

### 8.1 Superficie API
- **API Rust nativa** basata su builder pattern per costruire formule programmaticamente, pensata per essere ergonomica da usare da un motore di symbolic execution scritto anch'esso in Rust.
- **API C-ABI** che replica per quanto ragionevole le funzioni più usate della C API di Z3 (`Z3_mk_*`, `Z3_solver_check`, ecc.), per permettere una migrazione a basso attrito ai progetti esistenti che oggi dipendono da Z3 via FFI.
- **Bindings Python** generati automaticamente dalla API C-ABI, dato che è l'ecosistema dominante per tool di reverse engineering (angr, tool basati su claripy).
- **Target WebAssembly** per uso in tool basati su browser/VS Code extension.

### 8.2 Osservabilità
- Tracing strutturato (span per ogni fase: parsing, preprocessing, ogni chiamata theory, ogni conflitto) esportabile in formato compatibile con `tracing`/OpenTelemetry, per profiling fine-grained — capacità che Z3 non offre nativamente.
- Statistiche runtime esportabili in JSON (numero di conflitti, decisioni, restart, dimensione clausole apprese, tempo per teoria) per permettere dashboard di regressione prestazionale automatizzate.
- Modalità di **replay deterministico**: dato un log di sessione, ri-eseguire esattamente la stessa sequenza di decisioni per riprodurre bug non deterministici.

### 8.3 Fuzzing e testing differenziale
- **Generatore grammar-based di formule SMT-LIB** casuali (per sort e per teoria), per fuzzing strutturato.
- **Testing differenziale automatizzato contro Z3 e cvc5**: ogni formula generata viene risolta da tutti e tre i solver; ogni disaccordo (SAT vs UNSAT) è per definizione un bug e va loggato con la formula minimizzata (delta-debugging/ddmin) per riproducibilità.
- **Metamorphic testing**: applicare trasformazioni che preservano la satisfiabilità (rinominazione variabili, negazione doppia, riordino conjunctions) e verificare che il risultato non cambi.
- **Benchmark suite**: import automatico della libreria SMT-LIB pubblica (categorie QF_BV, QF_LIA, QF_LRA, QF_AUFBV) e dei benchmark della SAT Competition per il solo layer SAT[web:27], con dashboard storica di tempo/memoria per commit, per intercettare regressioni prestazionali in CI.

### 8.4 Infrastruttura di continuous integration
Pipeline CI multi-piattaforma (Linux, Windows, target WASM) con tre livelli di test ad ogni commit: unit test per ogni modulo isolato, test di integrazione su un sottoinsieme rappresentativo della benchmark suite con limite di tempo, e job notturno esteso che esegue l'intera suite con testing differenziale contro Z3/cvc5.

---

## 9. Funzionalità "oltre Z3" — differenziatori concreti

Questa sezione elenca esplicitamente le direzioni dove il progetto punta a superare, non solo eguagliare, lo stato dell'arte:

- **Safety di memoria totale** grazie a Rust: nessuna classe di bug (use-after-free, buffer overflow, data race) presente nel codebase C++ di Z3 può esistere qui per costruzione.
- **Cache persistente di sotto-problemi risolti** fra invocazioni successive dello stesso processo host (utile per motori di symbolic execution che interrogano il solver migliaia di volte su formule quasi identiche a un path-branch di distanza), con hashing strutturale delle sotto-formule condivise.
- **Parallelismo a portfolio nativo**: più istanze del motore CDCL con euristiche di branching diverse (VSIDS, LRB, CHB) eseguite in thread paralleli su thread nativi Rust con condivisione di clausole apprese via canali lock-free, secondo il modello portfolio usato dai solver SAT competitivi moderni[web:27], ma progettato fin dal principio invece di essere un ripensamento tardivo.
- **Rephasing e restart guidati da statistiche esportate**, con la possibilità futura di innestare euristiche apprese offline (modelli leggeri per selezione euristica) senza dover ristrutturare il core.
- **Word-level bit-vector reasoning con propagazione di intervalli integrata nell'e-graph** (e-class analysis alla `egg`[web:16]), per ridurre sistematicamente la dimensione del bit-blasting rispetto a un bit-blaster ingenuo — un'area dove l'implementazione descritta nella query originale (bit-blasting puro) viene esplicitamente superata.
- **Certificati di prova verificabili indipendentemente** (DRAT + log theory-level) come funzionalità di prima classe, per un uso credibile in contesti di security research dove un errore silenzioso del solver ha conseguenze pratiche.
- **Formato di serializzazione binario proprietario** per formule e modelli, molto più compatto e veloce da (de)serializzare rispetto a SMT-LIB testuale, per pipeline di analisi automatizzata ad alto volume.

---

## 10. Roadmap in fasi con criteri di uscita misurabili

**Fase 0 — Fondamenta (infrastruttura, non solving).**
Setup workspace Cargo multi-crate (separazione netta: `sat-core`, `smt-ir`, `theories`, `api`, `cli`), sistema di tipi IR con hash-consing, parser SMT-LIB2 minimale, infrastruttura di test differenziale contro Z3 già collegata da subito (anche se il motore ancora non risolve nulla, la pipeline di confronto va pronta presto).
Criterio di uscita: parsing corretto del 100% di un sottoinsieme di benchmark SMT-LIB QF_BV senza crash.

**Fase 1 — Core SAT CDCL.**
Two-watched literals, VSIDS, 1-UIP, restart basati su LBD, clause database management.
Criterio di uscita: risolvere una porzione significativa dei benchmark della SAT Competition entro un budget di tempo comparabile (stesso ordine di grandezza, non necessariamente competitivo) con `splr`/`varisat`[web:14].

**Fase 2 — Bit-blasting QF_BV puro + CNF pipeline completa.**
Traduzione diretta di espressioni bit-vector in CNF, senza ancora CDCL(T) vero e proprio.
Criterio di uscita: risolvere crackme reali e predicati di reverse engineering noti in tempi ragionevoli, validati contro Z3 su un corpus di formule reali estratte da binari.

**Fase 3 — Framework CDCL(T) + EUF.**
Interfaccia theory-solver generica, equality engine centralizzato, congruence closure.
Criterio di uscita: superare correttamente (stesso risultato SAT/UNSAT) il 100% della categoria QF_UF di SMT-LIB su un campione rappresentativo.

**Fase 4 — LRA/LIA via Simplex Dutertre-de Moura.**
Criterio di uscita: parità di risultati con Z3 su QF_LRA/QF_LIA campionati, con tempo entro un fattore accettabile definito a priori (es. non più di 5x più lento in questa fase iniziale, da migliorare in fasi successive).

**Fase 5 — Nelson-Oppen / model-based combination fra EUF+LRA+BV, teoria Array.**
Criterio di uscita: risolvere correttamente formule QF_AUFBV miste, il caso più rappresentativo per binary analysis reale.

**Fase 6 — Hardening: fuzzing intensivo, proof production, ottimizzazione prestazionale mirata (profiling e riduzione allocazioni), parallelismo a portfolio.**
Criterio di uscita: zero disaccordi non spiegati contro Z3/cvc5 su fuzzing esteso di 72+ ore continuative; certificati DRAT verificabili su tutte le istanze UNSAT testate.

**Fase 7 — Estensioni facoltative**: Datatypes, Floating Point, Stringhe, quantificatori con E-matching, bindings multi-linguaggio, target WASM.

Ogni fase deve produrre un report di benchmark comparativo pubblico (tempo, memoria, tasso di successo) rispetto alla fase precedente e rispetto a Z3/cvc5, per rendere misurabile ogni affermazione di "miglioramento".

---

## 11. Rischi principali e mitigazioni

- **Rischio di correttezza silenziosa** (il solver risponde SAT/UNSAT sbagliato senza crashare): mitigato strutturalmente dal testing differenziale continuo e dalla validazione dei modelli prodotti (sezione 7).
- **Esplosione combinatoria nel bit-blasting** su moltiplicazioni/divisioni larghe: mitigata dal word-level reasoning pre-bit-blasting (sezione 6.3) e da limiti di preprocessing configurabili.
- **Complessità della combinazione di teorie**: è storicamente la parte più soggetta a bug sottili anche nei solver maturi; mitigata iniziando con solo due teorie disgiunte (EUF+LRA) prima di aggiungere BV e Array, seguendo rigorosamente l'ordine di fase della roadmap.
- **Sottostima dell'impegno ingegneristico**: un motore CDCL(T) production-grade con quattro teorie integrate è dell'ordine delle decine di migliaia di righe di Rust, non poche migliaia — la stima di 2.000-5.000 righe menzionata per un bit-blaster essenziale copre solo la Fase 2, non l'intera pipeline qui descritta.

---

## Riferimenti tecnici principali consultati

Architettura CDCL(T)/DPLL(T) e combinazione di teorie: panoramica Z3 di Bjørner[web:5], note di Barrett e Tinelli[web:7], dispense ETH Zürich e CMU sulla combinazione Nelson-Oppen[web:1][web:2][web:3], tesi di Barbosa su CDCL(T)[web:6], slide di Griggio[web:12] e Tinelli[web:13], architettura interna cvc5[web:10]. Simplex per aritmetica lineare: paper originale Dutertre-de Moura[web:28], estensione Sum-of-Infeasibilities[web:19], note su LIA con branch-and-bound[web:25]. E-graph e congruence closure: libreria `egg`[web:16][web:29] e relative analisi successive[web:26]. Riferimenti SAT-core Rust esistenti: `splr`[web:14]. Benchmark SAT competitivo: SAT Competition 2023[web:27].
