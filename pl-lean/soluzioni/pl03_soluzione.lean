/-
Il seguente `import` serve a portare qui le definizioni della lezione precedente.

Se stai lavorando su `https://live.lean-lang.org/`, rimuovi l'`import` e
copia-incolla il codice della lezione precedente prima di questa.
-/
import PL_Lean.PL02_Nat


set_option autoImplicit false


/-
# Induzione strutturale

Nella lezione precedente abbiamo definito funzioni ricorsive sui numeri naturali.
In questa lezione impariamo la tecnica dimostrativa corrispondente: l'*induzione strutturale*.

Alla fine della lezione dovresti essere in grado di:

* riconoscere quando l'analisi per casi è insufficiente e serve l'induzione;
* identificare il caso base, il caso induttivo e l'ipotesi induttiva;
* scegliere la variabile di induzione guardando la definizione ricorsiva coinvolta;
* usare `rw`, `exact` e `simp` insieme a un'ipotesi induttiva;
* eseguire induzione strutturale su altri dati strutturati oltre a `Nat`.
-/


section Induction

/-
## Induzione: la controparte dimostrativa della ricorsione

Nella lezione precedente abbiamo notato che l'analisi per casi non basta per
dimostrare `addN 0 n = n`: nel caso successore otteniamo il goal per `k + 1`,
ma per risolverlo dobbiamo conoscere il risultato per `k`. Questo è esattamente
ciò che fornisce l'*induzione matematica*.

Supponiamo di voler dimostrare una proprietà `P n` per ogni numero naturale `n`.
Il principio di induzione dice che è sufficiente dimostrare:

1. `P 0`                       -- il caso base;
2. `P n -> P (n + 1)`          -- il caso induttivo.

La seconda parte dice che se la proprietà è vera per un `n` arbitrario, allora
è vera per il suo successore.

In Lean, la tattica `induction` espone esattamente questi casi. Nel caso induttivo,
otteniamo anche l'*ipotesi induttiva* `ih`: l'enunciato per il numero più piccolo.

-/

#check addN_succ_right    -- questo lemma sarà usato nella dimostrazione: controllalo

theorem zero_addN (n : Nat) : addN 0 n = n := by
  induction n with
  | zero => rfl               -- caso base
  | succ n' ih =>             -- caso induttivo (nota `ih` nella Infoview)
      rw [addN_succ_right]    -- addN 0 (n' + 1) -> (addN 0 n') + 1
      rw [ih]

/-
Seguiamo la dimostrazione. Dopo `induction n with`, Lean mostra due goal:

    case zero:   addN 0 0 = 0
    case succ:   ih : addN 0 n' = n'
                 ⊢ addN 0 (n' + 1) = n' + 1

* Il primo goal segue per calcolo, quindi `rfl` funziona.
* Nel secondo goal, usiamo due riscritture:
  1. `rw [addN_succ_right]` riscrive `addN 0 (n' + 1)` in `addN 0 n' + 1`.
  2. `rw [ih]` sostituisce `addN 0 n'` con `n'`, e il goal diventa `n' + 1 = n' + 1`,
     che `rw` chiude da solo (senza uso esplicito di `rfl`).

Questa dimostrazione evidenzia una corrispondenza importante:

    PROGRAMMAZIONE               DIMOSTRAZIONE
    ------------------------------------------------
    match n with ...             cases n with ...
    chiamata ricorsiva su n'     ipotesi induttiva su n'
    caso base                    caso base
    caso ricorsivo               caso induttivo

La dimostrazione ha la stessa forma della funzione ricorsiva di cui parla.

-/

/-
### Scegliere la variabile di induzione

Come altro esempio, consideriamo una variante di `addN_succ_right` dove il
successore è nel primo argomento. Il teorema contiene due variabili, quindi
dobbiamo decidere su quale indurre.

La scelta utile è `m`, perché `addN` esamina il suo secondo argomento. Dopo
aver diviso `m` in `0` e `m' + 1`, le equazioni di definizione di `addN`
diventano disponibili, e l'ipotesi induttiva descrive esattamente la chiamata
ricorsiva.

Una regola pratica utile è:

    Guarda la definizione che è bloccata, e induci sull'argomento su cui
    quella definizione ricorre.

Come esperimento, prova a sostituire `induction m` sotto con `induction n` e
ispeziona l'ipotesi induttiva risultante. Lean accetta il comando, ma l'ipotesi
non descrive la chiamata ricorsiva di cui abbiamo bisogno.
-/

theorem addN_succ_left (n m : Nat) : addN (n + 1) m = addN n m + 1 := by
  induction m with
  | zero => rfl
  | succ m' ih =>
    rw [addN_succ_right]      -- riscrive addN_succ_right nel lato sinistro di =
    rw [addN_succ_right]      -- riscrive addN_succ_right nel lato destro di =
    rw [ih]

/-
Nella dimostrazione precedente, avremmo potuto semplicemente scrivere:
  | succ m' ih => rw [addN_succ_right,addN_succ_right,ih]
Ho diviso le riscritture in tre passi così puoi controllare i loro effetti nella Infoview.

Le dimostrazioni tattiche di questa forma sono spesso scritte in modo più breve
usando `simp`, che riscrive ripetutamente usando le definizioni e i lemmi che gli
diamo. Ad esempio, il caso induttivo sopra potrebbe essere scritto

    | succ m' ih => simp [addN, ih]

Useremo entrambi gli stili. La versione esplicita con `rw` è migliore per capire
la dimostrazione passo-passo, `simp` è più veloce da scrivere.
-/

/-
Possiamo ora dimostrare la commutatività della nostra funzione di addizione.
-/

theorem addN_comm (n m : Nat) : addN n m = addN m n := by
  induction m with
  | zero =>
    rw [addN_zero]
    rw [zero_addN]
  | succ m' ih =>
    rw [addN_succ_right]
    rw [addN_succ_left]
    rw [ih]

/-
La dimostrazione sopra è una tappa importante. Siamo passati da un breve
programma ricorsivo a una proprietà matematica sul programma, e Lean ha
verificato la dimostrazione meccanicamente.
-/

end Induction



section Boolean_expressions

/-
## L'induzione strutturale non è solo induzione sui numeri

La forma di una dimostrazione per induzione è determinata dai costruttori del tipo.
Per `Nat`, i valori formano una catena lineare:

    0, succ 0, succ (succ 0), ...

Di conseguenza, il caso induttivo ha un solo valore più piccolo e una sola
ipotesi induttiva. Altri tipi induttivi possono ramificarsi.

Come esempio, considera la sintassi delle espressioni booleane:

    t ::= true | false | if t₀ then t₁ else t₂

Questo è un tipo di dato ad albero. Un'espressione `if` contiene tre espressioni
booleane più piccole.
-/

inductive BExp where
  | btrue  : BExp
  | bfalse : BExp
  | bifte  : BExp → BExp → BExp → BExp
  deriving Repr

/-

La funzione `evalBExp` valuta un'espressione booleana per ricorsione strutturale.
Segue le stesse clausole della *semantica big-step*.

Scrivendo `t ⇒ v` per "l'espressione `t` si valuta al valore booleano `v`", le
regole sarebbero:

-----------------          ------------------
  btrue ⇒ true               bfalse ⇒ false

  t0 ⇒ true    t1 ⇒ v          t0 ⇒ false    t2 ⇒ v
-------------------------      --------------------------
 bifte t0 t1 t2 ⇒ v             bifte t0 t1 t2 ⇒ v

Qui implementiamo quelle regole come una funzione, dato che sappiamo già che ogni
espressione ha uno ed un solo risultato booleano determinato. Nelle lezioni
successive formalizzeremo la semantica operazionale come relazioni induttivamente
definite.

-/

def evalBExp : BExp → Bool
  | .btrue          => true
  | .bfalse         => false
  | .bifte t0 t1 t2 => if evalBExp t0 then evalBExp t1 else evalBExp t2


example :
    let ex0 := .bifte (.bifte .bfalse .btrue .bfalse) .btrue .bfalse
    evalBExp ex0 = false := by rfl

/-
Ecco un'altra funzione strutturalmente ricorsiva. `dualBExp` scambia `true` e `false`.
Ad ogni condizionale, dualizza la condizione e scambia anche i due rami.
-/

def dualBExp : BExp → BExp
  | .btrue        => .bfalse
  | .bfalse       => .btrue
  | .bifte t0 t1 t2 =>
      .bifte (dualBExp t0) (dualBExp t2) (dualBExp t1)

/-
Applicare `dualBExp` due volte dà di nuovo l'espressione originale. La dimostrazione
usa l'induzione strutturale su `t`.

Ci sono tre casi, uno per ogni costruttore. Nota che il caso `bifte` fornisce
*tre* ipotesi induttive, perché `bifte` ha tre argomenti ricorsivi:

    ih0 : dualBExp (dualBExp t0) = t0
    ih1 : dualBExp (dualBExp t1) = t1
    ih2 : dualBExp (dualBExp t2) = t2

Questa è la principale differenza rispetto all'induzione su `Nat`, il cui
costruttore `succ` ha un solo argomento ricorsivo.
-/

theorem dualBExp_involutive (t : BExp) : dualBExp (dualBExp t) = t := by
  induction t with
  | btrue   => rfl
  | bfalse  => rfl
  | bifte t0 t1 t2 ih0 ih1 ih2 =>
      rw [dualBExp]         -- srotola l'applicazione esterna di dualBExp
      rw [dualBExp]         -- srotola l'applicazione rimanente
      rw [ih0, ih1, ih2]    -- applica le tre ipotesi induttive

/-
Nel caso `bifte`, le prime due riscritture calcolano le due applicazioni di
`dualBExp`. Il goal risultante contiene una doppia applicazione per ogni
sottoalbero. L'ultima riga usa le tre ipotesi induttive per sostituire quelle
espressioni con `t0`, `t1` e `t2`.

L'induzione strutturale segue la dichiarazione del tipo di dato:

* viene generato un caso di dimostrazione per ogni costruttore;
* viene generata un'ipotesi induttiva per ogni argomento ricorsivo del costruttore.

L'induzione non riguarda specificamente i numeri. È un modo di dimostrare una
proprietà per ogni valore finito generato da una definizione induttiva.
-/

end Boolean_expressions



section Exercises

/-
## Esercizi

Le etichette di difficoltà sono relative a questa lezione:

* **1/4 -- riscaldamento:** un'idea o calcolo diretto;
* **2/4 -- standard:** un'induzione di routine con un'ipotesi induttiva utile;
* **3/4 -- sostanziale:** diversi lemmi o un'analisi per casi aggiuntiva;
* **4/4 -- sfida:** pianificazione della dimostrazione e una lunga catena di riscritture.

Gli esercizi sono raggruppati per argomento, non strettamente per difficoltà.
Un buon percorso iniziale è fare tutti gli esercizi valutati 1/4 e 2/4, poi
tornare agli esercizi più difficili su moltiplicazione e alberi sintattici.
La difficoltà dipende anche da quanti suggerimenti usi.

-/


/-
### Esercizio: Sommare successori

**Difficoltà: 1/4 (riscaldamento).**

Questo non richiede induzione. Usa `addN_succ_right` e `addN_succ_left`.
-/

theorem addN_self_succ (n : Nat) : addN (n + 1) (n + 1) = addN n n + 1 + 1 := by
  rw [addN_succ_right]
  rw [addN_succ_left]

/-
### Esercizio: Associatività di addN

**Difficoltà: 2/4 (induzione standard).**

Dimostra che `addN` è associativa.

Suggerimento: induzione su `k`. Nel caso successore, srotola le addizioni con
`addN_succ_right`, e finisci con l'ipotesi induttiva.
-/

theorem addN_assoc (n m k : Nat) : addN (addN n m) k = addN n (addN m k) := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    rw [addN_succ_right]
    rw [addN_succ_right]
    rw [addN_succ_right]
    rw [ih]

/-
### Esercizio: Zero è assorbente a sinistra per mulN

**Difficoltà: 2/4 (induzione standard).**

Dimostra che moltiplicare per zero a sinistra dà zero.
Suggerimento: induci su `n`. Nel caso successore, riscrivi con
`mulN_succ_right`, poi usa l'ipotesi induttiva. L'uguaglianza rimanente
vale per calcolo.
-/

theorem mulN_zero_left (n : Nat) : mulN 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [mulN_succ_right]
    rw [ih]
    rfl


/-
### Esercizio: Uno è identità a sinistra per mulN

**Difficoltà: 2/4 (induzione standard).**

Dimostra che uno è un'identità a sinistra per `mulN`.

Suggerimento: induci su `n`. Nel caso successore, usa `mulN_succ_right` e
l'ipotesi induttiva. L'uguaglianza rimanente segue per calcolo.
-/

#check mulN_succ_right

theorem mulN_one_left (n : Nat) : mulN 1 n = n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [mulN_succ_right]
    rw [ih]
    rfl


/-
### Esercizio: Moltiplicazione di un successore (sinistra)

**Difficoltà: 4/4 (sfida).** È ragionevole saltarlo in una prima passata.

La definizione di `mulN` ricorre sul suo *secondo* argomento, quindi `mulN (n + 1) m`
non può essere calcolato finché non sappiamo qualcosa su `m`. Pertanto:

Suggerimento 1: procedi per induzione su `m`.

Suggerimento 2 (caso base): usa `mulN_zero_right`.

Suggerimento 3 (caso successore): scrivi `x` per `mulN n m'` e segui il goal
nella Infoview. La dimostrazione ha tre fasi.

1. Srotola le moltiplicazioni: riscrivi con `mulN_succ_right`. Deve essere
   usato due volte, una per ciascun lato. Poi usa l'ipotesi induttiva `ih`
   per rimuovere il rimanente `mulN (n + 1) m'`. Ora entrambi i lati sono
   addizioni di `x` e dei due numeri `m'` e `n`:

       addN (addN x m') (n + 1)  =  addN (addN x n) (m' + 1)

2. Estrai i successori: riscrivi con `addN_succ_right` (due volte). Ora entrambi
   i lati terminano con `+ 1`.

3. I numeri `m'` e `n` appaiono in ordine diverso sui due lati.
   Questo non è un calcolo: ci servono *associatività* e *commutatività*
   dell'addizione. Usa `addN_assoc` (due volte) per raggruppare entrambi i lati
   come `addN x (addN _ _)`, e `addN_comm` con argomenti espliciti per scambiare
   `m'` e `n`.
-/

theorem mulN_succ_left (n m : Nat) : mulN (n + 1) m = addN (mulN n m) m := by
  induction m with
  | zero =>
    rw [mulN_zero_right]
    rw [mulN_zero_right]
    rfl
  | succ m' ih =>
    rw [mulN_succ_right]
    rw [mulN_succ_right]
    rw [ih]
    rw [addN_succ_right]
    rw [addN_succ_right]
    rw [addN_assoc]
    rw [addN_assoc]
    rw [addN_comm m' n]


/-
### Esercizio: Commutatività di mulN

**Difficoltà: 2/4 una volta che `mulN_succ_left` è disponibile.**

Dimostra che la moltiplicazione è commutativa (teorema `mulN_comm`).

Suggerimento: nel caso induttivo, sfrutta `mulN_succ_right` e `mulN_succ_left`.
-/

theorem mulN_comm (n m : Nat) : mulN n m = mulN m n := by
  induction m with
  | zero =>
    rw [mulN_zero_right]
    rw [mulN_zero_left]
  | succ m' ih =>
    rw [mulN_succ_right]
    rw [mulN_succ_left]
    rw [ih]


/-
### Esercizio: La moltiplicazione distribuisce sull'addizione (sinistra)

**Difficoltà: 3/4 (sostanziale).**

Dimostra che la moltiplicazione distribuisce sull'addizione:

    a * (b + c)  =  a * b + a * c

Su quale variabile dovremmo indurre? Guarda le definizioni:

* `mulN a n` ricorre sul suo *secondo* argomento `n`;
* `addN b c` ricorre sul suo secondo argomento `c`.

Nel lato sinistro `mulN a (addN b c)`, il numero `addN b c` è il secondo
argomento di `mulN`. Se `c` è un successore, allora `addN b c` è anch'esso un
successore, e `mulN` può quindi srotolarsi. Quindi la scelta naturale è
l'induzione su `c`.
-/

theorem mulN_addN_distrib_left (a b c : Nat) : mulN a (addN b c) = addN (mulN a b) (mulN a c) := by
  induction c with
  | zero =>
    rw [addN_zero]
    rw [mulN_zero_right]
    rw [addN_zero]
  | succ c' ih =>
    rw [addN_succ_right]
    rw [mulN_succ_right]
    rw [ih]
    rw [mulN_succ_right]
    rw [addN_assoc]


/-
#### Sfida opzionale: scegliere una variabile di induzione meno conveniente

**Difficoltà: 4/4.**

La seguente dimostrazione stabilisce lo stesso risultato per induzione su `a`.
Questa scelta è valida, ma richiede molti più riarrangiamenti algebrici. Illustra
perché scegliere la variabile che controlla la definizione ricorsiva bloccata
di solito porta a una dimostrazione più chiara.
-/

theorem mulN_addN_distrib_left_by_first_arg (a b c : Nat) :
    mulN a (addN b c) = addN (mulN a b) (mulN a c) := by
  induction a with
  | zero =>
    rw [mulN_zero_left]
    rw [mulN_zero_left]
    rw [mulN_zero_left]
    rfl
  | succ a' ih =>
    rw [mulN_succ_left]
    rw [mulN_succ_left]
    rw [mulN_succ_left]
    rw [ih]
    rw [addN_assoc]
    rw [addN_assoc]
    rw [addN_comm]


/-
### Esercizio: Associatività di mulN

**Difficoltà: 3/4 (sostanziale).**

Dimostra che la moltiplicazione è associativa (teorema `mulN_assoc`).

Suggerimento: nel caso induttivo, sfrutta `mulN_addN_distrib_left`.
-/

theorem mulN_assoc (n m k : Nat) : mulN (mulN n m) k = mulN n (mulN m k) := by
  induction k with
  | zero =>
    rw [mulN_zero_right]
    rw [mulN_zero_right]
  | succ k' ih =>
    rw [mulN_succ_right]
    rw [mulN_succ_right]
    rw [ih]
    rw [mulN_addN_distrib_left]


/-
### Esercizio: Riflessività di eqN

**Difficoltà: 1/4 (riscaldamento).**

Dimostra che `eqN` è riflessiva. Suggerimento: procedi per induzione su `a`, e usa
la tattica `exact`.
-/

theorem eqN_refl (a : Nat) : eqN a a = true := by
  induction a with
  | zero => rfl
  | succ a' ih => exact ih


/-
### Esercizio: Riflessività di leN

**Difficoltà: 1/4 (riscaldamento).**

Dimostra che ogni numero naturale è minore o uguale a se stesso. La dimostrazione
ha la stessa forma induttiva di `eqN_refl`.

def leN : Nat → Nat → Bool
  | 0,     _     => true
  | _ + 1, 0     => false
  | n + 1, m + 1 => leN n m

-/

theorem leN_refl (n : Nat) : leN n n = true := by
  induction n with
  | zero => rfl
  | succ n' ih => exact ih


/-
### Esercizio: Antisimmetria di leN

**Difficoltà: 4/4 (sfida).**

Dimostra che `leN` è antisimmetrica.

Suggerimento: fai prima `intro n`, poi induci su `n`, così che `m` rimanga
quantificato nell'ipotesi induttiva. Poi dividi `m` con `cases`: i casi misti
(`zero` con `succ`, `succ` con `zero`) hanno un'ipotesi falsa.
Nel caso `succ`, `succ`, usa l'ipotesi induttiva.
-/

theorem leN_antisymm : ∀ n m, leN n m → leN m n → eqN n m := by
  intro n
  induction n with
  | zero =>
    intro m h1 h2
    cases m with
    | zero => rfl
    | succ _ => rfl
  | succ n' ih =>
    intro m h1 h2
    cases m with
    | zero => rfl
    | succ m' =>
      apply ih
      · exact h1
      · exact h2


/-
### Esercizio: Sottrarre un numero da se stesso

**Difficoltà: 1/4 (riscaldamento).**

Dimostra la seguente proprietà per induzione su `n`. Nel caso successore, la
definizione di `subN` riduce il goal all'ipotesi induttiva.

def subN : Nat → Nat → Nat
  | 0,     _     => 0
  | n + 1, 0     => n + 1
  | n + 1, m + 1 => subN n m

-/

theorem subN_self (n : Nat) : subN n n = 0 := by
  induction n with
  | zero => rfl
  | succ n' ih => exact ih


/-
### Esercizio: Caratterizzazione alternativa di even (n + 1)

**Difficoltà: 2/4 (induzione standard).**

Dimostra che `isEven (n + 1)` è la negazione booleana di `isEven n`.
Suggerimento: `simp` sa che `!` è involutiva.
-/

theorem isEven_succ (n: Nat) : isEven (n+1) = !(isEven n) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [ih]
    simp


/-
### Esercizio: I numeri raddoppiati sono pari

**Difficoltà: 2/4 (induzione standard).**

Suggerimento: per induzione su `n`.
-/

theorem isEven_doubleN (n: Nat) : isEven (doubleN n) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [doubleN]
    rw [addN_succ_right]
    rw [addN_succ_right]
    rw [isEven_succ]
    rw [ih]
    rfl


/-
### Esercizio: Double e addN

**Difficoltà: 2/4 (induzione standard con lemmi precedenti).**

Suggerimento: induci su `n`. Nel caso successore, riscrivi con l'ipotesi
induttiva, `addN_succ_right` e `addN_succ_left`.
-/

theorem doubleN_addN (n: Nat) : doubleN n = addN n n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [doubleN]
    rw [addN_succ_right]
    rw [addN_succ_left]
    rw [ih]
    rfl


/-
### Esercizio: Correttezza di dualBExp

**Difficoltà: 3/4 (induzione seguita da analisi per casi booleana).**

Dimostra che `dualBExp` nega il valore booleano di un'espressione.

Suggerimento: usa l'induzione strutturale su `t`. Nel caso `bifte` ti serviranno
le tre ipotesi induttive. È anche utile considerare i due possibili valori di
`evalBExp t0` con

    cases h : evalBExp t0 with ...

Dopo l'analisi per casi, entrambi i lati si calcolano alla stessa espressione
booleana, quindi `rfl` chiude ogni caso.
-/

theorem evalBExp_dual (t : BExp) :
    evalBExp (dualBExp t) = !(evalBExp t) := by
  induction t with
  | btrue => rfl
  | bfalse => rfl
  | bifte t0 t1 t2 ih0 ih1 ih2 =>
    rw [dualBExp]
    rw [evalBExp]
    rw [evalBExp]
    rw [ih0]
    cases h : evalBExp t0 with
    | true =>
      rw [h]
      rw [evalBExp]
      rw [ih1]
      rw [evalBExp]
      rw [h]
      rfl
    | false =>
      rw [h]
      rw [evalBExp]
      rw [ih2]
      rw [evalBExp]
      rw [h]
      rfl


/-
### Esercizio (lungo): Connettivi booleani

**Difficoltà: 4/4 complessiva (esercizio esteso).** I singoli compiti sotto
iniziano dolcemente e costruiscono verso una dimostrazione di preservazione
semantica.

In precedenza abbiamo definito `BExp`, un linguaggio con tre costrutti:

    btrue                  la costante true
    bfalse                 la costante false
    bifte c t e            "if c then t else e"

e la sua funzione di valutazione `evalBExp : BExp → Bool`.

Qui definiamo un secondo linguaggio, `BExpConn`, che usa i *connettivi* logici
invece del condizionale:

    btrue                  la costante true
    bnot t                 negazione
    band t0 t1             congiunzione
    bor t0 t1              disgiunzione

Entrambi i linguaggi sono tipi induttivi, quindi definiamo la loro valutazione
per ricorsione strutturale. Per `BExpConn` ogni equazione usa il corrispondente
operatore booleano di Lean: `!`, `&&`, `||`.
-/

inductive BExpConn where
  | btrue  : BExpConn
  | bnot   : BExpConn → BExpConn
  | band   : BExpConn → BExpConn → BExpConn
  | bor    : BExpConn → BExpConn → BExpConn
  deriving Repr


/-
__Esercizio (difficoltà 1/4):__ Definisci la funzione di valutazione per `BExpConn`.
-/
def evalBExpConn : BExpConn → Bool
  | .btrue    => true
  | .bnot t   => !(evalBExpConn t)
  | .band t0 t1 => evalBExpConn t0 && evalBExpConn t1
  | .bor t0 t1  => evalBExpConn t0 || evalBExpConn t1

example :
    let ex0 := .band (.bor (.bnot .btrue) .btrue) .btrue
    evalBExpConn ex0 = true := by rfl

example :
    let ex1 := .band (.bor (.bnot .btrue) .btrue) (.bnot .btrue)
    evalBExpConn ex1 = false := by rfl

/-
Ogni connettivo può essere espresso con un condizionale:

    not a     =  if a then false else true
    a and b   =  if a then b else false
    a or b    =  if a then true else b

__Esercizio (difficoltà 2/4):__ Definisci una funzione `bexpconn_to_bexp` che traduce
i termini `BExpConn` in termini `BExp`, seguendo l'intuizione sopra.
-/

def bexpconn_to_bexp : BExpConn → BExp
  | .btrue    => .btrue
  | .bnot t   => .bifte (bexpconn_to_bexp t) .bfalse .btrue
  | .band t0 t1 => .bifte (bexpconn_to_bexp t0) (bexpconn_to_bexp t1) .bfalse
  | .bor t0 t1  => .bifte (bexpconn_to_bexp t0) .btrue (bexpconn_to_bexp t1)


-- __Esercizio (difficoltà 1/4):__ Testa la traduzione sui due esempi sopra.

example :
    let ex0 := .band (.bor (.bnot .btrue) .btrue) .btrue
    evalBExpConn ex0 = evalBExp (bexpconn_to_bexp ex0) := by rfl

example :
    let ex1 := .band (.bor (.bnot .btrue) .btrue) (.bnot .btrue)
    evalBExpConn ex1 = evalBExp (bexpconn_to_bexp ex1) := by rfl

/-
__Esercizio (difficoltà 3/4):__ Dimostra che la traduzione preserva il significato:
valutare un termine in `BExpConn` dà lo stesso booleano che valutare
la sua traduzione in `BExp`.

Suggerimento: usa l'induzione strutturale. In ogni caso ricorsivo, riscrivi prima con
le ipotesi induttive. Poi dividi sul valore booleano della prima sottoespressione
tradotta. La sintassi `cases h : e` esegue la divisione e registra un'equazione
per `e`, permettendo al condizionale circostante di calcolare.

-/

theorem bexpconn_equiv_bexp (t : BExpConn) : evalBExpConn t = evalBExp (bexpconn_to_bexp t) := by
  induction t with
  | btrue => rfl
  | bnot t ih =>
    rw [evalBExpConn]
    rw [bexpconn_to_bexp]
    rw [evalBExp]
    rw [ih]
    cases h : evalBExp (bexpconn_to_bexp t) with
    | true => rfl
    | false => rfl
  | band t0 t1 ih0 ih1 =>
    rw [evalBExpConn]
    rw [bexpconn_to_bexp]
    rw [evalBExp]
    rw [ih0]
    cases h : evalBExp (bexpconn_to_bexp t0) with
    | true =>
      rw [h]
      rw [evalBExp]
      rw [ih1]
      rfl
    | false =>
      rw [h]
      rw [evalBExp]
      rfl
  | bor t0 t1 ih0 ih1 =>
    rw [evalBExpConn]
    rw [bexpconn_to_bexp]
    rw [evalBExp]
    rw [ih0]
    cases h : evalBExp (bexpconn_to_bexp t0) with
    | true =>
      rw [h]
      rw [evalBExp]
      rfl
    | false =>
      rw [h]
      rw [evalBExp]
      rw [ih1]
      rfl

end Exercises


section Binary_numbers

/-
## Numeri binari (esercizio esteso opzionale)

**Difficoltà: 4/4 complessiva.** I primi compiti di programmazione sono
abbordabili, ma la sequenza completa è lunga. Funziona bene come lavoro
di laboratorio opzionale o come sfida per studenti che finiscono gli esercizi
principali.

I numeri naturali possono essere scritti in binario. Definiamo un nuovo tipo
induttivo di numeri binari con tre costruttori:

    bz        il numero 0
    b0 n      aggiungi la cifra 0:  il numero 2 * n
    b1 n      aggiungi la cifra 1:  il numero 2 * n + 1

La cifra meno significativa è il costruttore *più esterno*. Ad esempio:

    0  =  bz
    1  =  b1 bz
    2  =  b0 (b1 bz)
    3  =  b1 (b1 bz)
    4  =  b0 (b0 (b1 bz))
    5  =  b1 (b0 (b1 bz))
    6  =  b0 (b1 (b1 bz))

Controlla uno di essi a mano: `b0 (b1 (b1 bz))` è due volte il numero `b1 (b1 bz)`,
che è `2 * 1 + 1 = 3`, quindi è 6.

Questo tipo di dato ammette anche rappresentazioni con zeri iniziali. Ad esempio,
sia `bz` che `b0 bz` denotano zero. Quindi `binToNat` non è iniettiva su ogni
`BinNat`. La funzione `natToBin` sotto produce rappresentazioni canoniche;
dimostreremo la direzione di conversione che rimane vera senza prima definire
un predicato separato per i numerali canonici.
-/

inductive BinNat where
  | bz : BinNat
  | b0 : BinNat → BinNat
  | b1 : BinNat → BinNat
  deriving Repr

/-
### Compito 1: Convertire binario in naturale

**Difficoltà: 1/4 (programmazione di riscaldamento).**

Scrivi una funzione `binToNat` che converte un `BinNat` in un `Nat`.
-/

def binToNat : BinNat → Nat
  | .bz => 0
  | .b0 n => 2 * binToNat n
  | .b1 n => 2 * binToNat n + 1

example : binToNat (.b0 (.b1 (.b1 .bz))) = 6 := by rfl


/-
### Compito 2: Incrementare un numero binario

**Difficoltà: 2/4 (programmazione ricorsiva con carry).**

Scrivi una funzione `binIncr` che aggiunge uno *direttamente sui numerali*, come
in un contatore binario:
* zero diventa `1`;
* un numerale che termina in `0` ha la sua ultima cifra cambiata in `1`;
* un numerale che termina in `1` diventa `0` e *riporta* al resto.
-/

def binIncr : BinNat → BinNat
  | .bz => .b1 .bz
  | .b0 n => .b1 n
  | .b1 n => .b0 (binIncr n)

example : binToNat (binIncr (.b0 (.b1 (.b1 .bz)))) = 7 := by rfl

/-
### Compito 3: Convertire naturale in binario

**Difficoltà: 2/4 (programmazione ricorsiva).**

Scrivi una funzione `natToBin` che converte un `Nat` in un `BinNat`
contando da zero.
-/

def natToBin : Nat → BinNat
  | 0 => .bz
  | n + 1 => binIncr (natToBin n)

example : natToBin 6 = (.b0 (.b1 (.b1 .bz))) := by rfl
example : natToBin 11 = (.b1 (.b1 (.b0 (.b1 .bz)))) := by rfl


/-
### Compito 4: Correttezza dell'incremento binario (1)

**Difficoltà: 1/4 (calcolo).**

Considera il seguente diagramma:

                  succ
        n:Nat ----------------> n':Nat
          |                       |
 natToBin |              natToBin |
          |                       |
          v       binIncr         v
        b:BinNat -------------> b':BinNat

Dimostra che il diagramma *commuta*, cioè i due percorsi verso b' sono equivalenti.
-/

theorem natToBin_succ (n : Nat) : natToBin (n + 1) = binIncr (natToBin n) := by
  rfl


/-
### Compito 5: Definire il raddoppio

**Difficoltà: 2/4 (analisi per casi in una definizione).**

Definisci `binDouble`, che raddoppia un numerale *direttamente sui numerali*,
senza convertire in `Nat`. Zero deve rimanere `bz` (non vogliamo una cifra zero iniziale):

    binDouble bz     = bz
    binDouble (b0 n) = b0 (b0 n)
    binDouble (b1 n) = b0 (b1 n)
-/

def binDouble : BinNat → BinNat
  | .bz => .bz
  | .b0 n => .b0 (.b0 n)
  | .b1 n => .b0 (.b1 n)

example : binDouble .bz = .bz := by rfl
example : binDouble (.b1 .bz) = .b0 (.b1 .bz) := by rfl
example : binToNat (binDouble (.b1 (.b1 .bz))) = 6 := by rfl


/-
### Compito 6: Correttezza del raddoppio

**Difficoltà: 1/4 (analisi per casi).**

Dimostra che `binDouble` raddoppia davvero il numero rappresentato.
Suggerimento: non serve induzione. Ci sono tre costruttori, quindi usa `cases`.
-/

theorem binToNat_binDouble (b : BinNat) :
    binToNat (binDouble b) = 2 * binToNat b := by
  cases b with
  | bz => rfl
  | b0 n =>
    rw [binDouble]
    rw [binToNat]
    rw [binToNat]
    omega
  | b1 n =>
    rw [binDouble]
    rw [binToNat]
    rw [binToNat]
    omega


/-
### Compito 7: Correttezza dell'incremento binario (2)

**Difficoltà: 3/4 (induzione più aritmetica lineare).**

Considera il seguente diagramma:

                    binIncr
        b:BinNat -------------> b':BinNat
          |                       |
 binToNat |              binToNat |
          |                       |
          v         succ          v
        n:Nat ----------------> n':Nat

Dimostra che il diagramma *commuta*, cioè i due percorsi verso n' sono equivalenti.

Suggerimento: usa la tattica `omega` su goal che coinvolgono aritmetica sui
numeri naturali. Questa tattica dimostra equazioni e disuguaglianze di aritmetica
lineare su `Nat`, usando le ipotesi nel contesto. Qui l'induzione gestisce la
struttura ricorsiva, mentre `omega` gestisce solo il riarrangiamento aritmetico
finale; non sostituisce l'induzione.
-/

theorem binToNat_binIncr (b : BinNat) :
    binToNat (binIncr b) = binToNat b + 1 := by
  induction b with
  | bz => rfl
  | b0 n ih =>
    rw [binIncr]
    rw [binToNat]
    rw [binToNat]
    omega
  | b1 n ih =>
    rw [binIncr]
    rw [binToNat]
    rw [binToNat]
    rw [ih]
    omega


/-
### Compito 8: Convertire un numero in binario e ritorno

**Difficoltà: 2/4 una volta che il Compito 7 è disponibile.**

Dimostra che convertire un numero in binario e ritorno dà lo stesso numero.

Suggerimento: induzione su `n`. Il caso successore necessita di `natToBin_succ`,
`binToNat_binIncr` dal Compito 7 e dell'ipotesi induttiva. Puoi usarli con
`rw [natToBin_succ, binToNat_binIncr, ih]`.
-/

theorem binToNat_natToBin (n : Nat) : binToNat (natToBin n) = n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [natToBin_succ]
    rw [binToNat_binIncr]
    rw [ih]

end Binary_numbers