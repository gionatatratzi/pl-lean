/-

# Numeri naturali, ricorsione e funzioni di ordine superiore

Questo file è sia una lezione che un programma Lean. Leggi i commenti
dall'alto verso il basso, ma posiziona anche il cursore su ogni comando e
ispeziona la Infoview di Lean. Sei incoraggiato a modificare espressioni,
introdurre errori e osservare le risposte di Lean.

Nella lezione precedente abbiamo imparato a:
* ispezionare e valutare espressioni Lean;
* definire costanti e funzioni pure;
* usare `Bool`, espressioni condizionali e pattern matching;
* usare funzioni come valori;
* enunciare proprietà semplici e dimostrarle con tattiche di base.

In questa lezione usiamo di nuovo tutte queste idee, ora sui *numeri naturali*.
I numeri naturali sono il nostro primo esempio di tipo induttivo con infiniti
valori. Sono il luogo più semplice per vedere come *dati*, *funzioni ricorsive*
e *dimostrazioni per induzione* si incastrano insieme.

Impareremo a:
* ispezionare il tipo induttivo `Nat` e i suoi due costruttori;
* definire funzioni su `Nat` per pattern matching;
* definire funzioni ricorsive e comprendere la ricorsione strutturale;
* scrivere funzioni aritmetiche: addizione, moltiplicazione, potenze, fattoriale,
  confronto e sottrazione;
* combinare espressioni `if` con funzioni a valori booleani;
* scrivere funzioni di ordine superiore: funzioni che prendono funzioni come
  argomenti, o che restituiscono funzioni come risultati;
* usare funzioni anonime e applicazione parziale;
* dimostrare proprietà semplici dei nostri programmi con `rfl`, `rw`, `simp`,
  `cases` e `induction`.

-/

set_option autoImplicit false


section Reading_this_file

/-
## Come leggere questo file

Come nella lezione precedente, i commenti spiegano le idee mentre le dichiarazioni
sotto di essi sono vero codice Lean.

Ricorda i tre comandi particolarmente utili durante l'apprendimento:

* `#check e` chiede a Lean il tipo di `e`;
* `#eval e` valuta `e` quando Lean può calcolarne il valore;
* `#print name` mostra una dichiarazione.

Useremo di nuovo tutti e tre qui sotto. Useremo anche `example`, che enuncia un
fatto e chiede a Lean di verificarlo, senza dare un nome al fatto.

### Come funzionano gli esercizi

Gli esercizi sono contrassegnati dalla parola `Exercise`. In molti di essi
sostituisci il segnaposto `sorry` con la tua soluzione. La parola `sorry`
significa "prometto di riempirlo più tardi": Lean lo accetta, ma mostra un avviso.

Molti esercizi di programmazione sono seguiti da alcuni *test*, scritti così:

    example : tripleN 4 = 12 := by rfl

Un test è silenzioso quando passa e mostra un errore quando fallisce. Quindi
quando apri questo file per la prima volta, i test degli esercizi sono rossi:
questo è previsto! Il tuo obiettivo è renderli silenziosi. Puoi sempre usare
`#eval` per sperimentare mentre lavori.

-/

/-
__Exercise__: prima di continuare, scrivi in un commento il tipo di `7`.
Cosa ti aspetti che `#check 7` riporti? Poi verifica la tua ipotesi.
-/

-- La tua risposta: `7` ha tipo `Nat` (Lean sceglie `Nat` come tipo predefinito
-- per i numerali quando non c'è altro contesto).

#check 7

/-
I numerali come `7` potrebbero in principio denotare molti tipi di numeri
(numeri naturali, interi, numeri in virgola mobile, ...). Quando nient'altro
dice il contrario, Lean sceglie `Nat`.

-/

end Reading_this_file


section Natural_numbers

/-
## Numeri naturali

I numeri naturali sono i numeri

    0, 1, 2, 3, ...

In Lean formano il tipo induttivo `Nat`.

Un *tipo induttivo* è definito elencando i suoi *costruttori*: gli unici modi di
costruire un valore di quel tipo. Concettualmente, i costruttori di `Nat` sono:

* `Nat.zero`, che costruisce zero;
* `Nat.succ n`, che costruisce il successore di un numero naturale `n`.

Come regole di inferenza, scriveremmo questi costruttori come:

                  n
--------      ----------
Nat.zero      Nat.succ n

Usando queste regole di inferenza, possiamo derivare che 3 è in Nat come segue:

--------
Nat.zero
------------------
Nat.succ Nat.zero
-----------------------------
Nat.succ (Nat.succ Nat.zero)
---------------------------------------
Nat.succ (Nat.succ (Nat.succ Nat.zero))

Quindi:

    0       = Nat.zero
    1       = Nat.succ Nat.zero
    2       = Nat.succ (Nat.succ Nat.zero)
    3       = Nat.succ (Nat.succ (Nat.succ Nat.zero))

I numerali come `0`, `1`, `2`, ... sono solo notazione per valori di numeri
naturali. L'idea importante non è la notazione in sé, ma la struttura induttiva:
partendo da zero, ogni numero naturale è ottenuto prendendo ripetutamente un
successore.

Questa struttura guiderà sia i nostri programmi che le nostre dimostrazioni.

-/

#check Nat            --- anche i tipi hanno tipi!
#check Nat.zero
#check Nat.succ
#check (0 : Nat)
#check (7 : Nat)

#eval (0 : Nat)
#eval (1 : Nat)
#eval (7 : Nat)

#print Nat

/-
Ad esempio, `Nat.succ 4` è il numero naturale 5.
-/

#eval Nat.succ 4

/-
Il costruttore `Nat.succ` è esso stesso una funzione in Nat → Nat. Il suo tipo
dice che, dato un numero naturale, ne produce un altro:
-/

#check Nat.succ

/-
Questo è il nostro primo importante esempio di tipo induttivo con un costruttore
che ha un argomento.

Confrontalo con `Bool` della lezione precedente:

    Bool  ha due costruttori, `true` e `false`.
    Nat   ha due costruttori, `zero` e `succ`.

La differenza è che `succ` porta con sé un altro numero naturale.
Questo rende `Nat` *infinito*: da ogni numero naturale possiamo costruirne un
altro prendendo il suo successore.

-/

/-
### Due modi di scrivere il successore

Scrivere `Nat.succ n` è preciso ma pesante. Lean ci permette anche di scrivere
`n + 1` per il successore di `n`. Le due espressioni sono lo stesso numero, e
Lean preferisce *stampare* `n + 1`: lo vedrai spesso nella Infoview.

I seguenti fatti valgono per puro calcolo, quindi `rfl` li dimostra.
-/

example : Nat.succ 4 = 5 := by rfl

example : 3 = Nat.succ (Nat.succ (Nat.succ Nat.zero)) := by rfl

example (n : Nat) : Nat.succ n = n + 1 := by rfl

/-
Nota però che `rfl` non è abbastanza potente per dimostrare che `n + 1 = 1 + n`:
-/
-- example (n : Nat) : Nat.succ n = 1 + n := by rfl  -- Questo fallisce!
-- Infatti `1 + n` non si riduce a `Nat.succ n` perché `+` ricorre sul secondo
-- argomento. Quindi NON si può chiudere con `rfl`.


/-
### Aritmetica integrata

Lean conosce già le solite operazioni sui numeri naturali.
-/

#eval 7 + 5
#eval 7 * 5
#eval 17 / 5       -- divisione intera
#eval 17 % 5       -- resto
#eval 2 ^ 10       -- potenza
#eval 2 ^ 100      -- nessun overflow: a differenza di `int` in C o Java, `Nat` è illimitato

/-
La sottrazione merita un avvertimento. Non ci sono numeri naturali negativi,
quindi la sottrazione si ferma a zero:
-/

#eval 7 - 5
#eval 5 - 7

/-
In questa lezione reimplementeremo deliberatamente addizione, moltiplicazione e
così via da zero (`addN`, `mulN`, ...). L'obiettivo è imparare come funzionano le
funzioni ricorsive sui dati induttivi, e poi dimostrare cose su di esse. Nei
programmi reali dovresti naturalmente usare le operazioni integrate, che sono
molto più veloci.

-/

end Natural_numbers


section Pattern_matching_on_Nat

/-
## Pattern matching sui numeri naturali

Abbiamo già usato il pattern matching con `Bool`. La stessa idea funziona con `Nat`.
Una funzione sui numeri naturali può descrivere separatamente cosa succede per zero
e per un successore.

Ad esempio, il predecessore di zero è definito qui come zero, mentre il
predecessore di un successore è il numero dentro il successore.

-/

def predN (n : Nat) : Nat :=
  match n with
  | Nat.zero   => Nat.zero
  | Nat.succ k => k

#eval predN 0
#eval predN 1
#eval predN 7

/-
Il pattern `Nat.succ k` fa due cose contemporaneamente:

1. controlla che l'argomento sia un successore;
2. dà un nome, `k`, al numero memorizzato dentro quel successore.

Questa è esattamente la stessa idea del pattern matching su un booleano, ma con la
differenza che ora il costruttore porta dati che possiamo usare nel lato destro.

Lean controlla anche che i pattern coprano *tutti* i costruttori.
__Exercise__: Prova a commentare il caso `Nat.zero` da `predN` e leggi il
messaggio di errore.

-/

--- Il predecessore del successore di n è sempre n
theorem pred_succ (n: Nat) : predN (Nat.succ n) = n := by rfl

--- La maggior parte delle volte, anche il successore del predecessore di n è n
example : Nat.succ (predN 3) = 3 := by rfl
example : Nat.succ (predN 7) = 7 := by rfl

/-
__Exercise__: ma è *sempre* vero? Se no, fornisci un controesempio
-/
example : let n := 0
  !(Nat.succ (predN n) = n) := by rfl


/-
Possiamo anche usare la sintassi compatta a equazioni introdotta nella lezione precedente.
-/

def isZero : Nat → Bool
  | 0          => true
  | Nat.succ _ => false

#eval isZero 0
#eval isZero 3

/-
L'underscore `_` è un wildcard. Nel caso successore non ci serve ricordare quale
numero naturale compare dentro il successore.

Nota che il pattern `0` è un numerale, che è permesso nei pattern.
I pattern possono anche usare la notazione `n + 1` invece di `Nat.succ n`. Quindi
`predN` può essere scritto in modo più breve:
-/

def predN₂ : Nat → Nat
  | 0     => 0
  | n + 1 => n

#eval predN₂ 7

/-
D'ora in poi useremo principalmente `n + 1` nei pattern, dato che questo è ciò
che Lean ci mostra nei goal.
Tuttavia, deve essere usato coscientemente: scrivere `1 + n` in un pattern
risulta in un errore!

I pattern possono anche essere *annidati*: il pattern `n + 2` significa
`Nat.succ (Nat.succ n)`, e corrisponde a ogni numero che è almeno due.
Possiamo usarlo per calcolare la parità di un numero. Un numero è pari quando è
zero; è dispari quando è uno; altrimenti rimuoviamo due successori e continuiamo.
-/

def isEven : Nat → Bool
  | 0     => true
  | 1     => false
  | n + 2 => isEven n

example : isEven 0    := by rfl
example : !(isEven 1) := by rfl
example : isEven 2    := by rfl
example : !(isEven 7) := by rfl
example : isEven 10   := by rfl

/-
Nota la chiamata ricorsiva `isEven n` nell'ultimo caso. L'argomento della
chiamata ricorsiva è più piccolo dell'argomento originale `n + 2`. Lean può
vederlo dal pattern: `n` è ottenuto dall'argomento originale rimuovendo due
costruttori.

Ad esempio:

    isEven 4  =  isEven 2  =  isEven 0  =  true

Questo ci porta a una delle idee centrali della programmazione funzionale:
i dati ricorsivi sono naturalmente processati da funzioni ricorsive.

-/

/-
__Exercise__ (`plusTwo`): definisci una funzione `plusTwo` che aggiunge 2 al suo argomento
Suggerimento: non ogni funzione necessita di pattern matching.
-/

def plusTwo (n : Nat) : Nat :=
  n + 2

example : plusTwo 0 = 2 := by rfl
example : plusTwo 1 = 3 := by rfl


/-
__Exercise__ (`minusTwo`): definisci una funzione `minusTwo` che sottrae due dal
suo argomento, fermandosi a zero.
-/

def minusTwo : Nat → Nat
  | 0     => 0
  | 1     => 0
  | n + 2 => n

example : minusTwo 0 = 0 := by rfl
example : minusTwo 1 = 0 := by rfl
example : minusTwo 7 = 5 := by rfl


/-
__Exercise__ (`isOdd`): definisci `isOdd`, che è `true` esattamente per i numeri
dispari. Puoi farlo per pattern matching, o riutilizzando `isEven` insieme alla
negazione booleana `!`.
-/

def isOdd (n : Nat) : Bool :=
  match n with
  | 0     => false
  | 1     => true
  | n + 2 => isOdd n

example : isOdd 0 = false := by rfl
example : isOdd 7 = true := by rfl
example : isOdd 10 = false := by rfl

theorem odd_iff_not_even (n: Nat) : isOdd n ↔ !(isEven n) := by
  induction n using isEven.induct with
  | case1 => rfl
  | case2 => rfl
  | case3 n ih => exact ih

end Pattern_matching_on_Nat


section Recursion

/-
## Funzioni ricorsive

In un linguaggio imperativo, un modo familiare di processare un numero naturale è un ciclo.
Ad esempio, possiamo aggiungere `m` a `n` contando `m` fino a zero:

    result := n
    while m > 0 do
        result := result + 1
        m := m - 1
    return result

Nella programmazione funzionale esprimiamo la stessa idea per ricorsione.
Una funzione esamina l'input, gestisce il caso base e fa una chiamata ricorsiva
su una parte più piccola dell'input. Non ci sono variabili da aggiornare: il
"contatore del ciclo" è semplicemente un argomento che diventa più piccolo in
ogni chiamata.

Ecco l'addizione, definita ricorsivamente sul secondo argomento.

Matematicamente:

    n + 0     = n
    n + (m+1) = (n + m) + 1

In Lean, questo diventa:
-/

def addN (n m : Nat) : Nat :=
  match m with
  | 0      => n
  | m' + 1 => Nat.succ (addN n m')

#check addN
#eval addN 2 3
#eval addN 10 0
#eval addN 0 7

/-
La chiamata ricorsiva è `addN n m'`. Il nuovo argomento `m'` è più piccolo
dell'argomento originale `m' + 1`.

Lean valuta `addN 2 3` srotolando la definizione ancora e ancora:

    addN 2 3
    = Nat.succ (addN 2 2)
    = Nat.succ (Nat.succ (addN 2 1))
    = Nat.succ (Nat.succ (Nat.succ (addN 2 0)))
    = Nat.succ (Nat.succ (Nat.succ 2))
    = 5

Leggere una tale traccia è un ottimo modo per capire una funzione ricorsiva.
Quando non sei sicuro di una definizione, prova a produrre una traccia a mano.

La definizione segue un pattern molto utile:

    match n with
    | caso base       => risultato per il caso base
    | caso ricorsivo  => risultato costruito da una chiamata ricorsiva più piccola

Questo si chiama *ricorsione strutturale*: le chiamate ricorsive sono fatte su
pezzi dell'input ottenuti rimuovendo costruttori. Lean accetta una definizione
ricorsiva solo se può controllare che la ricorsione termini. Non è solo una
questione tecnica. Lean è anche un assistente alla dimostrazione, e una funzione
che non termina mai ci permetterebbe di dimostrare affermazioni false. Ad esempio,
Lean rifiuta la seguente definizione, perché la chiamata ricorsiva è su un
numero *più grande* (provalo in un file scratch e leggi il messaggio di errore):

    def bad (n : Nat) : Nat :=
      bad (n + 1)

-/

/-
Possiamo scrivere la stessa definizione usando il pattern matching in stile equazionale.
-/

def addN₂ : Nat → Nat → Nat
  | n, 0      => n
  | n, m' + 1 => Nat.succ (addN₂ n m')

#eval addN₂ 4 5

/-
Le due funzioni calcolano la stessa operazione. Più avanti lo *dimostreremo*.

Per ora, prova a prevedere il risultato di ogni espressione prima di chiedere a
Lean di calcolarla.
-/

#eval addN 3 4
#eval addN (addN 1 2) 3

/-
Una funzione può naturalmente chiamare una funzione precedentemente definita. Non
abbiamo bisogno di ripetere l'implementazione dell'addizione ogni volta che
vogliamo sommare numeri. Questa è una delle ragioni principali per definire
piccole funzioni riutilizzabili.
-/

def doubleN (n : Nat) : Nat :=
  addN n n

#eval doubleN 0
#eval doubleN 5

/-
### Moltiplicazione

La moltiplicazione può essere definita come addizione ripetuta:

    n * 0     = 0
    n * (m+1) = (n * m) + n

-/

def mulN (n m : Nat) : Nat :=
  match m with
  | 0      => 0
  | m' + 1 => addN (mulN n m') n

#check mulN
#eval mulN 3 4
#eval mulN 7 0
#eval mulN 0 9

/-
Leggi il caso ricorsivo dall'interno verso l'esterno:

    mulN n m'

calcola `n * m'`. Poi aggiungiamo un'altra copia di `n`:

    addN (mulN n m') n

La struttura del programma rispecchia la definizione matematica.

-/

/-
### Esponenziazione

L'esponenziazione è moltiplicazione ripetuta, ricorsivamente sull'esponente:

    b ^ 0     = 1
    b ^ (e+1) = b * (b ^ e)

-/

def powN (b e : Nat) : Nat :=
  match e with
  | 0      => 1
  | e' + 1 => mulN b (powN b e')

#eval powN 2 5
#eval powN 3 0
#eval powN 0 3

/-
### Fattoriale

La funzione fattoriale è definita matematicamente da

    0!     = 1
    (n+1)! = (n+1) * n!

-/

def factorial : Nat → Nat
  | 0     => 1
  | n + 1 => mulN (n + 1) (factorial n)

#check factorial
#eval factorial 0
#eval factorial 1
#eval factorial 5
#eval factorial 6

/-
La chiamata ricorsiva `factorial n` è di nuovo su un numero naturale più piccolo.

Gli esempi sopra illustrano un principio generale:

* i dati induttivi suggeriscono definizioni ricorsive;
* le definizioni ricorsive riducono i dati induttivi fino a raggiungere un caso base.

-/

end Recursion


section Exercises_after_recursion

/-
## Esercizi

Prima di continuare, risolvi questi piccoli esercizi. Rafforzano il pattern
matching e la ricorsione.

-/

/-
__Exercise__ (`tripleN`): definisci una funzione `tripleN` che calcola tre volte
il suo argomento. Riutilizza `doubleN` e `addN` invece di scrivere una
definizione ricorsiva.
-/

def tripleN (n : Nat) : Nat :=
  addN (doubleN n) n

example : tripleN 0 = 0  := by rfl
example : tripleN 4 = 12 := by rfl

/-
__Exercise__ (`sumUpTo`): definisci `sumUpTo` ricorsivamente in modo che

    sumUpTo 0       = 0
    sumUpTo (n + 1) = (n + 1) + sumUpTo n

Ad esempio, `sumUpTo 4` è `4 + 3 + 2 + 1 + 0`.
Puoi usare il `+` integrato di Lean qui.
-/

def sumUpTo : Nat → Nat
  | 0     => 0
  | n + 1 => (n + 1) + sumUpTo n

example : sumUpTo 0 = 0   := by rfl
example : sumUpTo 4 = 10  := by rfl
example : sumUpTo 10 = 55 := by rfl

/-
__Exercise__ (`fibN`): definisci la funzione Fibonacci:

    fibN 0       = 0
    fibN 1       = 1
    fibN (n + 2) = fibN n + fibN (n + 1)

Osserva che questa definizione ha due casi base e *due* chiamate ricorsive.
Lean la accetta perché entrambe le chiamate sono su argomenti più piccoli.
-/

def fibN : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fibN n + fibN (n + 1)

example : fibN 0 = 0    := by rfl
example : fibN 1 = 1    := by rfl
example : fibN 7 = 13   := by rfl
example : fibN 10 = 55  := by rfl

end Exercises_after_recursion


section Comparing_numbers

/-
## Confrontare numeri

Le funzioni con diversi argomenti possono fare pattern matching su diversi
argomenti contemporaneamente. Ecco tre esempi classici:

* `eqN n m` testa se `n` e `m` sono uguali;
* `leN n m` testa se `n` è minore o uguale a `m`;
* `subN n m` calcola `n - m`, fermandosi a zero.

Ciascuna delle prime due restituisce un `Bool`, quindi potremo usarle come
condizioni di un `if`. Nei pattern sotto, `_ + 1` significa "qualsiasi
successore, il cui predecessore non ci serve nominare".
-/

def eqN : Nat → Nat → Bool
  | 0,     0     => true
  | 0,     _ + 1 => false
  | _ + 1, 0     => false
  | n + 1, m + 1 => eqN n m

def leN : Nat → Nat → Bool
  | 0,     _     => true
  | _ + 1, 0     => false
  | n + 1, m + 1 => leN n m

def subN : Nat → Nat → Nat
  | 0,     _     => 0
  | n + 1, 0     => n + 1
  | n + 1, m + 1 => subN n m

#eval eqN 3 3
#eval eqN 3 4
#eval leN 2 5
#eval leN 5 2
#eval leN 4 4
#eval subN 7 3
#eval subN 3 7

/-
In ogni caso l'ultima equazione rimuove un costruttore da *entrambi* gli argomenti.
Quindi la chiamata ricorsiva è su argomenti più piccoli.

Lean fornisce anche confronti integrati: `==` calcola un `Bool`, e `≤`, `<`
sono affermazioni che Lean può decidere, quindi possono essere usate direttamente
in un `if`:
-/

#eval 3 == 3
#eval if 3 ≤ 5 then "yes" else "no"

/-
__Exercise__ (`ltN`): definisci `ltN n m`, che testa se `n < m`.
Suggerimento: `n < m` vale esattamente quando `n + 1 ≤ m`. Riutilizza `leN`.
-/

def ltN (n m : Nat) : Bool :=
  leN (Nat.succ n) m

example : ltN 2 3 = true  := by rfl
example : ltN 3 3 = false := by rfl
example : ltN 4 3 = false := by rfl

end Comparing_numbers


section Conditionals_with_Nat

/-
## Espressioni condizionali con numeri naturali

L'espressione condizionale della lezione precedente è ancora utile.
Ricorda che `if` è un'espressione: calcola un valore.

Ora possiamo combinarla con una funzione a valori booleani sui numeri naturali.
Ad esempio, `isEven n` restituisce un `Bool`, quindi può essere usata come
condizione di un `if`.
-/

def nextIfEven (n : Nat) : Nat :=
  if isEven n then Nat.succ n else n

#eval nextIfEven 0
#eval nextIfEven 1
#eval nextIfEven 2
#eval nextIfEven 7

/-
Questo è un utile promemoria che pattern matching e `if` sono complementari:

* usa il pattern matching quando vuoi descrivere i diversi costruttori
  di un tipo di dato;
* usa `if` quando hai già una condizione booleana e vuoi scegliere
  tra due risultati.

Qui `leN` fornisce la condizione:
-/

def minN (n m : Nat) : Nat :=
  if leN n m then n else m

#eval minN 3 8
#eval minN 9 4

/-
I condizionali possono essere concatenati con `else if`. La seguente funzione
calcola una descrizione di un numero come `String`.
-/

def describe (n : Nat) : String :=
  if eqN n 0 then "zero"
  else if isEven n then "even"
  else "odd"

#eval describe 0
#eval describe 7
#eval describe 10

/-
Un altro esempio, che mescola le nostre funzioni con le operazioni integrate di Lean.
Il *passo di Collatz* dimezza un numero pari, e mappa un numero dispari `n` in
`3n + 1`. Ripetere questo passo è oggetto di un famoso problema aperto!
-/

def collatzStep (n : Nat) : Nat :=
  if isEven n then n / 2 else 3 * n + 1

#eval collatzStep 6
#eval collatzStep 7

/-
__Exercise__ (`zeroIfEven`): definisci `zeroIfEven` in modo che restituisca `0`
per input pari e restituisca il numero originale per input dispari.
-/

def zeroIfEven (n : Nat) : Nat :=
  if isEven n then 0 else n

example : zeroIfEven 4 = 0 := by rfl
example : zeroIfEven 5 = 5 := by rfl

/-
__Exercise__ (`maxN`): definisci `maxN n m`, il maggiore di due numeri, usando
`if` e `leN`.
-/

def maxN (n m : Nat) : Nat :=
  if leN n m then m else n

example : maxN 3 8 = 8 := by rfl
example : maxN 9 4 = 9 := by rfl
example : maxN 5 5 = 5 := by rfl

end Conditionals_with_Nat


section Higher_order_functions

/-
## Funzioni come valori: ora con i numeri naturali

Nella lezione precedente abbiamo visto che le funzioni sono valori e possono
essere passate come argomenti. Con i numeri naturali questa idea diventa molto
più interessante, perché possiamo usare funzioni di ordine superiore per
descrivere il calcolo ripetuto.

Una *funzione di ordine superiore* è una funzione che prende un'altra funzione
come argomento, restituisce una funzione, o entrambe le cose.

Primo, l'esempio più semplice: applicare una funzione due volte.
-/

def applyTwiceN (f : Nat → Nat) (n : Nat) : Nat :=
  f (f n)

#check applyTwiceN
#eval applyTwiceN Nat.succ 5
#eval applyTwiceN doubleN 3

/-
Il parametro `f` ha un tipo funzione:

    Nat → Nat

È usato proprio come qualsiasi altro valore. In `applyTwiceN f n`, l'espressione
`f n` calcola una applicazione, e `f (f n)` ne calcola due.

-/

/-
Possiamo passare anche una funzione anonima.
-/

#eval applyTwiceN (fun n : Nat => n + 1) 5
#eval applyTwiceN (fun n : Nat => n * 2) 3

/-
La funzione anonima

    fun n : Nat => n + 1

ha tipo `Nat → Nat`.

Come nella lezione precedente, il tipo del parametro può spesso essere inferito
in un contesto in cui Lean conosce già il tipo funzione atteso. Lean ha anche
una notazione più breve: un punto `·` segna l'argomento mancante, quindi `(· + 1)`
significa `fun x => x + 1`.
-/

#check (fun n : Nat => n + 1)
#eval applyTwiceN (fun n => n * 2) 3
#eval applyTwiceN (· + 10) 1

/-
### Ripetere una funzione

`applyTwiceN` ripete sempre esattamente due volte. Possiamo generalizzarlo usando
un numero naturale per dire quante volte la funzione deve essere applicata.
Questo è la controparte funzionale di un ciclo `for` che viene eseguito `k` volte:

    for i in 1 .. k do
        n := f n
    return n

Il caso base è importante:

    applicare una funzione zero volte lascia l'input invariato.

Per il caso successore, applichiamo la funzione `k'` volte e poi la applichiamo
ancora una volta.
-/

def iterateN (f : Nat → Nat) (k n : Nat) : Nat :=
  match k with
  | 0      => n
  | k' + 1 => f (iterateN f k' n)

#check iterateN
#eval iterateN Nat.succ 5 0
#eval iterateN Nat.succ 3 10
#eval iterateN (fun n : Nat => n * 2) 4 1

/-
Ci sono tre ruoli in `iterateN`:

* `f` è l'operazione che vogliamo ripetere;
* `k` dice quante volte ripeterla;
* `n` è il valore di partenza.

Ad esempio, ecco come Lean srotola una chiamata con `k = 3`:

    iterateN f 3 n
    = f (iterateN f 2 n)
    = f (f (iterateN f 1 n))
    = f (f (f (iterateN f 0 n)))
    = f (f (f n))

Questo è un tipico pattern di programmazione funzionale di ordine superiore: la
ricorsione è usata per controllare la ripetizione, mentre l'operazione effettiva
è fornita come dato.

(Si potrebbe anche definire `iterateN` chiamando se stessa su `f n`, invece di
applicare `f` alla fine. I risultati sono gli stessi, ma le dimostrazioni sulla
versione sopra risultano un po' più semplici.)

-/

/-
Possiamo recuperare `applyTwiceN` da `iterateN`:
-/

def applyTwiceN₂ (f : Nat → Nat) (n : Nat) : Nat :=
  iterateN f 2 n

#eval applyTwiceN₂ Nat.succ 5
#eval applyTwiceN₂ doubleN 3

/-
Dato che `iterateN` prende qualsiasi funzione di tipo `Nat → Nat`, possiamo usarlacon il passo di Collatz definito sopra. Partendo da 6, cinque passi danno

    6 -> 3 -> 10 -> 5 -> 16 -> 8
-/

#eval iterateN collatzStep 5 6

/-
### Applicazione parziale

Ricorda dalla lezione precedente che i tipi funzione associano a destra.
Quindi

    Nat → Nat → Nat

significa

    Nat → (Nat → Nat)

Una funzione può quindi ricevere i suoi argomenti uno alla volta.

Ad esempio, `addN 5` è essa stessa una funzione dai numeri naturali ai numeri
naturali: aggiunge 5 al suo argomento.
-/

#check addN 5
#eval (addN 5) 3
#eval (addN 10) 2

/-
Possiamo dare un nome a questa funzione parzialmente applicata.
-/

def addFive : Nat → Nat :=
  addN 5

#check addFive
#eval addFive 0
#eval addFive 7

/-
Questa è un'altra idea centrale della programmazione funzionale: le funzioni sono
valori ordinari, quindi possiamo memorizzare una funzione parzialmente applicata
in un nome e passarla a un'altra funzione.
-/

#eval iterateN addFive 3 0

/-
__Exercise__ (`addTen`): definisci `addTen` per applicazione parziale di `addN`.
Poi usala con `iterateN`: applicare `addTen` tre volte a 10 deve dare 40.
-/

def addTen : Nat → Nat :=
  addN 10

example : addTen 5 = 15 := by rfl
example : iterateN addTen 3 10 = 40 := by rfl

end Higher_order_functions


section Functions_returning_functions

/-
## Funzioni che restituiscono funzioni

Possiamo anche definire funzioni che *restituiscono* funzioni.

Ad esempio, `makeAdder a` restituisce una funzione che aggiunge `a` al suo argomento.
-/

def makeAdder (a : Nat) : Nat → Nat :=
  fun n => addN a n

#check makeAdder
#check makeAdder 7
#eval makeAdder 7 3

/-
Dato che `makeAdder 7` è una funzione, possiamo passarla direttamente a `iterateN`.
-/

#eval iterateN (makeAdder 2) 5 0

/-
Questo stile è utile quando un calcolo ha un parametro fisso e un parametro che
verrà fornito in seguito. (Naturalmente, `makeAdder a` si comporta esattamente
come l'applicazione parziale `addN a`.)

La stessa idea funziona con la moltiplicazione.
-/

def makeMultiplier (a : Nat) : Nat → Nat :=
  fun n => mulN a n

#eval makeMultiplier 3 4
#eval iterateN (makeMultiplier 2) 4 1

/-
L'ultima espressione parte da 1 e raddoppia quattro volte:

    1 -> 2 -> 4 -> 8 -> 16

Quindi le funzioni di ordine superiore ci permettono di descrivere un processo
senza codificare l'operazione nel processo stesso.

-/

/-
__Exercise__ (`makePower`): definisci `makePower e`, che restituisce la funzione
che eleva il suo argomento alla potenza `e`. Ad esempio, `makePower 2` è la
funzione di quadratura. Riutilizza `powN`.

Poi prevedi, e verifica con `#eval`, il valore di `iterateN (makePower 2) 3 2`.
-/

def makePower (e : Nat) : Nat → Nat :=
  fun n => powN n e

example : makePower 2 5 = 25 := by rfl
example : makePower 3 2 = 8  := by rfl
example : makePower 0 9 = 1  := by rfl

-- #eval iterateN (makePower 2) 3 2
-- Calcolo: 2 -> 4 -> 16 -> 256

/-
### Composizione

Un'altra operazione standard di ordine superiore è la composizione di funzioni.
Date

    f : Nat → Nat
    g : Nat → Nat

possiamo costruire una nuova funzione che prima applica `g` e poi `f`.
-/

def composeN (f g : Nat → Nat) : Nat → Nat :=
  fun n => f (g n)

#check composeN
#eval composeN Nat.succ doubleN 3
#eval composeN doubleN Nat.succ 3

/-
Il primo risultato è 7 e il secondo è 8: l'ordine conta. In generale:

    composeN f g n = f (g n)

quindi `g` è applicata per prima.

Lean ha un operatore di composizione integrato, scritto `∘` (tipo `\comp`):
-/

#eval ((fun n : Nat => n + 1) ∘ (fun n : Nat => n * 2)) 5

/-
__Exercise__ (composizione): scrivi un'espressione, senza definire una nuova
funzione con nome, che applichi `doubleN` e poi `Nat.succ` al numero 5. Valutala
con `#eval`; il risultato dovrebbe essere 11. Trova due modi diversi di scriverla.
-/

-- Primo modo: usando l'operatore di composizione
#eval (Nat.succ ∘ doubleN) 5

-- Secondo modo: usando composeN
#eval composeN Nat.succ doubleN 5

end Functions_returning_functions


section Higher_order_functions_over_ranges

/-
## Funzioni di ordine superiore che iterano sui numeri

I numeri naturali possono anche descrivere *quante volte* o *su quale intervallo*
avviene un calcolo. In un linguaggio imperativo scriveremmo un ciclo come

    total := 0
    for i in 0 .. n-1 do
        total := total + f i
    return total

La versione funzionale è una funzione ricorsiva che prende `f` come argomento.
-/

def sumBelow (f : Nat → Nat) (n : Nat) : Nat :=
  match n with
  | 0      => 0
  | n' + 1 => sumBelow f n' + f n'

/-
`sumBelow f n` calcola `f 0 + f 1 + ... + f (n-1)`. Scelte diverse di `f`
danno somme diverse:
-/

#eval sumBelow (fun i => i) 5          -- 0 + 1 + 2 + 3 + 4
#eval sumBelow (fun i => i * i) 4      -- 0 + 1 + 4 + 9
#eval sumBelow (fun _ => 1) 7          -- conta i termini

/-
La funzione successiva combina ricorsione, `if` e un *predicato*: una funzione
che restituisce un `Bool`. Conta quanti numeri sotto `n` soddisfano il predicato.
-/

def countBelow (p : Nat → Bool) (n : Nat) : Nat :=
  match n with
  | 0      => 0
  | n' + 1 => if p n' then countBelow p n' + 1 else countBelow p n'

#eval countBelow isEven 10                 -- 0, 2, 4, 6, 8
#eval countBelow (fun i => leN 3 i) 10     -- 3, 4, ..., 9

/-
Nota che abbiamo passato la nostra funzione `isEven` come argomento. Le funzioni
che definiamo sono valori ordinari, utilizzabili ovunque.

-/

/-
__Exercise__ (`anyBelow`): definisci `anyBelow p n`, che restituisce `true` se
*qualche* numero sotto `n` soddisfa il predicato `p`, e `false` altrimenti.
Usa `if` nel caso ricorsivo.
-/

def anyBelow (p : Nat → Bool) (n : Nat) : Bool :=
  match n with
  | 0      => false
  | n' + 1 => if p n' then true else anyBelow p n'

example : anyBelow (fun i => eqN i 3) 5 = true := by rfl
example : anyBelow (fun i => eqN i 7) 5 = false := by rfl
example : anyBelow isEven 0 = false := by rfl

/-
__Exercise__ (`sumOfSquares`): definisci `sumOfSquares n`, la somma dei quadrati
dei numeri sotto `n`, riutilizzando `sumBelow` con una funzione anonima.
-/

def sumOfSquares (n : Nat) : Nat :=
  sumBelow (fun i => i * i) n

example : sumOfSquares 0 = 0 := by rfl
example : sumOfSquares 4 = 14 := by rfl

end Higher_order_functions_over_ranges


section Arithmetic_by_iteration

/-
## Aritmetica come iterazione

Possiamo combinare le idee della lezione. Le operazioni aritmetiche sono
applicazioni ripetute di operazioni più semplici:

* aggiungere `m` significa prendere il successore `m` volte;
* moltiplicare per `m` significa aggiungere `n` ripetutamente, `m` volte,
  partendo da 0;
* elevare alla potenza `e` significa moltiplicare per `b` ripetutamente, `e` volte,
  partendo da 1.

Usando `iterateN`, ciascuna di queste è una definizione di una riga. L'operazione
che viene ripetuta è passata esplicitamente, spesso per applicazione parziale o
per funzione anonima.
-/

def addByIterate (n m : Nat) : Nat :=
  iterateN Nat.succ m n

def mulByIterate (n m : Nat) : Nat :=
  iterateN (fun x => addN x n) m 0

def powByIterate (b e : Nat) : Nat :=
  iterateN (mulN b) e 1

#eval addByIterate 3 4
#eval mulByIterate 3 4
#eval powByIterate 2 5
#eval powByIterate 3 4

/-
Questo è un esempio di due implementazioni diverse che esprimono la stessa idea:

* `powN` segue la solita definizione matematica ricorsiva dell'esponenziazione;
* `powByIterate` separa il controllo della ripetizione (`iterateN`) dall'operazione
  che viene ripetuta (`mulN b`).

La seconda definizione è particolarmente interessante dal punto di vista della
programmazione funzionale perché l'operazione è passata esplicitamente come
funzione. Dimostreremo sotto che, per `addN` e `powN`, i due stili concordano.

-/

end Arithmetic_by_iteration


section Proofs_by_simplification

/-
La maggior parte delle dimostrazioni che abbiamo visto finora calcola solo
funzioni su valori concreti e controlla l'uguaglianza:
-/

example : addN 1 1 = 2 := by rfl

/-
Qui la tattica `rfl` funziona perché entrambi i lati si riducono per calcolo
allo stesso numero.
-/

/-
La definizione di `addN` ricorre sul suo *secondo* argomento. Quindi le seguenti
due equazioni possono essere lette direttamente dalla definizione, e `rfl` le
dimostra anche se `n` e `m` sono numeri naturali arbitrari.
-/

theorem addN_zero (n : Nat) : addN n 0 = n := by
  rfl

theorem addN_succ (n m : Nat) : addN n (m + 1) = (addN n m) + 1 := by
  rfl

/-
Similmente per la moltiplicazione:
-/

theorem mulN_succ (n m : Nat) : mulN n (m + 1) = addN (mulN n m) n := by
  rfl

/-
__Exercise__: dimostra il teorema corrispondente per `mulN` e zero a destra.
-/

theorem mulN_zero (n : Nat) : mulN n 0 = 0 := by
  rfl

end Proofs_by_simplification


section Proofs_by_rewriting

/-
### Riscrittura

I teoremi non sono solo da dimostrare: possono essere *usati*. La tattica `rw [h]`,
dove `h` è un'equazione `a = b`, sostituisce `a` con `b` nel goal. Se il goal
diventa della forma `x = x`, `rw` lo chiude automaticamente.
-/

theorem succ_addN_zero : ∀ n : Nat, Nat.succ (addN n 0) = Nat.succ n := by
  intros n
  rw [addN_zero]    --- addN n 0 = n

/-
__Exercise__: dimostra in modo simile che `isZero n = eqN n 0`.
-/

theorem isZero_eq_eqN (n : Nat) : isZero n = eqN n 0 := by
  cases n with
  | zero   => rfl
  | succ _ => rfl

end Proofs_by_rewriting


section Induction

/-
## Induzione: la controparte dimostrativa della ricorsione

L'analisi per casi non basta per `addN 0 n = n`: nel caso successore otteniamo
il goal per `k + 1`, ma per risolverlo dobbiamo conoscere il risultato per `k`.
Questo è esattamente ciò che fornisce l'*induzione matematica*.

Supponiamo di voler dimostrare una proprietà `P n` per ogni numero naturale `n`.
Il principio di induzione dice che è sufficiente dimostrare:

1. `P 0`                       -- il caso base;
2. `P n -> P (n + 1)`          -- il caso successore.

La seconda parte dice che se la proprietà è vera per un `n` arbitrario, allora
è vera per il suo successore.

In Lean, la tattica `induction` espone esattamente questi casi. Nel caso successore,
otteniamo anche l'*ipotesi induttiva* `ih`: l'enunciato per il numero più piccolo.

-/

theorem zero_addN (n : Nat) : addN 0 n = n := by
  induction n with
  | zero => rfl
  | succ n' ih => rw [addN_succ, ih]

/-
Seguiamo la dimostrazione. Dopo `induction n with`, Lean mostra due goal:

    case zero:   addN 0 0 = 0
    case succ:   ih : addN 0 n' = n'
                 ⊢ addN 0 (n' + 1) = n' + 1

* Il primo goal segue per calcolo, quindi `rfl` funziona.
* Nel secondo goal, `rw [addN_succ]` riscrive `addN 0 (n' + 1)` in
  `addN 0 n' + 1`. Poi `rw [ih]` sostituisce `addN 0 n'` con `n'`, e il goal
  diventa `n' + 1 = n' + 1`, che `rw` chiude da solo.

Questa è una corrispondenza molto importante:

    PROGRAMMAZIONE               DIMOSTRAZIONE
    ------------------------------------------------
    match n with ...             cases n with ...
    chiamata ricorsiva su n'     ipotesi induttiva su n'
    caso base                    caso base
    caso ricorsivo               caso successore

La dimostrazione ha la stessa forma della funzione ricorsiva di cui parla.

-/

/-
Un altro esempio, con il successore a *sinistra* di un'addizione. Induciamo
su `m`, dato che `addN` è ricorsiva sul suo secondo argomento.
-/

theorem addN_succ_left (n m : Nat) : addN (n + 1) m = addN n m + 1 := by
  induction m with
  | zero => rfl
  | succ m' ih => rw [addN_succ, addN_succ, ih]

/-
Il primo `rw [addN_succ]` srotola una delle due addizioni, il secondo srotola
l'altra, e `ih` finisce il lavoro.

Le dimostrazioni tattiche di questa forma sono spesso scritte in modo più breve
usando `simp`, che riscrive ripetutamente usando le definizioni e i lemmi che gli
diamo. Ad esempio, il caso successore sopra potrebbe essere scritto

    | succ m' ih => simp [addN, ih]

Useremo entrambi gli stili. La versione esplicita con `rw` è migliore per capire
la dimostrazione, `simp` è più veloce da scrivere.

-/

/-
Possiamo ora dimostrare la commutatività della nostra funzione di addizione.
Questa è una dimostrazione leggermente più grande, e mostra come i lemmi
precedenti vengono riutilizzati.
-/

theorem addN_comm (n m : Nat) : addN n m = addN m n := by
  induction m with
  | zero => rw [addN_zero, zero_addN]
  | succ m' ih => rw [addN_succ, addN_succ_left, ih]

/-
La dimostrazione sopra è una tappa importante. Siamo passati da un breve
programma ricorsivo a una proprietà matematica sul programma, e Lean ha
verificato la dimostrazione meccanicamente.

Non abbiamo bisogno di conoscere ogni tattica di Lean per fare questo. Un piccolo
kit di strumenti è già sufficiente per molte dimostrazioni elementari:

* `rfl`       -- chiude un'uguaglianza che segue per calcolo;
* `rw [h]`    -- riscrive il goal usando l'equazione `h`;
* `simp`      -- semplifica ripetutamente usando definizioni e lemmi noti;
* `cases`     -- divide un valore induttivo nei suoi costruttori;
* `induction` -- ragiona ricorsivamente su un valore induttivo.

-/

/-
__Exercise__ (`zero_mulN`): dimostra che `mulN 0 n = 0`.

Suggerimento: induzione su `n`. Il caso successore necessita di `mulN_succ`,
`addN_zero` e dell'ipotesi induttiva `ih`. Puoi usarli con `rw [...]` o dentro
`simp [...]`.
-/

theorem zero_mulN (n : Nat) : mulN 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n' ih => rw [mulN_succ, ih, addN_zero]

end Induction


section Proofs_about_higher_order_functions

/-
## Dimostrare fatti sulle funzioni di ordine superiore

Le funzioni di ordine superiore sono funzioni ordinarie, quindi possiamo
ragionare su di esse allo stesso modo.

Primo, `applyTwiceN` è semplicemente `iterateN` con due ripetizioni. Entrambi
i lati si calcolano a `f (f n)`, quindi `rfl` è sufficiente:
-/

theorem applyTwiceN_eq_iterateN (f : Nat → Nat) (n : Nat) :
    applyTwiceN f n = iterateN f 2 n := by
  rfl

/-
Secondo, dimostriamo ciò che avevamo affermato nella sezione sull'aritmetica per
iterazione: aggiungere `m` è davvero prendere il successore `m` volte.
L'enunciato riguarda un numero arbitrario `m`, quindi usiamo l'induzione.
-/

theorem iterate_succ (n m : Nat) : iterateN Nat.succ m n = addN n m := by
  induction m with
  | zero => rfl
  | succ m' ih => simp [iterateN, addN, ih]

/-
Qui `simp` srotola entrambi i lati del caso successore, riscrive con `ih`, e
i due lati diventano identici.

La stessa struttura di dimostrazione funziona per le potenze. Moltiplicare
ripetutamente per `b`, partendo da 1, è l'esponenziazione: le due implementazioni
`powByIterate` e `powN` concordano.
-/

theorem iterate_mulN (b e : Nat) : iterateN (mulN b) e 1 = powN b e := by
  induction e with
  | zero => rfl
  | succ e' ih => simp [iterateN, powN, ih]

/-
Nota come questi teoremi collegano ciò che abbiamo imparato: la ricorsione
definisce `iterateN`, gli argomenti di ordine superiore descrivono l'operazione
ripetuta, e l'induzione dimostra che il risultato coincide con la definizione
diretta.

-/

end Proofs_about_higher_order_functions


section Exercises

/-
## Esercizi

I seguenti esercizi raccolgono le idee principali della lezione.
Prova a risolverli senza prima guardare le definizioni precedenti.

Come prima, gli esercizi di programmazione vengono con test (o righe `#eval`
il cui risultato atteso è dato in un commento). Per le dimostrazioni, Lean
accetta l'esercizio quando `sorry` è stato sostituito da una dimostrazione completa.

-/

/-
### Esercizio 1: addizione ripetuta come funzione di ordine superiore

Definisci `repeatAdd k a`, una *funzione* che aggiunge `a` al suo argomento,
`k` volte. Il suo tipo dovrebbe avere la forma

    Nat → Nat → Nat → Nat

Usa `iterateN` e l'applicazione parziale (o una funzione anonima).
-/

def repeatAdd (k a : Nat) : Nat → Nat :=
  iterateN (fun x => addN x a) k

example : repeatAdd 3 5 10 = 25 := by rfl
example : repeatAdd 0 5 10 = 10 := by rfl

/-
### Esercizio 2: potenze di due

Definisci `powerOfTwo k`, che calcola `2 ^ k` iterando `doubleN` partendo
da 1. Non usare `powN`.
-/

def powerOfTwo (k : Nat) : Nat :=
  iterateN doubleN k 1

example : powerOfTwo 0 = 1  := by rfl
example : powerOfTwo 6 = 64 := by rfl

/-
### Esercizio 3: numeri primi

Un numero è primo quando ha esattamente due divisori: 1 e se stesso.

(a) Definisci `countDivisors n`, il numero di divisori di `n` tra 1 e `n`.

    Suggerimento: riutilizza `countBelow`. Il test `d` divide `n` è `n % d == 0`.
    Dato che `countBelow p n` guarda i numeri `0, ..., n-1`, il divisore da
    testare è `d + 1`.

(b) Definisci `isPrimeN n`, che è `true` esattamente quando `countDivisors n` è 2.
-/

def countDivisors (n : Nat) : Nat :=
  countBelow (fun d => n % (d + 1) == 0) n

def isPrimeN (n : Nat) : Bool :=
  countDivisors n == 2

-- #eval countDivisors 6      -- atteso: 4  (1, 2, 3, 6)
-- #eval countDivisors 7      -- atteso: 2
-- #eval countDivisors 12     -- atteso: 6
-- #eval isPrimeN 0           -- atteso: false
-- #eval isPrimeN 1           -- atteso: false
-- #eval isPrimeN 7           -- atteso: true
-- #eval isPrimeN 9           -- atteso: false
-- #eval isPrimeN 13          -- atteso: true

/-
### Esercizio 4: confronta due implementazioni

Abbiamo due definizioni di addizione, `addN` e `addN₂`. Dimostra che calcolano
la stessa funzione.

Suggerimento: l'induzione sul secondo argomento è una scelta naturale. Confronta
le due definizioni: il caso successore dovrebbe essere risolto da
`simp [addN, addN₂, ih]`, o da un `rw` esplicito.
-/

theorem addN_eq_addN₂ (n m : Nat) : addN n m = addN₂ n m := by
  induction m with
  | zero => rfl
  | succ m' ih => simp [addN, addN₂, ih]

/-
### Esercizio 5: iterare l'identità

Dimostra che applicare la funzione identità un numero qualsiasi di volte non
cambia il suo argomento. Suggerimento: induzione sul numero di iterazioni `k`.
-/

def identityN (n : Nat) : Nat :=
  n

theorem iterate_identity (k n : Nat) : iterateN identityN k n = n := by
  induction k with
  | zero => rfl
  | succ k' ih => simp [iterateN, identityN, ih]

/-
### Esercizio 6: la composizione è associativa

Dimostra che comporre tre funzioni non dipende da come mettiamo le parentesi.
Entrambi i lati sono funzioni, e hanno la stessa definizione dopo aver srotolato
`composeN`. Non serve induzione.
-/

theorem composeN_assoc (f g h : Nat → Nat) :
    composeN (composeN f g) h = composeN f (composeN g h) := by
  rfl

/-
### Esercizio 7 (sfida): associatività dell'addizione

Dimostra che `addN` è associativa.

Suggerimento: induzione su `k`. Nel caso successore, srotola le addizioni con
`addN_succ`, e finisci con l'ipotesi induttiva.
-/

theorem addN_assoc (n m k : Nat) :
    addN (addN n m) k = addN n (addN m k) := by
  induction k with
  | zero => rfl
  | succ k' ih => rw [addN_succ, addN_succ, addN_succ, ih]

/-
### Esercizio 8: progetta la tua funzione

Scegli una funzione utile sui numeri naturali che può essere definita
ricorsivamente. Esempi includono una funzione che conta quante volte un numero
pari può essere dimezzato, una funzione che calcola la somma dei primi `n` numeri
dispari, o una funzione di ordine superiore di tua invenzione.

Scrivi:

1. il suo tipo;
2. la sua definizione ricorsiva;
3. tre esempi `#eval`;
4. un teorema semplice su di essa, con una dimostrazione.

Mantieni la funzione abbastanza piccola da poter capire ogni chiamata ricorsiva.

-/

-- Esempio: contare quante volte un numero pari può essere dimezzato
def countHalvings : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => if isEven (n + 2) then 1 + countHalvings ((n + 2) / 2) else 0

-- Esempi:
#eval countHalvings 8   -- 8 -> 4 -> 2 -> 1: 3
#eval countHalvings 16  -- 16 -> 8 -> 4 -> 2 -> 1: 4
#eval countHalvings 6   -- 6 -> 3: 1

-- Teorema: countHalvings 0 = 0
theorem countHalvings_zero : countHalvings 0 = 0 := by rfl

end Exercises
