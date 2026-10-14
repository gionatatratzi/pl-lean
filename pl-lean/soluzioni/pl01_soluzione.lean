/-

# Numeri naturali e programmazione ricorsiva

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
* definire funzioni ricorsive;
* scrivere funzioni aritmetiche: addizione, moltiplicazione, potenze, fattoriale,
  confronto e sottrazione;
* dimostrare proprietà semplici dei nostri programmi, esplorando nuove tattiche.

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

end Reading_this_file


namespace MyNat

/-
## Numeri naturali

I numeri naturali sono i numeri

    0, 1, 2, 3, ...

In Lean formano il *tipo induttivo* `Nat`.
Qui ridefiniamo `Nat` in un nuovo namespace, per
evitare conflitti con il tipo nativo `Nat` di Lean.
-/

inductive Nat where
  | zero : Nat          --- assioma: zero è un Nat
  | succ : Nat -> Nat   --- regola di inferenza: se n è un Nat, allora succ n è un Nat

#eval Nat.zero
#eval Nat.succ Nat.zero
#eval Nat.succ (Nat.succ Nat.zero)

/-
Un tipo induttivo è definito elencando i suoi *costruttori*: gli unici modi di
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

end MyNat


/-
Ora torniamo al tipo nativo `Nat` di Lean. Quindi, d'ora in poi possiamo usare
la pretty-printing e tutti gli operatori standard su `Nat` definiti nella
libreria Lean.
-/

section Natural_numbers

#check Nat            --- anche i tipi hanno tipi!
#check Nat.zero
#check Nat.succ

#check (7 : Nat)      --- Lean converte implicitamente 7 in un Nat
#eval (7 : Nat)

#print Nat            --- il Nat integrato ha la stessa struttura di MyNat.Nat

/-
Ad esempio, `Nat.succ 4` è il numero naturale 5.
-/

#eval Nat.succ 4

/-
Il costruttore `Nat.succ` è esso stesso una funzione in Nat → Nat.
Il suo tipo dice che, dato un numero naturale, ne produce un altro:
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
### Un po' di zucchero sintattico

Scrivere `Nat.succ n` è preciso ma pesante. Lean ci permette anche di scrivere
`n + 1` per il successore di `n`. Le due espressioni denotano esattamente lo
stesso numero, e Lean preferisce *stampare* `n + 1`: lo vedrai nella Infoview.

I seguenti fatti valgono per puro calcolo, quindi `rfl` li dimostra.
-/

example : 3 = Nat.succ (Nat.succ (Nat.succ Nat.zero)) := by rfl

example (n : Nat) : Nat.succ n = n + 1 := by rfl

/-
__Exercise__: Nota che `rfl` non è abbastanza potente per dimostrare equivalenze
apparentemente ovvie, come ad esempio `n + 1 = 1 + n`. Sostituisci `sorry` con
`rfl` e controlla se il goal viene risolto.
-/
-- esempio (n : Nat) : Nat.succ n = 1 + n := by rfl  -- Questo fallisce!
-- In realtà `1 + n` non si riduce a `Nat.succ n` perché `+` ricorre sul primo argomento? No,
-- `Nat.add` ricorre sul secondo argomento. Quindi `1 + n` non è definizionalmente uguale a `Nat.succ n`.
-- Pertanto `rfl` fallisce. La soluzione corretta è che NON si può chiudere con `rfl`.


/-
### Operatori aritmetici integrati

Lean conosce già le solite operazioni sui numeri naturali.
-/

#eval 7 + 5
#eval 6 * 7
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

Definiamo la funzione predecessore per pattern matching:
* il predecessore di zero è zero,
* il predecessore di un successore è il numero dentro il successore.

-/

def predN (n : Nat) : Nat :=
  match n with
  | Nat.zero   => Nat.zero
  | Nat.succ k => k

/-
Il pattern `Nat.succ k` fa due cose contemporaneamente:

1. controlla che l'argomento sia un successore;
2. dà un nome, `k`, al numero memorizzato dentro quel successore.

Lean controlla anche che i pattern coprano *tutti* i costruttori.
__Exercise__: Prova a commentare il caso `Nat.zero` da `predN` e leggi il
messaggio di errore.
-/

--- Possiamo usare `rfl` per dimostrare fatti semplici per calcolo.
example : predN 0 = 0 := by rfl
example : predN 1 = 0 := by rfl
example : predN 7 = 6 := by rfl

--- Con `rfl` possiamo anche dimostrare fatti più generali: ad esempio, che
--- il predecessore del successore di n è sempre n
theorem pred_succ (n: Nat) : predN (Nat.succ n) = n := by rfl

--- La maggior parte delle volte, anche il successore del predecessore di `n` è `n`
example : Nat.succ (predN 3) = 3 := by rfl
example : Nat.succ (predN 7) = 7 := by rfl

/-
__Exercise__: ma è *sempre* vero? Se no, fornisci un controesempio
-/
example : let n := 0                  --- sostituisci questo sorry con un numero naturale
  !(Nat.succ (predN n) == n) := by rfl   --- una volta fatto, sostituisci questo sorry con rfl

/-
Possiamo definire il predecessore un po' più succintamente, usando:
* il numerale `0` invece di `Nat.zero` nel primo pattern;
* lo zucchero sintattico `n + 1` invece di `Nat.succ n` nel secondo pattern;
* la sintassi compatta a equazioni, che non richiede la parola chiave `match`.
Queste semplificazioni portano alla seguente definizione:
-/

def predN₂ : Nat → Nat
  | 0     => 0
  | n + 1 => n

#eval predN₂ 7


/-
Sfruttiamo tutte le scorciatoie usate in `predN₂`, e il wildcard `_` introdotto
nella lezione precedente, per definire una funzione `isZero` che dice se il suo
argomento è zero.
-/

def isZero : Nat → Bool
| 0 => true
| _ => false

example : isZero 0 = true  := by rfl
example : isZero 3 = false := by rfl


/-
D'ora in poi useremo principalmente `n + 1` nei pattern, dato che questo è ciò
che Lean ci mostra nei goal.
Tuttavia, deve essere usato coscientemente: scrivere `1 + n` in un pattern
risulta in un errore!

I pattern possono anche essere *annidati*: il pattern `n + 2` significa
`Nat.succ (Nat.succ n)`, e corrisponde a ogni numero che è almeno due.

-/

end Pattern_matching_on_Nat


section Recursion

/-
## Test di parità

Nei linguaggi imperativi, un modo familiare di processare un numero naturale è un ciclo.

Ad esempio, supponiamo di voler calcolare se un numero è pari, ma il nostro
linguaggio non ha un operatore modulo. In un linguaggio imperativo, potremmo
risolvere il problema come segue:

    while n >= 2 do
        n := n - 2
    if n = 0 then   // n = 0 -> il numero è pari
      return true
    else            // n = 1 -> il numero è dispari
      return false

Nella programmazione funzionale esprimiamo la stessa idea per *ricorsione*.
Una funzione esamina l'input, gestisce il caso base e fa una chiamata ricorsiva
su una parte più piccola dell'input. Non ci sono variabili da aggiornare.

Ad esempio, la funzione `isEven` calcola la parità di un numero.

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
chiamata ricorsiva è *più piccolo* dell'argomento originale `n + 2`. Lean può
vederlo dal pattern: `n` è ottenuto dall'argomento originale rimuovendo due
costruttori.

Ad esempio:

    isEven 4  =  isEven 2  =  isEven 0  =  true

Questa osservazione è fondamentale per garantire la terminazione dei calcoli.

-/


/-
## Addizione ricorsiva

In un linguaggio imperativo, possiamo aggiungere `m` a `n` contando `m` fino a zero:

    result := n
    while m > 0 do
        result := result + 1
        m := m - 1
    return result

Per definire l'addizione ricorsivamente, dobbiamo prima scegliere quale dei due
argomenti vogliamo diminuire fino al caso base. Scegliamo il secondo argomento `m`.
Allora abbiamo le equazioni:

    n + 0     = n
    n + (m+1) = (n + m) + 1

In Lean, queste equazioni possono essere trasformate direttamente in una
funzione ricorsiva:
-/

def addN (n m : Nat) : Nat :=
  match m with
  | 0      => n
  | m' + 1 => Nat.succ (addN n m')

#check addN

example : addN 2 3 = 5          := by rfl
example : addN (addN 1 2) 3 = 6 := by rfl

/-
La chiamata ricorsiva è `addN n m'`. Il nuovo argomento `m'` è più piccolo
dell'argomento originale `m' + 1`, quindi qualsiasi valutazione di `addN`
termina eventualmente.

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
__Exercise__: Ridefinisci `addN` usando zucchero sintattico e pattern matching
in stile equazionale.
-/

def addN₂ : Nat → Nat → Nat
  | n, 0     => n
  | n, m + 1 => Nat.succ (addN₂ n m)

example : addN₂ 4 5 = 9 := by rfl


/-

Come previsto, una funzione può chiamare una funzione precedentemente definita.
Non abbiamo bisogno di ripetere l'implementazione dell'addizione ogni volta che
vogliamo sommare numeri. Questa è una delle ragioni principali per definire
piccole funzioni riutilizzabili.

__Exercise__: Definisci una funzione ricorsiva `doubleN` che raddoppia il suo
argomento doubleN n = n+n
-/

def doubleN (n : Nat) : Nat := addN n n

example : doubleN 0 = 0   := by rfl
example : doubleN 5 = 10  := by rfl


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

example : mulN 3 4 = 12 := by rfl
example : mulN 7 0 = 0  := by rfl
example : mulN 0 9 = 0  := by rfl

/-
Leggi il caso ricorsivo dall'interno verso l'esterno:

    mulN n m'

calcola `n * m'`. Poi aggiungiamo un'altra copia di `n`:

    addN (mulN n m') n

La struttura del programma rispecchia la definizione matematica.

-/

end Recursion


section Exercises_on_recursion

/-
### Esercizio: Test se un numero è dispari

Definisci `isOdd`, che è `true` esattamente per i numeri dispari.
Puoi farlo per pattern matching, o riutilizzando `isEven` insieme alla negazione
booleana `!`.
-/

def isOdd (n : Nat) : Bool := !(isEven n)

example : isOdd 0 = false   := by rfl
example : isOdd 7 = true    := by rfl
example : isOdd 10 = false  := by rfl


/-
### Esercizio: Esponenziazione

L'esponenziazione è moltiplicazione ripetuta, ricorsivamente sull'esponente:

    b ^ 0     = 1
    b ^ (e+1) = b * (b ^ e)

-/

def powN (b e : Nat) : Nat :=
  match e with
  | 0     => 1
  | e' + 1 => mulN b (powN b e')

example : powN 2 5 = 32 := by rfl
example : powN 3 0 = 1  := by rfl
example : powN 0 3 = 0  := by rfl


/-
### Esercizio: Fattoriale

La funzione fattoriale è definita matematicamente da

    0!     = 1
    (n+1)! = (n+1) * n!

-/

def fact : Nat → Nat
  | 0     => 1
  | n + 1 => mulN (n + 1) (fact n)

example : fact 0 = 1   := by rfl
example : fact 1 = 1   := by rfl
example : fact 5 = 120 := by rfl

set_option maxRecDepth 2000 in --- per evitare `maximum recursion depth has been reached`
example : fact 6 = 720 := by rfl


/-
### Esercizio: Triplo

Definisci una funzione `tripleN` che calcola tre volte il suo argomento.
Riutilizza `doubleN` e `addN` invece di scrivere una definizione ricorsiva.
-/

def tripleN (n : Nat) : Nat := addN (doubleN n) n

example : tripleN 0 = 0  := by rfl
example : tripleN 4 = 12 := by rfl


/-
### Esercizio: Somma fino a

Definisci una funzione ricorsiva `sumUpTo` tale che
`sumUpTo n = 0 + 1 + 2 + ... + n`

    sumUpTo 0       = 0
    sumUpTo (n + 1) = (n + 1) + sumUpTo n

Puoi usare il `+` integrato di Lean qui.
-/

def sumUpTo : Nat → Nat
  | 0     => 0
  | n + 1 => (n + 1) + sumUpTo n

example : sumUpTo 0 = 0   := by rfl
example : sumUpTo 4 = 10  := by rfl
example : sumUpTo 10 = 55 := by rfl


/-
### Esercizio: Fibonacci

Definisci la funzione Fibonacci:

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


end Exercises_on_recursion


section Comparing_natural_numbers

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

example : eqN 3 3 = true    := by rfl
example : eqN 3 4 = false   := by rfl
example : leN 2 5 = true    := by rfl
example : leN 5 2 = false   := by rfl
example : leN 4 4 = true    := by rfl
example : subN 7 3 = 4      := by rfl
example : subN 3 7 = 0      := by rfl

/-
In ogni caso l'ultima equazione rimuove un costruttore da *entrambi* gli argomenti.
Quindi la chiamata ricorsiva è su argomenti più piccoli.
-/

/-
__Exercise__ (`ltN`): definisci `ltN n m`, che testa se `n < m`.
Suggerimento: `n < m` vale esattamente quando `n + 1 ≤ m`. Riutilizza `leN`.
-/

def ltN (n m : Nat) : Bool := leN (Nat.succ n) m

example : ltN 2 3 = true  := by rfl
example : ltN 3 3 = false := by rfl
example : ltN 4 3 = false := by rfl

end Comparing_natural_numbers


/-

## Dimostrazioni di proprietà dei numeri naturali

Nel resto della lezione sfruttiamo Lean per dimostrare formalmente alcune
proprietà che coinvolgono Nat.

-/


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
Oltre a questi casi semplici, `rfl` può anche dimostrare fatti più interessanti
che coinvolgono variabili quantificate. Ad esempio, poiché `addN` ricorre sul
suo *secondo* argomento, se in una proprietà tale argomento è zero, allora `rfl`
funziona, poiché `addN n 0` può essere calcolato.
-/

theorem addN_zero (n : Nat) : addN n 0 = n := by
  rfl

/-
La tattica `rfl` funziona anche per la seguente proprietà, che vale srotolando
la definizione di `addN`.
-/

theorem addN_succ_right (n m : Nat) : addN n (m + 1) = (addN n m) + 1 := by rfl

/-
__Exercise__: dimostra i teoremi corrispondenti per `mulN`:
* `mulN_zero`: n * 0 = 0;
* `mulN_succ`: n * (m+1) = n * m + n
-/

theorem mulN_zero (n : Nat) : mulN n 0 = 0 := by rfl

theorem mulN_succ (n m : Nat) : mulN n (m + 1) = addN (mulN n m) n := by rfl


end Proofs_by_simplification


section Proofs_by_rewriting

/-
### Riscrittura

I teoremi non sono solo da dimostrare: possono essere *usati* nelle dimostrazioni
di altri teoremi. La tattica `rw [h]`, dove `h` è un'equazione `a = b`,
sostituisce `a` con `b` nel goal.
-/

theorem succ_addN_zero : ∀ n : Nat, Nat.succ (addN n 0) = Nat.succ n := by
  intros n          --- sceglie un nome per la variabile quantificata
  rw [addN_zero]    --- addN n 0 = n

/-
Per capire perché tale dimostrazione funziona, posiziona il cursore a sinistra
del `rw` e guarda il goal nella Infoview:

  (addN n 0).succ = n.succ

Sappiamo dal teorema `addN_zero` che `addN n 0 = n`. Quindi, dopo la riscrittura
abbiamo un'uguaglianza.
-/

/-
Ecco un altro esempio di applicazione della tattica `rw`.
-/
theorem addN_id : ∀ n m : Nat,
  n = m →
  n + n = m + m := by
  intros n m        --- scegli nomi per le variabili universalmente quantificate
  intros h          --- sposta l'antecedente dell'implicazione nelle ipotesi
  rw [h]            --- riscrive h nel goal usando l'ipotesi h (da sinistra a destra)

/-
Nota una piccola differenza tra le dimostrazioni precedenti:
* In `succ_addN_zero`, l'uguaglianza usata in `rw` è presa da un altro teorema (`addN_zero`)
* In `addN_id`, l'uguaglianza usata in `rw` è presa dal *contesto*.
-/

/-
È importante notare che le riscritture hanno una direzione. Nelle dimostrazioni
precedenti, questa direzione era implicitamente da *sinistra a destra*. Ad esempio,
dopo l'applicazione di `rw [h]` in `addN_id`, il goal è ridotto a `m = m`
(controlla la Infoview).

È anche possibile applicare la riscrittura *da destra a sinistra* (controlla la
differenza nella Infoview).
-/
theorem addN_id₂ : ∀ n m : Nat,
  n = m →
  n + n = m + m := by
  intros n m        --- scegli nomi per le variabili universalmente quantificate
  intros h          --- sposta l'antecedente dell'implicazione nelle ipotesi
  rw [<-h]          --- riscrive h nel goal usando l'ipotesi h (da destra a sinistra)


/-
### Fatti che *non* valgono per calcolo

Che dire dell'affermazione simmetrica

    addN 0 n = n

dove `n` è un numero naturale arbitrario? L'espressione `addN 0 n` non può
essere calcolata finché non sappiamo quale numero naturale è `n`, perché `addN`
ispeziona il suo secondo argomento. Se provi

    example (n : Nat) : addN 0 n = n := by
      rfl

Lean riporta un errore. Abbiamo bisogno di una nuova idea: ragionare per *casi*
o per *induzione*.

-/

end Proofs_by_rewriting


section Proofs_by_case_analysis

/-
### Analisi per casi

La tattica `cases` è la controparte dimostrativa del pattern matching nelle definizioni.
Per un numero naturale `n` ci sono due casi:

* `n = 0`;
* `n = k + 1` per qualche numero naturale `k`.

Lean crea un goal per ogni caso. Considera l'affermazione che `leN n 0` è
vero se e solo se `n` è zero, espressa confrontandola con `isZero n`.
Nessuno dei due lati può essere calcolato finché `n` è sconosciuto, ma ogni caso può esserlo.
-/

theorem leN_zero_right (n : Nat) : leN n 0 = isZero n := by
  cases n with
  | zero   => rfl
  | succ _ => rfl

/-
Dopo `cases n with`, scriviamo un'alternativa per ogni costruttore.
Nel caso `succ` Lean darebbe un nome al numero dentro il successore; qui
non ci serve, quindi usiamo il wildcard `_`.

__Exercise__: Dimostra allo stesso modo che `isZero n = eqN n 0`.
-/

theorem isZero_eq_eqN (n : Nat) : isZero n = eqN n 0 := by
  cases n with
  | zero   => rfl
  | succ _ => rfl


/-
### Analisi per casi su un'uguaglianza

Dimostriamo che `Nat.succ` è iniettiva: due numeri naturali con lo stesso
successore sono uguali.
-/

theorem succN_injective : ∀ n m : Nat, Nat.succ n = Nat.succ m → n = m := by
  intros n m h
  cases h
  rfl

/-
Dopo `intros n m h`, Lean mostra (potrebbe stampare `n.succ` per `Nat.succ n`):

    n m : Nat
    h : Nat.succ n = Nat.succ m
    ⊢ n = m

Finora abbiamo usato `cases` sui numeri naturali. Qui la usiamo su un'ipotesi
`h`, che è essa stessa una *dimostrazione*.

L'uguaglianza è un tipo induttivo con un solo costruttore:

    Eq.refl a : a = a

(In realtà, il termine `rfl` è una scorciatoia per questo costruttore. In modalità
tattica, la tattica `rfl` chiude un goal di uguaglianza costruendo tale dimostrazione.)

Quindi, quando scriviamo `cases h` nella nostra dimostrazione, Lean considera
l'unico possibile caso di costruttore per una dimostrazione di uguaglianza: il
caso in cui `h` è una dimostrazione di riflessività.

Vediamo cosa significa nel nostro esempio. Una dimostrazione di riflessività per
`Nat.succ n` ha tipo:

    Eq.refl (Nat.succ n) : Nat.succ n = Nat.succ n

Ma il tipo di `h` è:

    Nat.succ n = Nat.succ m

Per far coincidere questi due tipi, Lean deve far combaciare:

    Nat.succ n    con    Nat.succ m

Entrambe le espressioni sono costruite usando lo stesso costruttore, `Nat.succ`,
quindi i loro argomenti devono combaciare. Lean quindi *unifica* `m` con `n`.

Infatti, il contesto e il goal diventano:

    n : Nat
    h : Nat.succ n = Nat.succ n         (potrebbe essere rimosso dalla Infoview)
    ⊢ n = n

Il goal finale è un'uguaglianza riflessiva, quindi `rfl` lo dimostra.

Questo non significa che ogni dimostrazione di uguaglianza debba essere
letteralmente scritta usando `rfl`: le dimostrazioni di uguaglianza possono
essere ottenute da ipotesi o altri teoremi. Piuttosto, significa che `Eq.refl`
è l'unico caso di costruttore da considerare quando si elimina una dimostrazione
di uguaglianza.
-/

/-
Nota che se `h` enuncia un'uguaglianza impossibile, come

    h : Nat.succ n = 0

il caso del costruttore riflessivo sarebbe impossibile: `Nat.succ` e `Nat.zero`
sono costruttori diversi. Di conseguenza, `cases h` chiuderebbe il goal
senza produrre nuovi goal.
-/

theorem succ_ne_zero_example (n : Nat) : Nat.succ n = 0 → False := by
  intro h
  cases h


end Proofs_by_case_analysis


section Proofs_by_exact

/-
### Chiudere un goal con `exact`

Dimostriamo che l'uguaglianza è transitiva: se `a = b` e `b = c`, allora `a = c`.
Formalmente, l'affermazione dice: per tutti i numeri naturali `a`, `b`, `c`,
se `a = b`, allora se `b = c`, allora `a = c` (le parentesi sono usate solo per chiarezza).
-/

theorem eq_trans : ∀ a b c : Nat, (a = b) → (b = c) → (a = c) := by
  intros a b c      --- scegli nomi per le variabili quantificate
  intros h1         --- sposta l'assunzione `a = b` nel contesto
  intros h2         --- sposta l'assunzione `b = c` nel contesto
  rw [h1]           --- riscrive `h1` nel goal
  exact h2          --- applica `h2` per chiudere il goal

/-
La tattica `intros` sposta le assunzioni dell'enunciato nel contesto,
dando loro dei nomi. Dopo i tre `intros`, Lean mostra:

    a b c : Nat
    h1 : a = b
    h2 : b = c
    ⊢ a = c

Le ipotesi sono dimostrazioni. `h1` è una dimostrazione di `a = b`, e `h2` è una
dimostrazione di `b = c`. Dobbiamo dimostrare `a = c`.

La tattica `rw [h1]` sostituisce `a` con `b` nel goal. Il goal diventa

    ⊢ b = c

`rw` cerca di chiudere il goal con `rfl`, ma `b` e `c` sono variabili diverse,
quindi il goal rimane aperto.

Ora il goal è esattamente l'enunciato dell'ipotesi `h2`. La tattica
`exact h2` chiude il goal fornendo una dimostrazione di *esattamente* ciò che
resta da dimostrare. In generale:

    exact t     chiude il goal corrente se `t` è una dimostrazione del goal.

Il termine `t` è spesso un'ipotesi, come qui, o un teorema applicato ad argomenti,
come `addN_zero n`.

Possiamo riscrivere l'enunciato in un modo alternativo, omettendo i quantificatori.
La dimostrazione è la stessa.
-/

theorem eq_trans₂ (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1]
  exact h2

/-
Possiamo anche riscrivere all'interno del contesto. Illustriamo questa funzionalità
sullo stesso enunciato. Controlla come cambia il contesto nella Infoview.
-/

theorem eq_trans₃ (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [<- h1] at h2
  exact h2


/-
__Exercise__: (`addN_zero_eq`) Usa `rw` e `exact` per dimostrare la seguente proprietà.
-/

theorem addN_zero_eq (n m : Nat) (h : n = m) : addN n 0 = m := by
  rw [addN_zero]
  exact h

/-
__Exercise__: (`addN_zero_trans`) Dimostra la seguente proprietà.
-/

theorem addN_zero_trans : ∀ a b c : Nat, a = b → b = c → addN a 0 = c := by
  intros a b c hab hbc
  rw [addN_zero]
  rw [hab]
  exact hbc

end Proofs_by_exact


section Proofs_with_have

/-
## Fatti intermedi con `have`

Una dimostrazione può essere più facile da capire se la dividiamo in passi più piccoli.
La tattica `have` ci permette di dimostrare un fatto intermedio e dargli un nome.
-/

example (a b c : Nat) (hab : a = b) (hbc : b = c) :
    Nat.succ a = Nat.succ c := by
  have hac : a = c := by    -- prima dimostra il fatto intermedio `a = c`
    rw [hbc] at hab         -- (guarda l'ipotesi cambiata)
    exact hab
  cases hac                 -- poi usa il fatto intermedio `hac`.
  rfl

/-
La forma generale è:

    have name : proposition := by
      proof

Lean cambia temporaneamente il goal in `proposition`. Una volta che quella
proposizione è stata dimostrata, il goal originale viene ripristinato e il nuovo
fatto è disponibile come `name`.

Usare `have` è utile quando un risultato intermedio ha un chiaro significato o
verrà usato più avanti nella dimostrazione.
-/


end Proofs_with_have


section Proofs_by_backward_reasoning

/-
### Ragionamento all'indietro

Usiamo `succN_injective` per dimostrare che due successori possono essere
rimossi su entrambi i lati di un'equazione. Nota che `succN_injective a b` non è
un'equazione. È un'implicazione:

    succN_injective a b : Nat.succ a = Nat.succ b → a = b

La sua *conclusione* è `a = b`, e la sua *premessa* è `Nat.succ a = Nat.succ b`.
Possiamo usare un tale teorema per ragionare *all'indietro*: per dimostrare la
conclusione, è sufficiente dimostrare la premessa. Lean offre due modi per farlo.

#### Primo modo: `rw` con un'equazione condizionale
-/

theorem succ_succ_injective (a b : Nat) : a.succ.succ = b.succ.succ → a = b := by
  intro h
  rw [<- succN_injective a b]
  rw [<- succN_injective a.succ b.succ]
  exact h

/-
Dopo `intro h`, Lean mostra:

    h : a.succ.succ = b.succ.succ
    ⊢ a = b

Il teorema `succN_injective a b` ha l'equazione `a = b` come conclusione, quindi
`rw` può usarlo. La freccia `<-` (anche scritta `←`) significa "da destra a sinistra":
`b` è sostituito da `a`. Il goal diventa `a = a`, che `rw` chiude con `rfl`.
La premessa del teorema non scompare: diventa il nuovo goal,

    ⊢ a.succ = b.succ

Il secondo `rw` fa lo stesso un livello più su e lascia

    ⊢ a.succ.succ = b.succ.succ

che è l'ipotesi `h`. Quindi `exact h` finisce la dimostrazione.

#### Secondo modo: `apply`

La tattica `apply` esprime la stessa idea direttamente.
-/

theorem succ_succ_injective₂ (a b : Nat) : a.succ.succ = b.succ.succ → a = b := by
  intro h
  apply succN_injective a b
  apply succN_injective a.succ b.succ
  exact h

/-
La regola è:

    apply t     dove `t : P → Q` e il goal corrente è `Q`:
                sostituisce il goal `Q` con il goal `P`.

In parole: "per dimostrare `Q` è sufficiente dimostrare `P`, perché `t` trasforma
una dimostrazione di `P` in una dimostrazione di `Q`". Seguiamo la nostra dimostrazione:

    dopo intro h:
        h : a.succ.succ = b.succ.succ
        ⊢ a = b

    dopo apply succN_injective a b:
        ⊢ a.succ = b.succ              -- la premessa

    dopo apply succN_injective a.succ b.succ:
        ⊢ a.succ.succ = b.succ.succ    -- di nuovo la premessa

L'ultimo goal è esattamente `h`, quindi `exact h` lo chiude. (Lean potrebbe
stampare `a.succ` come `a + 1`: è lo stesso enunciato.)

Alcuni dettagli da ricordare:

* Se `t` ha diverse premesse, `t : P1 → P2 → Q`, allora `apply t` crea un goal
  per ogni premessa, in ordine.
* Se `t` non ha premesse, `apply t` chiude semplicemente il goal, come `exact t`.
* Il goal deve corrispondere alla *conclusione* di `t`. Se non lo fa, Lean
  riporta un errore mostrando entrambi gli enunciati, come con `exact`.
* Spesso Lean riesce a trovare gli argomenti da solo. Prova a scrivere
  `apply succN_injective` senza `a b`: Lean confronta la conclusione `?n = ?m`
  con il goal `a = b`.

Confronta i tre strumenti che ora conosciamo per usare un teorema `t`:

    exact t     l'enunciato di `t` è esattamente il goal;
    rw [t]      `t` è un'equazione, e vogliamo riscrivere con essa;
    apply t     `t` è un'implicazione, e la sua conclusione è il goal:
                continuiamo con le sue premesse.

La dimostrazione con `apply` è anche più flessibile di `rw`: `rw` ha bisogno che
la conclusione sia un'equazione, mentre `apply` funziona con qualsiasi enunciato.

Infine, possiamo anche ragionare *in avanti*, dall'ipotesi al goal, applicando il
teorema a una dimostrazione, in un solo passo:

    exact succN_injective a b (succN_injective a.succ b.succ h)

Tutte e tre le dimostrazioni sono corrette. Le versioni con `rw` e `apply`
lavorano all'indietro dal goal e mostrano un nuovo goal dopo ogni passo, il che
le rende facili da seguire nella Infoview. La versione con `exact` costruisce
l'intera dimostrazione in una volta.
-/

end Proofs_by_backward_reasoning


/-
## Riepilogo

Non abbiamo bisogno di conoscere ogni tattica di Lean per fare questo. Un piccolo
kit di strumenti è già sufficiente per molte dimostrazioni elementari:

* `rfl`       -- chiude un'uguaglianza che segue per calcolo;
* `rw [h]`    -- riscrive il goal usando l'equazione `h` (da sinistra a destra);
* `rw [<-h]`  -- riscrive il goal usando l'equazione `h` (da destra a sinistra);
* `exact`     -- chiude il goal usando un'ipotesi nel contesto;
* `apply`     -- applica un'implicazione nel contesto a un goal;
* `simp`      -- semplifica ripetutamente usando definizioni e lemmi noti;
* `have`      -- dimostra fatti intermedi;
* `cases`     -- divide un valore induttivo nei suoi costruttori;
-/


section Exercises

/-
## Esercizi
-/

/-
### Esercizio: Definizioni equivalenti di successore
-/

theorem addN_one_right (n : Nat) : addN n 1 = Nat.succ n := by
  rfl


/-
### Esercizio: Sommare successori

Dimostra la seguente proprietà. Suggerimento: usa proprietà esistenti su addN e successori
-/

theorem addN_self_succ (n : Nat) : addN (n + 1) (n + 1) = addN n n + 1 + 1 := by
  -- Suggerimento: usa addN_succ_right due volte
  -- Attenzione: questo non è banale. Una dimostrazione per induzione è appropriata.
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [addN_succ_right]
    rw [addN_succ_right]
    rw [ih]


/-
### Esercizio: Riscrittura ripetuta

Usa `addN_succ_right` due volte. Osserva il goal nella Infoview dopo ogni
applicazione di `rw`.
-/

theorem addN_two_steps (n m : Nat) :
    addN n (m + 1 + 1) = addN n m + 1 + 1 := by
  rw [addN_succ_right]
  rw [addN_succ_right]


/-
### Esercizio: Riscrivere un'ipotesi

Riscrivi entrambe le occorrenze di `addN` in `h`, usando `addN_zero n` e
`addN_zero m`. Poi chiudi il goal con `exact`.
-/

theorem addN_zero_cancel (n m : Nat)
    (h : addN n 0 = addN m 0) : n = m := by
  rw [addN_zero] at h
  rw [addN_zero] at h
  exact h


/-
### Esercizio: Riscrittura da destra a sinistra

Usa `hab` da destra a sinistra nel goal, e poi usa `exact`.
-/

theorem eq_from_common_left (a b c : Nat)
    (hab : a = b) (hac : a = c) : b = c := by
  rw [<- hab]
  exact hac


/-
### Esercizio: Analisi per casi su un numero naturale

Dimostra il risultato considerando i casi `zero` e `succ` per `n`. Entrambi
i goal risultanti possono essere chiusi per calcolo.
-/

theorem leN_eq_eqN_zero (n : Nat) : leN n 0 = eqN n 0 := by
  cases n with
  | zero   => rfl
  | succ _ => rfl


/-
### Esercizio: Analisi per casi su un'uguaglianza impossibile

Introduci l'uguaglianza come ipotesi e poi fai analisi per casi su di essa.
-/

theorem zero_ne_succ (n : Nat) : 0 = Nat.succ n → False := by
  intro h
  cases h


/-
### Esercizio: Ragionamento all'indietro con due premesse

Usa `apply eq_trans₂ a b c`. Questo crea due goal: risolvili usando le
ipotesi `hab` e `hbc`.
-/

theorem eq_trans_apply (a b c : Nat)
    (hab : a = b) (hbc : b = c) : a = c := by
  apply eq_trans₂ a b c
  · exact hab
  · exact hbc


/-
### Esercizio: Ragionamento all'indietro ripetuto

Usa `succN_injective` tre volte con `apply`, e finisci con `exact h`.
-/

theorem succ_succ_succ_injective (a b : Nat) :
    Nat.succ (Nat.succ (Nat.succ a)) =
      Nat.succ (Nat.succ (Nat.succ b)) →
    a = b := by
  intro h
  apply succN_injective a b
  apply succN_injective a.succ b.succ
  apply succN_injective a.succ.succ b.succ.succ
  exact h


/-
### Esercizio: Fatti intermedi con `have`

Prima usa `have` e `succN_injective` per ottenere dimostrazioni di `a = b` e
`b = c`. Poi combina questi fatti intermedi per dimostrare `a = c`.
-/

theorem eq_from_succ_chain (a b c : Nat)
    (hab : Nat.succ a = Nat.succ b)
    (hbc : Nat.succ b = Nat.succ c) : a = c := by
  have h1 : a = b := succN_injective a b hab
  have h2 : b = c := succN_injective b c hbc
  rw [h1]
  exact h2


/-
### Esercizio: Semplificazione usando un'ipotesi

Usa `simp [h]` per sostituire `eqN a b` con `false` e calcolare la sua
negazione booleana.
-/

theorem not_eqN_of_false (a b : Nat) (h : eqN a b = false) :
    !(eqN a b) = true := by
  simp [h]

/-
### Esercizio: Sommare numeri uguali

Risolvi riscrivendo i teoremi o le assunzioni giuste.
-/

theorem plus_id : ∀ n m o : Nat, n = m → m = o → n + m = m + o := by
  intros n m o hnm hmo
  rw [hnm]
  rw [hmo]

/-
### Esercizio: Moltiplicare per zero

Risolvi riscrivendo i teoremi o le assunzioni giuste.
-/

theorem mult_n_0_m_0 : ∀ n m : Nat, addN (mulN n 0) (mulN m 0) = 0 := by
  intros n m
  rw [mulN_zero]
  rw [mulN_zero]
  rfl

/-
### Esercizio: Uno non è doppio

Suggerimento: puoi eliminare una contraddizione `h` con `cases h`.
-/

theorem one_not_double : ∀ n, 1 = mulN 2 n → False := by
  intro n h
  cases n with
  | zero =>
    rw [mulN_zero] at h
    cases h
  | succ k =>
    rw [mulN_succ] at h
    cases h

end Exercises