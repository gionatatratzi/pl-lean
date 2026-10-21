/-
Il seguente import porta nello scope le definizioni e i teoremi delle lezioni
precedenti, inclusi `addN`, `mulN`, `doubleN`, `isEven` e `eqN`.

Se stai lavorando su `https://live.lean-lang.org/`, rimuovi l'import e
copia il codice necessario dalle lezioni precedenti prima di questo file.
-/

import PL_Lean.PL03_Induction


set_option autoImplicit false


/-
# Tipi funzione e funzioni di ordine superiore

Finora, la maggior parte delle nostre funzioni consumava dati ordinari come
booleani e numeri naturali. In questa lezione prendiamo sul serio un'importante
idea della programmazione funzionale:

    una funzione è essa stessa un valore.

Una funzione può quindi essere nominata, passata come argomento, selezionata da
un condizionale, o restituita come risultato di un'altra funzione. Le funzioni
che consumano o producono funzioni sono chiamate *funzioni di ordine superiore*.

Alla fine della lezione dovresti essere in grado di:

* leggere tipi funzione contenenti diverse frecce e parentesi;
* ricordare che le frecce associano a destra e le applicazioni a sinistra;
* scrivere funzioni anonime con `fun`;
* usare l'applicazione parziale;
* definire funzioni che accettano o restituiscono altre funzioni;
* usare composizione e iterazione per costruire nuovi calcoli;
* dimostrare proprietà puntuali e uguaglianze tra funzioni;
* spiegare il ruolo di ogni argomento di una funzione di ordine superiore.

Per il momento, i nostri tipi di dato rimarranno `Bool` e `Nat`. L'unico
costruttore di tipo introdotto qui è la freccia funzione `→`.

Le difficoltà degli esercizi usano la stessa scala relativa di PL03:

* **1/4:** un'idea diretta;
* **2/4:** due idee devono essere combinate;
* **3/4:** una costruzione di ordine superiore più sostanziale;
* **4/4:** una sfida opzionale.
-/


section Reading_function_types

/-
## Leggere tipi funzione semplici

Per questa lezione, i tipi che usiamo possono essere descritti informalmente dalla grammatica

    T ::= Bool | Nat | T₁ → T₂

Il sistema di tipi di Lean è molto più ricco di così. Stiamo deliberatamente
lavorando dentro questo piccolo frammento semplicemente tipato per poterci
concentrare sui valori funzione.

`Bool` e `Nat` sono *tipi base*. Se `A` e `B` sono tipi, allora

    A → B

è il tipo delle funzioni che accettano un input di tipo `A` e restituiscono un
risultato di tipo `B`. Chiamiamo `A` il *dominio* e `B` il *codominio*.

Due regole spiegano la maggior parte di ciò che accade in questa lezione:

* **creazione di funzione:** se un'espressione `e` ha tipo `B` mentre `x` ha tipo
  `A`, allora `fun x : A => e` ha tipo `A → B`;
* **applicazione di funzione:** se `f : A → B` e `a : A`, allora `f a : B`.

Nella regola di applicazione, il tipo dell'argomento deve corrispondere al
dominio della funzione. Il tipo dell'intera applicazione è il codominio della
funzione. Il type checking previene quindi dal connettere calcoli incompatibili.

-/

#check Nat.succ
#check isEven
#check addN

/-
Lean riporta i seguenti tipi:

    Nat.succ : Nat → Nat
    isEven   : Nat → Bool
    addN     : Nat → Nat → Nat

I primi due tipi hanno una freccia:

* `Nat.succ` consuma un numero naturale e restituisce un numero naturale;
* `isEven` consuma un numero naturale e restituisce un booleano.

Il tipo di `addN` contiene due frecce. Le frecce associano a *destra*, quindi

    Nat → Nat → Nat

significa

    Nat → (Nat → Nat)

e non

    (Nat → Nat) → Nat.

Quindi `addN` prima consuma un `Nat`; il suo risultato è una funzione che consuma
il secondo `Nat` e infine restituisce un `Nat`.
-/

#check addN 5
#check (addN 5 : Nat → Nat)
#check addN 5 3

/-
L'applicazione di funzione associa a *sinistra*. Pertanto

    addN 5 3

significa

    (addN 5) 3.

Queste due convenzioni lavorano insieme:

    le frecce associano a destra; le applicazioni associano a sinistra.

Le parentesi possono cambiare radicalmente un tipo:

    Nat → Nat → Nat          una funzione consuma un Nat e restituisce una funzione
    (Nat → Nat) → Nat        una funzione che consuma una funzione e restituisce un Nat
    (Nat → Nat) → Nat → Nat  una funzione che consuma una funzione, poi un Nat

Le parentesi attorno a `Nat → Nat` negli ultimi due tipi non possono essere omesse.
-/

/-
__Exercise__: Spiega perché i seguenti comandi commentati sarebbero rifiutati.
Non decommentare entrambi contemporaneamente: leggi un errore atteso alla volta.

-- #check Nat.succ false
-- #check addN Nat.succ 3
-- #check addN 1 true
-/

-- Risposta:
-- #check Nat.succ false  → Nat.succ si aspetta un Nat, ma false è un Bool.
-- #check addN Nat.succ 3 → addN si aspetta un Nat come primo argomento, ma
--   Nat.succ è una funzione Nat → Nat.
-- #check addN 1 true     → addN 1 si aspetta un Nat come secondo argomento,
--   ma true è un Bool.

end Reading_function_types



section Anonymous_functions

/-
## Funzioni anonime

Una funzione non ha bisogno di un nome. L'espressione

    fun n : Nat => n + 1

è una *funzione anonima*, chiamata anche *astrazione lambda*. Accetta un numero
naturale chiamato `n` e restituisce `n + 1`.
-/

#check (fun n : Nat => n + 1)
#eval (fun n : Nat => n + 1) 5

/-
L'applicazione di funzione sostituisce l'argomento al parametro:

    (fun n : Nat => n + 1) 5
    = 5 + 1
    = 6

L'annotazione di tipo `: Nat` può essere omessa, poiché Lean può inferire il tipo
dal contesto.
-/

/- Naturalmente possiamo dare nomi a funzioni definite anonimamente -/
def incr := fun n : Nat => n + 1

/-
Il seguente teorema afferma che le due funzioni restituiscono lo stesso risultato
su ogni input. Questo è enunciato come un'*uguaglianza puntuale*. Più avanti
esprimeremo risultati simili come *uguaglianza di funzioni*.
-/
example : ∀ (n : Nat), incr n = (fun n : Nat => n + 1) n := by
  intros n
  rfl


/- __Exercise__: Risolvi i sorry. -/

example : (fun f => f 5) (fun n => n + 1) = 6 := by rfl
example : (fun f => f 5) (fun n => n * n) = 25 := by rfl


/-
Una funzione anonima può usare variabili dal contesto circostante:
-/

def incrBy (k : Nat) : Nat → Nat := fun n => n + k

/-
Il parametro `k : Nat` fornito nel contesto può essere equivalentemente spostato
sotto l'astrazione lambda.
-/

example (k n : Nat): incrBy k n = (fun k : Nat => fun n : Nat => n + k) k n := by rfl

example : ∀ (k n : Nat), incrBy k n = (fun k : Nat => fun n : Nat => n + k) k n := by
  intros k n
  rfl

end Anonymous_functions



section Functions_as_arguments

/-
## Passare funzioni come argomenti

Ecco un esempio più interessante di funzione di ordine superiore: applicare una
data funzione due volte.
-/

def applyTwiceN (f : Nat → Nat) (n : Nat) : Nat := f (f n)


/-
Lean stampa un tipo equivalente a

    applyTwiceN : (Nat → Nat) → Nat → Nat

Leggilo da sinistra a destra, rispettando le parentesi:

1. `applyTwiceN` riceve prima una funzione `f : Nat → Nat`;
2. poi riceve un valore iniziale `n : Nat`;
3. infine restituisce un `Nat`.

L'implementazione non sa cosa fa `f`. Sa solo che l'output di `f` è un altro
`Nat`, così che è legale applicare `f` di nuovo.

Questo è il motivo per cui `isEven` non può essere fornita a `applyTwiceN`:
`isEven` restituisce un `Bool`, ma una seconda applicazione richiederebbe un
altro `Nat`.

    -- #check applyTwiceN isEven 5
-/


/- __Exercise__: Risolvi i sorry -/
example : applyTwiceN Nat.succ 5 = 7 := by rfl
example : applyTwiceN doubleN 3 = 12 := by rfl
example : applyTwiceN (fun n => n * n) 2 = 16 := by rfl
example : applyTwiceN (applyTwiceN Nat.succ) 0 = 4 := by rfl


/- __Exercise__: Definisci una funzione `applyThreeTimesN` che soddisfi i test dati. -/

def applyThreeTimesN (f : Nat → Nat) (n : Nat) : Nat := f (f (f n))

example : applyThreeTimesN Nat.succ 5 = 8 := by rfl
example : applyThreeTimesN doubleN 1 = 8 := by rfl

end Functions_as_arguments



section Functions_as_return_values

/-
## Applicazione parziale e funzioni che restituiscono funzioni

Ricorda il tipo

    addN : Nat → (Nat → Nat).

Abbiamo già notato che se forniamo solo il primo argomento `Nat`,
il risultato è una funzione di tipo `Nat → Nat`:
-/

def addFive : Nat → Nat := addN 5

/-
Fornire meno argomenti di quanti una funzione possa alla fine consumare è
chiamato *applicazione parziale*. Non è coinvolto alcun meccanismo speciale:
`addN 5` è semplicemente il risultato della prima applicazione di funzione.
-/

/-
Le funzioni sono valori ordinari, quindi un condizionale può selezionare tra esse.
-/

def chooseN (s : Bool) (f g : Nat → Nat) : Nat → Nat :=
  if s then f else g

/- __Exercise__: Risolvi i sorry. -/

example : chooseN true  doubleN Nat.succ 4 = 8 := by rfl
example : chooseN false doubleN Nat.succ 4 = 5 := by rfl

/-
Nota che `chooseN` non esegue `f` o `g`: sceglie solo una delle due funzioni.
La funzione scelta viene applicata a `4` solo dopo.
-/


/- __Exercise__: definisci una funzione `sumFun : (Nat → Nat) → (Nat → Nat) → (Nat → Nat)`
che restituisce la somma puntuale dei suoi input. Cioè, `sumFun f g` restituisce una
funzione `h` tale che `h(n) = f(n) + g(n)`, per ogni `n : Nat`.
-/

def sumFun : (Nat → Nat) → (Nat → Nat) → (Nat → Nat) :=
  fun f g => fun n => f n + g n

example : sumFun (fun n => n+1) (fun n => n+n) 3 = 10 := by rfl
example : sumFun (fun n => n+1) (fun n => n+n) 5 = 16 := by rfl

end Functions_as_return_values



section Composition

/-
## Costruire funzioni per composizione

Date due funzioni

    f : Nat → Nat
    g : Nat → Nat

possiamo costruire una nuova funzione che prima applica `g` e poi applica `f` al risultato.
Questa operazione è chiamata *composizione di funzioni*.
-/

def composeN (f g : Nat → Nat) : Nat → Nat :=
  fun n => f (g n)

/- __Exercise__: risolvi i sorry -/

example : composeN Nat.succ doubleN 3 = 7 := by rfl
example : composeN doubleN Nat.succ 3 = 8 := by rfl

/-
Dopo aver risolto l'esercizio precedente, dovresti renderti conto che la composizione
di funzioni è sensibile all'ordine. In `composeN f g`, la funzione `g` è quella
applicata per prima.

Più in generale, la composizione è ben tipata quando il tipo di output del primo
calcolo corrisponde al tipo di input del secondo. Ad esempio, la funzione
`applyThenTest` prima applica una funzione `f : Nat → Nat` al suo argomento, e poi
la testa con una funzione `p : Nat → Bool`.
-/

def applyThenTest (p : Nat → Bool) (f : Nat → Nat) : Nat → Bool :=
  fun n => p (f n)

/- __Exercise__: risolvi i sorry -/

example : applyThenTest isEven Nat.succ 3 = true := by rfl
example : applyThenTest isEven Nat.succ 4 = false := by rfl

/-
Lean ha un operatore di composizione integrato `∘`, inserito come `\comp`:
-/

example : ((fun n : Nat => n + 1) ∘ (fun n : Nat => n * 2)) 5 = 11 := by rfl


/-
### Uguaglianza tra funzioni

Per dimostrare che due funzioni sono uguali, è sufficiente dimostrare che
restituiscono risultati uguali su ogni input. Questo principio è chiamato
*estensionalità delle funzioni*.

Abbiamo già usato questo principio sopra, per dimostrare che `incrBy` è uguale
alla sua versione anonima.

La tattica `funext` introduce un input arbitrario e trasforma un goal di
uguaglianza di funzioni in un'uguaglianza puntuale.
-/

def idN : Nat → Nat := fun n => n

theorem composeN_identity_left (f : Nat → Nat) : composeN idN f = f := by
  funext n
  rfl

/-
__Exercise__: dimostra che `idN` è anche l'identità a destra della composizione.
-/

theorem composeN_identity_right (f : Nat → Nat) : composeN f idN = f := by
  funext n
  rfl


/-
__Exercise__ Dimostra che la composizione di funzioni è associativa.
-/

theorem composeN_assoc (f g h : Nat → Nat) :
    composeN (composeN f g) h = composeN f (composeN g h) := by
  funext n
  rfl

end Composition



section State_transformers

/-
## Applicazione: programmi come trasformatori di stato

Una funzione `Nat → Nat` può essere letta come un piccolo programma che trasforma
uno stato. Ad esempio, supponiamo che lo stato sia il saldo di un conto bancario.
Un deposito e un prelievo sono funzioni dal vecchio saldo al nuovo.

Le funzioni restituite ricordano l'importo, quindi questi sono anche semplici
esempi di closure.
-/

def deposit (amount : Nat) : Nat → Nat :=
  fun balance => balance + amount

def withdraw (amount : Nat) : Nat → Nat :=
  fun balance => balance - amount

example : deposit 20 100 = 120 := by rfl
example : withdraw 7 100 = 93  := by rfl

/-
In questo contesto, la composizione di funzioni rappresenta l'esecuzione
sequenziale delle operazioni sul conto. Ricorda che la funzione scritta a destra
è eseguita per prima.
-/

example : composeN (deposit 20) (withdraw 7) 5 = 20 := by rfl

example : composeN (withdraw 7) (deposit 20) 5 = 18 := by rfl

/-
Questo esempio fornisce una ragione concreta per cui l'ordine della composizione
conta. Mostra anche perché le funzioni che rappresentano azioni sono valori utili:
possono essere assemblate in un programma più grande prima che qualsiasi stato
iniziale venga fornito.
-/

/-
__Exercise__: Dimostra che depositare zero è la trasformazione identità.

Suggerimento: Usa `funext` e `simp`.
-/

theorem deposit_zero : deposit 0 = idN := by
  funext balance
  simp [deposit, idN]

/-
__Exercise__: Dimostra che due depositi consecutivi possono essere combinati in uno.

Suggerimento: Usa `funext` e `simp`.
-/

theorem deposit_additivity (a b : Nat) : composeN (deposit a) (deposit b) = deposit (b + a) := by
  funext balance
  simp [composeN, deposit, Nat.add_assoc, Nat.add_comm]

/-
__Exercise__: Dimostra che l'effetto di un deposito può essere annullato da un
successivo prelievo.

Suggerimento: Usa la tattica `exists` per fornire un testimone per la variabile
esistenzialmente quantificata `b`.
-/

theorem deposit_reversibility : ∀ a : Nat, ∃ b : Nat, composeN (withdraw b) (deposit a) = idN := by
  intro a
  exists a
  funext balance
  simp [composeN, deposit, withdraw, idN]
  omega

end State_transformers



section Iteration

/-
## Iterare una funzione

La composizione descrive una sequenza fissa di operazioni. Spesso invece vogliamo
ripetere la stessa operazione un numero di volte che non è fisso nella definizione.

La funzione `iterateN` prende come input sia la funzione che vogliamo applicare sia
il numero di ripetizioni.

I tre argomenti giocano ruoli diversi:
* `f` descrive cosa fa un passo;
* `k` descrive quanti passi vengono eseguiti;
* `n` è lo stato iniziale.

Ad esempio:

    iterateN f 3 n = f (f (f n)).

La ricorsione controlla *quante volte* qualcosa accade; l'argomento funzione dice
*cosa* accade.
-/

def iterateN (f : Nat → Nat) (k n : Nat) : Nat :=
  match k with
  | 0      => n                     -- applicare una funzione zero volte lascia il valore iniziale invariato
  | k' + 1 => f (iterateN f k' n)

example : iterateN Nat.succ 5 0 = 5 := by rfl

/- __Exercise__ Risolvi i sorry -/

example : iterateN Nat.succ 3 12 = 15 := by rfl
example : iterateN (fun n => n + 3) 4 0 = 12 := by rfl
example : iterateN (addN 2) 4 1 = 9 := by rfl

/- Possiamo facilmente dimostrare che `applyTwice` è un caso speciale di `iterateN` quando `k=2` -/
theorem applyTwiceN_eq_iterateN2 (f : Nat → Nat) :
    applyTwiceN f = iterateN f 2 := by
  rfl


/- __Exercise__ Definisci la funzione `pow2` (esponenziazione in base 2) usando `iterateN` (niente ricorsione!). -/
def pow2 (n : Nat) : Nat := iterateN doubleN n 1

example : pow2 0 = 1 := by rfl
example : pow2 1 = 2 := by rfl
example : pow2 2 = 4 := by rfl
example : pow2 3 = 8 := by rfl


/-
### Punti fissi e induzione

Un valore `x` è un *punto fisso* di una funzione `f` quando applicare `f` a `x`
non lo cambia:

    f x = x

Il teorema sotto dice che se il valore iniziale `x` è un punto fisso di `f`,
allora applicare `f` ripetutamente un numero qualsiasi di volte produce ancora `x`.

Questo è il primo teorema in cui uno dei parametri è una *dimostrazione*:

    h : f x = x

Qui `h` è un'ipotesi. Il teorema dice:

    per ogni f, x e k,
    se f x = x,
    allora iterateN f k x = x.

Equivalentemente, il suo enunciato potrebbe essere scritto usando un'implicazione:

    ∀ (f : Nat → Nat) (x k : Nat),
      f x = x → iterateN f k x = x

Scrivendo `(h : f x = x)` prima dei due punti finali, diamo un nome a questa
assunzione. La dimostrazione può poi usare `h` ogni volta che necessita di
evidenza che `f x = x`.
-/

theorem iterateN_fixed_point
  (f : Nat → Nat)         -- la funzione
  (x k : Nat)             -- un input arbitrario e il numero di ripetizioni
  (h : f x = x) :         -- ipotesi: x è un punto fisso di f
    iterateN f k x = x    -- tesi: iterare f non cambia l'input x
  := by
  induction k with
  | zero =>
      rfl
  | succ k' ih =>
      rw [iterateN]
      rw [ih]
      exact h

/-
__Exercise__ Dimostra che `addN n k` è equivalente a `iterateN Nat.succ k n`

Suggerimento: induzione su `k`
-/

theorem iterateN_succ_eq_addN (k n : Nat) :
    iterateN Nat.succ k n = addN n k := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    rw [iterateN]
    rw [ih]
    rw [addN_succ]

/-
__Exercise__ Sfrutta `iterateN_succ_eq_addN` come lemma ausiliario (usando la
tattica `have`) per dimostrare quanto segue.
-/

theorem iterateN_succ_from_zero (k : Nat) :
    iterateN Nat.succ k 0 = k := by
  have h := iterateN_succ_eq_addN k 0
  rw [h]
  rw [zero_addN]

end Iteration



section Bounded_experiments

/-
## Traversali di ordine superiore: piccole analisi di dati

Prima di introdurre le liste, un numero naturale può rappresentare l'intervallo finito

    0, 1, ..., n-1

La funzione di ordine superiore `sumBelow` prende come input una funzione `f : Nat → Nat`
e un indice `n : Nat`, e calcola la sommatoria:

    f 0 + f 1 + ... + f (n - 1)
-/

def sumBelow (f : Nat → Nat) (n : Nat) : Nat :=
  match n with
  | 0      => 0
  | n' + 1 => sumBelow f n' + f n'

/- __Exercise__ Risolvi i sorry. -/

example : sumBelow (λ _ => 1) 7 = 7         := by rfl
example : sumBelow (λ n => n) 5 = 10         := by rfl
example : sumBelow (λ n => n) 6 = 15         := by rfl
example : sumBelow (λ n => 2 * n - 1) 6 = 30 := by rfl
example : sumBelow (λ n => 2 * n - 1) 7 = 42 := by rfl

/-
__Exercise (difficoltà: 1/4)__ Dimostra che sommare la costante `1` conta gli
elementi nell'intervallo.
-/

theorem sumBelow_one (n : Nat) :
    sumBelow (fun _ => 1) n = n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [sumBelow]
    rw [ih]
    rfl

/-
__Exercise__ (**difficoltà: 1/4**): definisci `sumOfSquares` fornendo una
funzione anonima di quadratura a `sumBelow`. Non scrivere un'altra ricorsione.
-/

def sumOfSquares (n : Nat) : Nat :=
  sumBelow (fun i => i * i) n

example : sumOfSquares 0 = 0  := by rfl
example : sumOfSquares 4 = 14 := by rfl
example : sumOfSquares 6 = 55 := by rfl


/-
Una funzione `p : Nat → Bool` può essere vista come un predicato sui numeri naturali.
La funzione `countBelow` prende come input un tale predicato e un indice `n : Nat`,
e conta il numero di valori nell'intervallo `0, ..., n-1` che soddisfano `p`.
-/

def countBelow (p : Nat → Bool) (n : Nat) : Nat :=
  match n with
  | 0      => 0
  | n' + 1 => if p n' then countBelow p n' + 1 else countBelow p n'

example : countBelow isEven 10 = 5 := by rfl


/-
__Exercise (difficoltà: 1/4)__ Definisci la funzione `anyBelow`, che restituisce `true`
ogniqualvolta **esiste** qualche elemento nell'intervallo `0,...,n-1` che soddisfa `p`.
-/
def anyBelow (p : Nat → Bool) (n : Nat) : Bool :=
  match n with
  | 0      => false
  | n' + 1 => if p n' then true else anyBelow p n'

example : anyBelow (fun i => eqN i 7) 10  = true := by rfl
example : anyBelow (fun i => eqN i 11) 10 = false := by rfl
example : anyBelow (fun i => eqN i 10) 10 = false := by rfl

/-
__Exercise (difficoltà: 1/4)__ Definisci la funzione `allBelow`, che restituisce `true`
ogniqualvolta **tutti** gli elementi nell'intervallo `0,...,n-1` soddisfano `p`.
-/

def allBelow (p : Nat → Bool) (n : Nat) : Bool :=
  match n with
  | 0      => true
  | n' + 1 => if p n' then allBelow p n' else false

example : allBelow (fun i => eqN (addN i 0) i) 50 = true := by rfl
example : allBelow (fun i => eqN (doubleN i) i) 10 = false := by rfl
example : allBelow (fun i => ltN i 10) 10 = true := by rfl


end Bounded_experiments



section Exercises


section Exercises_repeated_additions

/-
### Esercizio: Addizioni ripetute

In questo esercizio studiamo una definizione alternativa di moltiplicazione basata
su funzioni iterate.
-/

/-
__Exercise (difficoltà: 1/4)__ Definisci `repeatAdd k a`, che restituisce una
funzione che aggiunge `a` al suo input `k` volte.
-/

def repeatAdd (k a : Nat) : Nat → Nat :=
  fun n => iterateN (fun x => x + a) k n

example : repeatAdd 3 5 10 = 25 := by rfl
example : repeatAdd 0 5 10 = 10 := by rfl

/-
__Exercise (difficoltà: 1/4)__ Dimostra il teorema `repeatAdd_succ_left`.
Suggerimento: non serve induzione.
-/

theorem repeatAdd_succ_left (a b c : Nat) : repeatAdd (a+1) b c = addN (repeatAdd a b c) b := by
  rfl

/-
__Exercise (difficoltà: 2/4)__ Dimostra la seguente equivalenza tra `repeatAdd` e `mulN`.
-/

theorem repeatAdd_eq_mulN (a b : Nat) : repeatAdd b a 0 = mulN a b := by
  induction b with
  | zero => rfl
  | succ b' ih =>
    rw [repeatAdd_succ_left]
    rw [ih]
    rw [mulN_succ]

end Exercises_repeated_additions



section Exercises_bounded_search

/-
### Esercizio: Ricerca limitata
-/


/-
__Exercise (difficoltà: 1/4)__ Dimostra che se un testimone è stato trovato sotto `n`,
rimane un testimone sotto `n+1`.
-/

theorem anyBelow_grows (p : Nat → Bool) (n : Nat)
    (h : anyBelow p n = true) : anyBelow p (n + 1) = true := by
  induction n with
  | zero =>
    rw [anyBelow] at h
    rw [anyBelow]
    rw [h]
  | succ n' ih =>
    rw [anyBelow] at h ⊢
    by_cases hp : p n'
    · rw [if_pos hp]
      rw [if_pos hp]
    · rw [if_neg hp] at h
      rw [if_neg hp]
      exact ih h

/-
__Exercise (difficoltà: 2/4)__ Dimostra che il predicato che restituisce sempre
`true` passa su ogni intervallo finito.
-/

theorem allBelow_true (n : Nat) :
    allBelow (fun _ => true) n = true := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [allBelow]
    rw [if_pos rfl]
    exact ih

/-
__Exercise (difficoltà: 2/4)__ Dimostra che controllare che tutti i valori
soddisfano `p` è equivalente a controllare che non esiste alcun valore che non
soddisfa `p`.

Suggerimento: per induzione su `n`.
-/

theorem allBelow_eq_not_anyBelow_not (p : Nat → Bool) (n : Nat) :
    allBelow p n = !(anyBelow (fun i => !(p i)) n) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [allBelow]
    rw [anyBelow]
    by_cases hp : p n'
    · rw [if_pos hp]
      rw [if_neg]
      · rw [ih]
        simp
      · simp [hp]
    · rw [if_neg hp]
      rw [if_pos]
      · rfl
      · simp [hp]

/-
__Exercise (difficoltà: 2/4)__ Dimostra che se `p` è vero per tutti i valori,
allora `allBelow p` è vero fino a qualsiasi `n`.

Suggerimento: induzione su `n`.
-/

theorem allBelow_of_forall
    (p : Nat → Bool)
    (n : Nat)
    (h : ∀ i : Nat, p i = true) :
    allBelow p n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [allBelow]
    rw [if_pos (h n')]
    exact ih


/-
__Exercise (difficoltà: 2/4)__ Sfrutta `allBelow` per definire un test limitato
per la commutatività. Cioè, `checkCommutativeBelow` controlla che l'operatore
binario `op` è commutativo per valori nell'intervallo `0,...,n-1`.

Suggerimento: dato che `op` prende due argomenti, ti serviranno due usi di `allBelow`.
-/

def checkCommutativeBelow (op : Nat → Nat → Nat) (n : Nat) : Bool :=
  allBelow (fun a => allBelow (fun b => eqN (op a b) (op b a)) n) n

example : checkCommutativeBelow addN 20 = true      := by rfl
example : checkCommutativeBelow Nat.sub 20 = false  := by rfl

/-
__Exercise (difficoltà: 2/4)__ Dimostra che se un operatore è commutativo, allora
`checkCommutativeBelow` è vero per ogni `n`.

Suggerimento: applica `allBelow_of_forall`.
-/
example (op : Nat → Nat → Nat) (n : Nat) :
    (∀ a b : Nat, eqN (op a b) (op b a) = true) → checkCommutativeBelow op n = true := by
  intro h
  apply allBelow_of_forall
  intro a
  apply allBelow_of_forall
  intro b
  exact h a b

end Exercises_bounded_search



section Bank

/-
### Esercizio: Banca

Definiamo una `Bank` come una funzione da conti ai loro saldi (entrambi rappresentati come `Nat`).
Introduciamo poi operazioni per depositare e prelevare.
-/

def Bank := Nat → Nat   -- saldo di ogni conto (rappresentato come numeri naturali)

def emptyBank : Bank := fun _ => 0

def depositBank (a : Nat) (n : Nat) (b : Bank) : Bank :=
  fun x  => if x = a then b a + n else b x

example : depositBank 3 20 emptyBank 3 = 20 := by rfl
example : depositBank 3 20 emptyBank 4 = 0  := by rfl

/- __Exercise (difficoltà: 1/4)__ Dimostra che se un utente deposita `n`, allora
il suo saldo è aumentato esattamente di `n`. -/

theorem depositBank_same (a : Nat) (n : Nat) (b : Bank) :
    depositBank a n b a = b a + n := by
  simp [depositBank]

/- __Exercise (difficoltà: 1/4)__ Dimostra che se un utente deposita `n`, allora
il saldo di qualsiasi altro conto è preservato. -/

theorem depositBank_other
    (a x : Nat) (n : Nat) (b : Bank)
    (h : x ≠ a) :
    depositBank a n b x = b x := by
  simp [depositBank, h]

/- __Exercise (difficoltà: 1/4)__ Definisci un'operazione per prelevare dalla banca.
Se il conto non contiene fondi sufficienti, allora l'operazione non ha effetto. -/

def withdrawBank (a : Nat) (n : Nat) (b : Bank) : Bank :=
  fun x => if x = a then if b a ≥ n then b a - n else b a else b x

example : withdrawBank 3 20  (depositBank 3 100 emptyBank) 3 = 80  := by rfl
example : withdrawBank 3 120 (depositBank 3 100 emptyBank) 3 = 100 := by rfl

/- __Exercise (difficoltà: 2/4)__ Dimostra che due depositi sullo stesso conto
hanno lo stesso effetto di un singolo deposito della somma degli importi.

Suggerimento: Usa `funext` due volte: la prima volta sulla banca `b`, e la seconda
sul conto `x`.

La composizione di funzioni `∘` può essere riscritta tramite `rw [Function.comp_apply]`

Poi, usa la tattica `by_cases` per considerare separatamente i casi in cui
`x = a` e `x ≠ a`.

La tattica

    by_cases h : x = a

crea due goal:

* uno con `h : x = a`;
* uno con `h : x ≠ a`.

Questo è utile quando la definizione studiata contiene lo stesso test.
-/

theorem depositBank_additivity (a n1 n2 : Nat) : (depositBank a n2) ∘ (depositBank a n1) = depositBank a (n1 + n2) := by
  funext b
  funext x
  rw [Function.comp_apply]
  by_cases h : x = a
  · simp [depositBank, h]
  · simp [depositBank, h]


/- __Exercise (difficoltà: 4/4)__ Dimostra che due prelievi sullo stesso conto
hanno lo stesso effetto di un singolo prelievo della somma degli importi, purché
il conto abbia saldo iniziale sufficiente.

Suggerimento: Dimostra due lemmi ausiliari usando la tattica `have`:
  h1 : b a ≥ n1
  h2 : b a - n1 ≥ n2
Puoi dimostrarli con la tattica `omega`, una procedura di decisione per
l'aritmetica lineare.

Poi, usa la tattica `by_cases` per considerare separatamente i casi in cui
`x = a` e `x ≠ a`.

Per chiudere il primo caso, il teorema `Nat.sub_sub` può essere utile.
-/

theorem withdrawBank_additivity (a n1 n2 : Nat) (b : Bank) (h : b a ≥ n1 + n2) :
  (withdrawBank a n2) ((withdrawBank a n1) b) = withdrawBank a (n1 + n2) b := by
  funext x
  by_cases hx : x = a
  · subst hx
    have h1 : b a ≥ n1 := by omega
    have h2 : b a - n1 ≥ n2 := by omega
    simp [withdrawBank, h1, h2]
    omega
  · simp [withdrawBank, hx]

end Bank


section Closed_form_summations

/-
### Esercizio: Sommatorie in forma chiusa
-/


/-
__Exercise (difficoltà: 3/4)__ Dimostra che la somma dei primi `n` numeri dispari
è `n²`. Il valore iniziale all'indice zero contribuisce zero perché la sottrazione
sui `Nat` si ferma a zero.
-/

theorem sumOdd_closed (n : Nat) : sumBelow (λ n => 2 * n - 1) (n+1) = n * n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [sumBelow]
    rw [ih]
    omega


/-
__Exercise (difficoltà: 3/4)__ Dimostra la seguente formula in forma chiusa per
la sommatoria dei numeri.
-/

theorem sumId_closed (n : Nat) : 2 * (sumBelow (λ n => n)) (n+1) = (n+1) * n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [sumBelow]
    omega

end Closed_form_summations


end Exercises