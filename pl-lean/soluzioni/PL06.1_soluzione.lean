set_option autoImplicit false

/-
# Funzioni polimorfe

Nella lezione precedente abbiamo definito funzioni su tipi prodotto e somma concreti.
Ad esempio, abbiamo usato tipi come:

    Nat → Nat
    Nat ⊕ Bool → Bool ⊕ Nat
    (Nat × Nat → Nat) → (Nat → Nat → Nat)

Diverse di quelle definizioni non dipendevano davvero dai tipi particolari
`Nat` e `Bool`. Scambiare le componenti di una coppia, ad esempio, funziona allo
stesso modo indipendentemente dai tipi delle sue componenti.

In questa lezione studiamo come scrivere una singola definizione che funziona
uniformemente per molti tipi. Questa idea è chiamata **polimorfismo**.

La nostra applicazione principale sarà il tipo delle **liste**. Vedremo diversi
algoritmi sulle liste che sono naturalmente polimorfi, poiché non dipendono dai
tipi degli elementi della lista.

Alla fine della lezione dovresti essere in grado di:

* distinguere un parametro di tipo da un parametro di valore ordinario;
* leggere il tipo di una funzione polimorfa, come `(A : Type) → A → A`, e
  spiegare cosa promette;
* leggere e definire funzioni con parametri di tipo espliciti e impliciti;
* spiegare, informalmente, perché una funzione polimorfa deve trattare tutti i
  tipi uniformemente;
* capire perché Lean a volte mostra variabili di universo come `u`;
* costruire liste e ispezionarle tramite pattern matching;
* definire funzioni ricorsive e di ordine superiore sulle liste;
* dimostrare semplici proprietà delle liste per induzione.

Le difficoltà degli esercizi usano la stessa scala relativa delle lezioni precedenti:

* **1/4:** un'idea diretta;
* **2/4:** due idee devono essere combinate;
* **3/4:** una costruzione o dimostrazione più sostanziale;
* **4/4:** una sfida opzionale.

Trovi ulteriori esercizi estesi nel file `PL06_PolyEx.lean`.

-/


section Motivation

/-
## Perché il polimorfismo?

Considera le seguenti due funzioni identità:
-/

def identityNat (n : Nat) : Nat :=
  n

def identityBool (b : Bool) : Bool :=
  b

example : identityNat 5 = 5 := by rfl
example : identityBool true = true := by rfl

/-
Le loro implementazioni sono identiche. Solo i loro tipi sono diversi.
Duplicare la definizione per ogni possibile tipo sarebbe noioso
(e non potremmo mai scrivere tutte le definizioni, poiché ci sono infiniti tipi).

Lean permette a una funzione di ricevere un **tipo** come argomento. Questo è
possibile perché, in Lean, i tipi sono termini ordinari: `Nat` è un termine
proprio come `5`, così come `Type`, cioè il "tipo dei tipi".

Nella seguente definizione, `A` è un **parametro di tipo**, mentre `x` è un
ordinario **parametro di valore**:
-/

def identityExplicit (A : Type) (x : A) : A :=
  x

#check identityExplicit
#check (identityExplicit)   -- parentesi: stampa il tipo come tipo freccia
#check identityExplicit Nat
#check identityExplicit Bool

example : identityExplicit Nat 5 = 5 := by rfl
example : identityExplicit Bool true := by rfl

/-
Guardiamo attentamente cosa ci dice Lean.

La funzione `identityExplicit` ha *due* parametri:

* `A : Type` è un parametro di tipo: il suo valore è un tipo come `Nat`;
* `x : A` è un parametro di valore: il *tipo* di `x` è dato dal primo parametro.

L'ordine conta: la dichiarazione di `x` menziona `A`, quindi `A` deve essere
dichiarato prima. In generale, il tipo di un parametro e il tipo di risultato
possono dipendere dai parametri che vengono prima.

Di conseguenza, il *tipo* di `identityExplicit` è

    (A : Type) → A → A

Questo è chiamato **tipo di funzione dipendente**: il nome `A` legato davanti
alla prima freccia è *usato* nel resto del tipo. Leggilo come

    "per ogni tipo A, una funzione da A a A".

Lean accetta anche la notazione `∀ A : Type, A → A` per lo stesso tipo.
Quando il tipo di risultato *non* menziona l'argomento, otteniamo la freccia
ordinaria: `A → B` è solo un'abbreviazione per `(_ : A) → B`.

Qual è il tipo di un'applicazione a un tipo? Lean **sostituisce** l'argomento
al nome legato nel resto del tipo:

    identityExplicit Nat  : Nat → Nat       -- sostituisci A con Nat in A → A
    identityExplicit Bool : Bool → Bool     -- sostituisci A con Bool in A → A

Quindi, `identityExplicit` descrive una famiglia di funzioni identità, una per
ogni possibile scelta di `A`.

Tecnicamente, Lean rappresenta questa forma di polimorfismo usando il tipo di
funzione dipendente descritto sopra. Non abbiamo bisogno della teoria generale
dei tipi dipendenti per definire e usare funzioni polimorfe.
-/


/-
__Checkpoint 1__  Senza eseguire nulla, scrivi i tipi delle seguenti tre
espressioni, poi posiziona il cursore su ogni `#check` e confronta.

Poi, decidi quale delle tre righe commentate Lean rifiuterebbe, e *perché*.
Rimuovi il marcatore di commento per verificare la tua ipotesi.
-/

#check identityExplicit Nat 5
#check identityExplicit Bool
#check identityExplicit (List Nat)

-- #check identityExplicit Nat true    -- RIFIUTATO: true è Bool, ma Nat si aspetta un Nat
-- #check identityExplicit Bool true   -- ACCETTATO: Bool → Bool applicato a true
-- #check identityExplicit 5 Nat       -- RIFIUTATO: 5 non è un Type


/- __Exercise (difficoltà: 1/4)__ Definisci una funzione che, dato un valore `x`
di un tipo arbitrario, restituisce una coppia con `x` sia a sinistra che a destra.
Il parametro di tipo è esplicito per il momento.
-/

def duplicateExplicit (A : Type) (x : A) : A × A :=
  (x, x)

example : duplicateExplicit Nat 4 = (4, 4) := by rfl
example : duplicateExplicit Bool false = (false, false) := by rfl

end Motivation



section Implicit_parameters

/-
## Parametri di tipo impliciti

In un'applicazione come

    identityExplicit Nat 5

l'argomento `5` dice già a Lean che il tipo rilevante è `Nat`.
Scrivere `Nat` esplicitamente è quindi ridondante.

I parametri scritti tra parentesi graffe `{...}` sono **impliciti**.
Lean cerca di inferire i loro valori dall'espressione circostante.
-/

def identityImplicit {A : Type} (x : A) : A :=
  x

#check identityImplicit
#check @identityImplicit

#eval identityImplicit 5
#eval identityImplicit true

example : identityImplicit 12 = 12 := by rfl
example : identityImplicit "Ciao" = "Ciao" := by rfl

/-
In `identityImplicit 5`, Lean vede che `5 : Nat` e inferisce `A := Nat`.
Similmente, inferisce `A := Bool` in `identityImplicit true`.

L'argomento implicito non è scomparso. Il simbolo `@` chiede a Lean di mostrare
e accettare gli argomenti impliciti esplicitamente:
-/

#eval @identityImplicit Nat 5
#eval @identityImplicit Bool true

/-
Confronta le due applicazioni:

    identityImplicit 5       -- Lean inferisce l'argomento di tipo
    @identityImplicit Nat 5  -- forniamo l'argomento di tipo esplicitamente

Gli argomenti impliciti sono una comodità fornita dall'elaboratore di Lean (la
parte di Lean che trasforma ciò che scrivi in un'espressione completamente
esplicita). Non cambiano il significato della funzione. In particolare, le
parentesi graffe non sono ciò che rende la definizione polimorfa:
`identityExplicit` era già polimorfa. Le parentesi graffe permettono solo a Lean
di omettere e ricostruire l'argomento di tipo.

(Perché abbiamo impostato `autoImplicit false` all'inizio del file? Senza questa
opzione, Lean tratterebbe silenziosamente un nome sconosciuto come `A` in una
firma come un parametro implicito. Questo è comodo per gli esperti, ma nasconde
esattamente la cosa che vogliamo vedere in questa lezione: ogni parametro di tipo
dovrebbe essere visibile nella firma.)
-/


/-
__Checkpoint 2__  Quali delle seguenti quattro righe Lean accetta?
Decidi prima, poi rimuovi i marcatori di commento uno alla volta.

Sotto, `emptyList` ha un parametro implicito ma *nessun* parametro di valore.
Come può Lean trovare `A`?
-/

-- #check identityImplicit 5          -- ACCETTATO
-- #check identityImplicit Nat 5      -- RIFIUTATO: Nat è un tipo, non un valore; 5 come x
-- #check @identityImplicit Nat 5     -- ACCETTATO
-- #check @identityImplicit 5         -- RIFIUTATO: manca l'argomento di tipo

def emptyList {A : Type} : List A :=
  []

#check (emptyList : List Nat)
#check (emptyList : List Bool)

-- #eval emptyList      -- errore: Lean non può inferire A


/- __Exercise (difficoltà: 1/4)__ Riscrivi `duplicateExplicit` usando un
parametro di tipo implicito. -/

def duplicate {A : Type} (x : A) : A × A :=
  (x, x)

example : duplicate 4 = (4, 4) := by rfl
example : duplicate false = (false, false) := by rfl


/-
### Astrazione di tipo e applicazione di tipo

Le funzioni in Lean sono create con `fun`. Una funzione polimorfa è creata
esattamente allo stesso modo; il suo primo parametro è solo un tipo:
-/

#check fun (A : Type) (x : A) => x

example : identityExplicit = fun (A : Type) (x : A) => x := by rfl

/-
Quindi in Lean:

* **astrazione di tipo** ("questa funzione funziona per ogni tipo A") è un
  ordinario `fun` il cui parametro ha tipo `Type`;
* **applicazione di tipo** ("usala al tipo `Nat`") è un'ordinaria applicazione
  di funzione, come in `identityExplicit Nat`.

Non c'è macchinario separato per il polimorfismo. Gli argomenti impliciti
decidono solo *chi scrive* l'applicazione di tipo: tu (`@identityImplicit Nat 5`)
o l'elaboratore (`identityImplicit 5`).
-/


/-
__Checkpoint 3__  Prevedi quali dei seguenti tipi sono legittimi.
-/

-- #check @duplicate Nat 4        -- ACCETTATO: (Nat × Nat)
-- #check @duplicate 4            -- RIFIUTATO: manca il tipo
-- #check duplicate 4             -- ACCETTATO: (Nat × Nat)
-- #check (duplicate 4).1 + 1     -- ACCETTATO: Nat
-- #check (duplicate 4) + 1       -- RIFIUTATO: una coppia non si può sommare


end Implicit_parameters



/-
## Una breve nota sugli universi

Abbiamo appena detto che `Type` è "il tipo dei tipi". Ma `Type` stesso è un
termine, quindi deve avere un tipo anche lui. Chiediamolo a Lean:
-/

#check Nat
#check Type
#check Type 1

/-
Non può esserci un singolo tipo di tutti i tipi che soddisfi

    Type : Type

perché questo renderebbe la logica di Lean inconsistente (questo è noto come
paradosso di Girard, un cugino del paradosso di Russell). Lean organizza invece
i tipi in una gerarchia di **universi**:

    Type 0 : Type 1
    Type 1 : Type 2
    Type 2 : Type 3
    ...

`Nat`, `Bool` e `String` appartengono a `Type 0`. Quando scriviamo semplicemente
`Type`, intendiamo `Type 0`.
-/

/-
__Checkpoint 4__  In quale universo ti aspetti che viva ciascuno dei seguenti?
(`List` è una *funzione* da tipi a tipi; la studiamo sotto.)
-/

#check Type → Type
#check (A : Type) → A → A
#check List
#check List Nat

/-
Sorprendentemente, il tipo della funzione identità non è in `Type 0`.
Poiché quantifica su tutti i tipi in `Type`, è "troppo grande" per essere uno di essi.
-/

/-
Possiamo dichiarare nomi per livelli di universo arbitrari:
-/

universe u v w

/-
La seguente è la versione universo-polimorfa della funzione identità:
-/

def identityU {A : Type u} (x : A) : A :=
  x

#check @identityU

/-
La definizione funziona per un tipo `A` in qualsiasi universo `u`.
Lean normalmente inferisce sia `u` che `A`, quindi usare la funzione rimane semplice:
-/

example : identityU 7 = 7 := by rfl
example : identityU true = true := by rfl

example : identityU Nat = Nat := by rfl    -- non potevamo farlo con `identityImplicit`
example : identityU (Nat × Bool) = (Nat × Bool) := by rfl

/-
Per il resto della lezione, ometteremo gli universi nelle definizioni polimorfe.
Questo ha uno svantaggio, in quanto queste funzioni sono meno generali di quanto
potrebbero essere, ma ha il vantaggio di rendere le nostre definizioni più facili
da leggere.
-/

section Polymorphic_functions


/-
## Funzioni polimorfe su tipi familiari

Generalizziamo ora alcune funzioni della lezione precedente.
-/

def firstP {A : Type} {B : Type} (p : A × B) : A :=
  p.1

def secondP {A : Type} {B : Type} (p : A × B) : B :=
  p.2

def swapP {A : Type} {B : Type} (p : A × B) : B × A :=
  (p.2, p.1)

example : firstP (3, true) = 3 := by rfl
example : secondP (3, true) = true := by rfl
example : swapP (3, true) = (true, 3) := by rfl
example : swapP ("Lean", 4) = (4, "Lean") := by rfl

/-
Nota che `swapP` ha due parametri di tipo, poiché le due componenti possono
avere tipi diversi. La sua implementazione non ha comunque bisogno di sapere
quali siano.
-/


/- __Exercise (difficoltà: 1/4)__ Definisci una funzione polimorfa che sostituisce
la prima componente di una coppia preservando la seconda. Nota che la nuova prima
componente può avere un tipo *diverso* da quella vecchia, motivo per cui la firma
ha tre parametri di tipo. -/

def replaceFirst {A : Type} {B : Type} {C : Type w}
    (newFirst : C) (p : A × B) : C × B :=
  (newFirst, p.2)

example : replaceFirst false (3, "hello") = (false, "hello") := by rfl


/-
### Funzioni polimorfe su `Option`

`Option A` rappresenta o un valore di tipo `A` o nessun valore.
Le definizioni di `Option` e dei suoi costruttori sono polimorfe:

    none   : Option A
    some x : Option A       se x : A
-/

def getOrElseP {A : Type} (o : Option A) (fallback : A) : A :=
  match o with
  | none   => fallback
  | some x => x

example : getOrElseP (some 7) 0 = 7 := by rfl
example : getOrElseP none 0 = 0 := by rfl
example : getOrElseP (some "Ciao") "unknown" = "Ciao" := by rfl


/- __Exercise (difficoltà: 1/4)__ Definisci `mapOptionP`. Se l'option contiene
un elemento di tipo `A`, applica `f` per ottenere un `B`. Preserva `none`. -/

def mapOptionP {A : Type} {B : Type}
    (f : A → B) (o : Option A) : Option B :=
  match o with
  | none   => none
  | some x => some (f x)

example : mapOptionP Nat.succ (some 4) = some 5 := by rfl
example : mapOptionP Nat.succ none = none := by rfl


/- __Exercise (difficoltà: 1/4)__ Dimostra che scambiare due volte una coppia
polimorfa restituisce la coppia originale. -/

theorem swapP_twice {A : Type} {B : Type} (p : A × B) :
    swapP (swapP p) = p := by
  rcases p with ⟨a, b⟩
  rfl


/- __Exercise (difficoltà: 1/4)__ Dimostra che mappare la funzione identità su
un'option la lascia invariata. -/

#check identityImplicit

theorem mapOptionP_identity {A : Type} (o : Option A) :
    mapOptionP (fun x => x) o = o := by
  cases o with
  | none => rfl
  | some x => rfl


/-
### Comportamento uniforme (parametricità)

Una funzione con tipo

    {A : Type} → A → A

deve funzionare per ogni possibile `A`. Non può assumere che il suo argomento sia
un numero naturale, un booleano o una stringa. In particolare, non può sommare
il suo argomento, negarlo o ispezionarne i costruttori.

Lean lo impone. La seguente definizione è *rifiutata*:

    def bad {A : Type} (x : A) : A := 0

Lean cerca un modo per scrivere `0` come valore del tipo sconosciuto `A`, e
riporta che non riesce a trovarne uno (fallisce nel sintetizzare `OfNat A 0`).

Senza ricevere operazioni aggiuntive, l'unico valore di tipo `A` disponibile alla
funzione è il suo argomento. Questa uniformità è l'idea intuitiva dietro il
**polimorfismo parametrico**. È una *restrizione* su ciò che la funzione può fare,
e allo stesso tempo una *garanzia* per chi la usa: dal solo tipo impariamo molto
sulla funzione.
-/


/-
__Checkpoint 5__  Il tipo `{A : Type} → A → A → A` ha (almeno) due abitanti che
si comportano diversamente. Definiscili.
-/

def pickFirst {A : Type} (x y : A) : A :=
  x

def pickSecond {A : Type} (x y : A) : A :=
  y

example : pickFirst 10 20 = 10      := by rfl
example : pickSecond 10 20 = 20     := by rfl
example : pickFirst "a" "b" = "a"   := by rfl
example : pickSecond "a" "b" = "b"  := by rfl

/-
__Checkpoint 6__  Definisci funzioni (totali, terminanti) con i tipi dati.
-/

example : {A : Type} → A → A          := fun x => x

-- Definisci due funzioni diverse con il tipo dato
example : {A : Type} → A → Option A   := fun x => some x
example : {A : Type} → A → Option A   := fun _ => none

-- Definisci due funzioni diverse con il tipo dato
example : {A : Type} → A → Bool       := fun _ => true
example : {A : Type} → A → Bool       := fun _ => false

/-
Nota quanto ci dice il solo tipo! Questo fenomeno è chiamato **parametricità**;
vedremo una conseguenza concreta per le liste più avanti (il teorema
`mapL_reverseL`).
-/


end Polymorphic_functions



section Lists

/-
## Liste polimorfe

Una lista contiene zero o più valori dello **stesso** tipo.
Il tipo lista di Lean è polimorfo:
-/

#check List
#check List Nat
#check List (Nat × Bool)

/-
`List` da solo è un **costruttore di tipo**: deve essere applicato a un tipo.
Ad esempio, applicare `List` a `Nat` produce il tipo `List Nat`;
In termini delle sezioni precedenti: `List` è una funzione di tipo `Type u → Type u`,
e `List Nat` è il risultato della sua applicazione.

Concettualmente, il tipo lista integrato di Lean ha la seguente definizione:

    inductive List (A : Type u) where
      | nil  : List A
      | cons : A → List A → List A

Non ripetiamo questa dichiarazione sotto poiché `List` è già definito da Lean.

Una lista ha quindi due possibili forme (usando la notazione di Lean):

* `[]`, la lista vuota;
* `x :: xs`, una lista non vuota con testa `x` e coda `xs`.

La notazione `[a, b, c]` abbrevia:

    a :: b :: c :: []
-/

def numbers : List Nat :=
  [1, 2, 3, 4]

def truthValues : List Bool :=
  [true, false, true]

def labelledNumbers : List (String × Nat) :=
  [("zero", 0), ("one", 1), ("two", 2)]

example : [1, 2, 3] = 1 :: 2 :: 3 :: [] := by rfl

/-
Il seguente non sarebbe accettato perché tutti gli elementi devono avere lo stesso tipo:

    def badList := [1, true]       -- errore di tipo

La ragione è visibile nel tipo `List A`: c'è solo *un* `A`, scelto una volta per
tutta la lista. Se abbiamo davvero bisogno di mescolare due tipi di elementi,
usiamo una lista su un tipo somma della lezione precedente:
-/

def mixedList : List (Nat ⊕ Bool) :=
  [Sum.inl 1, Sum.inr true]


/-
__Checkpoint 7__

I costruttori di `List` sono essi stessi funzioni polimorfe. Prevedi i tipi delle
seguenti espressioni, e quali saranno rifiutate.
-/

-- #check [1,2,3]                              -- List Nat
-- #check [[1],[2],[3]]                        -- List (List Nat)
-- #check [[1],2,[3]]                          -- RIFIUTATO: mescola List Nat e Nat
-- #check [some 1,none,some 3]                 -- List (Option Nat)
-- #check [some 1,none,some false]             -- RIFIUTATO: mescola Option Nat e Option Bool
-- #check [Sum.inl 10, Sum.inr true, Sum.inl 20] -- List (Nat ⊕ Bool)
-- #check [Sum.inl 10, Sum.inr 20]             -- List (Nat ⊕ Nat)
-- #check [Sum.inl 10, Sum.inl true]           -- RIFIUTATO: inl si aspetta un tipo coerente



section Pattern_matching_on_lists

/-
## Pattern matching sulle liste

Poiché una lista ha due costruttori, un pattern match completo ha normalmente due rami:
uno per `[]` e uno per `x :: xs`.
-/

def headOptionL {A : Type} (xs : List A) : Option A :=
  match xs with
  | []     => none
  | x :: _ => some x

example : headOptionL ([10, 20, 30] : List Nat) = some 10 := by rfl
example : headOptionL ([] : List Nat) = none := by rfl

/-
Il risultato è un `Option A` perché una lista vuota non ha primo elemento.
Usare `Option` rende questa possibilità esplicita nel tipo di ritorno.
Vedremo nel Checkpoint 9 che, a causa della parametricità, non c'è alternativa:
una funzione `List A → A` non può esistere.
-/


/- __Exercise (difficoltà: 1/4)__ Definisci una funzione che rimuove il primo
elemento di una lista. La coda della lista vuota è ancora la lista vuota. -/

def tailL {A : Type} (xs : List A) : List A :=
  match xs with
  | []     => []
  | _ :: xs => xs

example : tailL ([10, 20, 30] : List Nat) = [20, 30] := by rfl
example : tailL ([] : List Nat) = [] := by rfl


/- __Exercise (difficoltà: 1/4)__ Verifica se una lista è vuota. -/

def isEmptyL {A : Type} (xs : List A) : Bool :=
  match xs with
  | []     => true
  | _ :: _ => false

example : isEmptyL ([] : List Bool) = true  := by rfl
example : isEmptyL [true, false] = false    := by rfl

/-
__Exercise (difficoltà: 2/4)__ Dimostra che una lista `l` è vuota se e solo se
`headOptionL l` restituisce `none`. Non serve induzione.
-/

theorem empty_no_head (A : Type) (l : List A) :
  isEmptyL l = true ↔ headOptionL l = none := by
  constructor
  · intro h
    cases l with
    | nil => rfl
    | cons x xs => simp [isEmptyL] at h
  · intro h
    cases l with
    | nil => rfl
    | cons x xs => simp [headOptionL] at h


/- __Exercise__ Formalizza e dimostra un teorema che afferma che la coda di una
lista `l` è vuota ogniqualvolta `l` è vuota (usa le funzioni `isEmptyL` e `tailL`
date prima).
-/

theorem empty_tail_empty (A : Type) (l : List A) :
    isEmptyL l = true → isEmptyL (tailL l) = true := by
  intro h
  cases l with
  | nil => rfl
  | cons x xs => simp [isEmptyL] at h

end Pattern_matching_on_lists



section Recursive_list_functions

/-
## Ricorsione strutturale sulle liste

Come per i numeri naturali, il pattern matching può essere combinato con la ricorsione.
Nel caso non vuoto, una funzione strutturalmente ricorsiva chiama se stessa sulla
coda `xs`, che è strutturalmente più piccola di `x :: xs`.

La lunghezza non dipende dai valori memorizzati nella lista, quindi la testa è
corrisposta da un wildcard.
-/

def lengthL {A : Type} : List A → Nat
  | []      => 0
  | _ :: xs => 1 + lengthL xs

example : lengthL ([10, 20, 30] : List Nat) = 3 := by rfl
example : lengthL ([] : List Bool) = 0 := by rfl

/-
La stessa definizione funziona per liste in ogni tipo di elemento perché non
ispeziona mai un elemento. Guarda il tipo: `A` compare solo nell'*argomento*,
non nel risultato, quindi il risultato non può contenere alcun elemento della lista.
-/


/- __Exercise (difficoltà: 1/4)__ Definisci la somma di una lista di numeri naturali.
Questa funzione *non* è polimorfa perché l'operazione di addizione è specifica per `Nat`.
-/

def sumL : List Nat → Nat
  | []      => 0
  | x :: xs => x + sumL xs

example : sumL [2, 3, 4] = 9 := by rfl

/-
La prossima funzione unisce due liste. Attraversa ricorsivamente la prima lista
e pone ciascuno dei suoi elementi davanti alla seconda lista.
-/

def appendL {A : Type} : List A → List A → List A
  | [],      ys => ys
  | x :: xs, ys => x :: appendL xs ys

example : appendL [1, 2] [3, 4] = [1, 2, 3, 4] := by rfl
example : appendL ([] : List Nat) [3, 4] = [3, 4] := by rfl


/-
__Checkpoint 8__ Calcola `appendL [1,2] [3]` a mano.
Scrivi ogni passo in un commento, srotolando esattamente un'equazione di `appendL`
alla volta, e indica quale equazione hai usato e quali valori sono usati per le
variabili x, xs e ys.

    appendL (1 :: 2 :: []) (3 :: [])
  = 1 :: appendL (2 :: []) (3 :: [])     -- eqn 2, con x = 1, xs = [2], ys = [3]
  = 1 :: 2 :: appendL ([] : List Nat) [3] -- eqn 2, con x = 2, xs = [], ys = [3]
  = 1 :: 2 :: [3]                         -- eqn 1, con ys = [3]
  = [1, 2, 3]
-/


/- __Exercise (difficoltà: 1/4)__ Definisci `replicateL n x`, che costruisce una
lista contenente `n` copie di `x`. -/

def replicateL {A : Type} : Nat → A → List A
  | 0,     _ => []
  | n + 1, x => x :: replicateL n x

example : replicateL 4 true = [true, true, true, true] := by rfl
example : replicateL 0 "Ciao" = [] := by rfl


/- __Exercise (difficoltà: 2/4)__ Restituisci l'ultimo elemento di una lista, se
esiste. Nota che la chiamata ricorsiva è fatta sulla coda non vuota. -/

def lastOptionL {A : Type u} : List A → Option A
  | []      => none
  | [x]     => some x
  | _ :: xs => lastOptionL xs

example : lastOptionL ([10, 20, 30] : List Nat) = some 30 := by rfl
example : lastOptionL ([] : List Nat) = none := by rfl


/-
__Checkpoint 9__  Definisci funzioni con i tipi dati, ogniqualvolta esistono.
-/

example : {A : Type} → List A → List A := fun xs => xs
example : {A B : Type} → List A → List B := fun _ => []
example : {A : Type} → List A → Nat := fun xs => lengthL xs
-- example : {A : Type} → List A → A := sorry  -- IMPOSSIBILE per parametricità!

end Recursive_list_functions



section Higher_order_list_functions

/-
## Funzioni di ordine superiore sulle liste

Polimorfismo e funzioni di ordine superiore sono particolarmente utili insieme.
Ricorda che una funzione di ordine superiore riceve o restituisce un'altra funzione.

La funzione `mapL` riceve una trasformazione `f : A → B` e la applica a ogni
elemento di una lista:
-/

def mapL {A B : Type} (f : A → B) : List A → List B
  | []      => []
  | x :: xs => f x :: mapL f xs

example : mapL Nat.succ [1, 2, 3] = [2, 3, 4] := by rfl
example : mapL (fun b : Bool => !b) [true, false, true] = [false, true, false] := by rfl

/-
Leggi attentamente il suo tipo:

    mapL : (A → B) → List A → List B

La funzione può cambiare il tipo degli elementi. Ad esempio:
-/

example : mapL (fun n => if n > 2 then true else false) [1, 2, 3] = [false, false, true] := by rfl

/-
Possiamo ottenere lo stesso effetto dell'ultima `mapL` più succintamente usando `decide`.
-/

example : mapL (fun n => decide (n > 2)) [1, 2, 3] = [false, false, true] := by rfl

/-
__Checkpoint 10__  Scrivi i tipi di queste applicazioni parziali.
-/

#check mapL Nat.succ
#check mapL (fun n : Nat => decide (n > 2))
#check mapL (fun b : Bool => !b)


/- __Exercise (difficoltà: 1/4)__ Definisci `filterL`. Preserva esattamente gli
elementi per cui il predicato booleano `p` restituisce `true`. -/

def filterL {A : Type u}
    (p : A → Bool) : List A → List A
  | []      => []
  | x :: xs => if p x then x :: filterL p xs else filterL p xs

example : filterL (fun n : Nat => decide (n > 2)) [1, 2, 3, 4] = [3, 4] := by rfl


/- __Exercise (difficoltà: 1/4)__ Definisci `allL` e `anyL`.

* `allL p xs` è vero quando `p` è vero per *tutti* gli elementi di `xs`;
* `anyL p xs` è vero quando `p` è vero per *almeno un* elemento di `xs`.

Pensa attentamente ai risultati per la lista vuota.
-/

def allL {A : Type u} (p : A → Bool) : List A → Bool
  | []      => true
  | x :: xs => p x && allL p xs

def anyL {A : Type u} (p : A → Bool) : List A → Bool
  | []      => false
  | x :: xs => p x || anyL p xs

example : allL (fun n : Nat => decide (n > 0)) [1, 2, 3] = true   := by rfl
example : allL (fun n : Nat => decide (n > 0)) [1, 0, 3] = false  := by rfl
example : allL (fun n : Nat => decide (n > 0)) [] = true          := by rfl
example : anyL (fun n : Nat => decide (n > 5)) [1, 8, 3] = true   := by rfl
example : anyL (fun n : Nat => decide (n > 5)) [1, 2, 3] = false  := by rfl
example : anyL (fun n : Nat => decide (n > 5)) [] = false         := by rfl


/- __Exercise (difficoltà: 1/4)__ Conta gli elementi che soddisfano un predicato. -/

def countIfL {A : Type u} (p : A → Bool) : List A → Nat
  | []      => 0
  | x :: xs => if p x then 1 + countIfL p xs else countIfL p xs

example : countIfL (fun n : Nat => decide (n > 2)) [1, 3, 2, 4, 5] = 3 := by rfl



section Equality_as_an_argument

/-
### Quando una funzione polimorfa ha bisogno di un'operazione aggiuntiva

È facile definire un test di appartenenza specificamente per i numeri naturali:
-/

def containsN (target : Nat) : List Nat → Bool
  | []      => false
  | x :: xs => (x == target) || containsN target xs

example : containsN 3 [1, 2, 3, 4] = true := by rfl
example : containsN 8 [1, 2, 3, 4] = false := by rfl

/-
Possiamo semplicemente sostituire `Nat` con un tipo arbitrario `A`? La struttura
ricorsiva funzionerebbe ancora, ma Lean non saprebbe come confrontare due valori
arbitrari di tipo `A`.
-/


/-
__Checkpoint 11__  Perché la seguente definizione fallisce? Cosa dice il
messaggio di errore, e come si relaziona al Checkpoint 6?
Come puoi risolvere il problema?

    def containsBad {A : Type} (target : A) : List A → Bool
      | []      => false
      | x :: xs => (x == target) || containsBad target xs
-/

/-
Lean riporta che non riesce a sintetizzare un'istanza di `BEq A`: non conosce
alcun modo per confrontare due valori del tipo arbitrario `A` per uguaglianza.
Questo è esattamente il fenomeno della sezione precedente: una funzione polimorfa
non può usare alcuna operazione su `A` a meno che quell'operazione non sia *fornita*.
-/

/-
Una soluzione è ricevere il test di uguaglianza come argomento esplicito aggiuntivo:
-/

def containsBy {A : Type}
    (equal : A → A → Bool) (target : A) : List A → Bool
  | []      => false
  | x :: xs => equal x target || containsBy equal target xs

example : containsBy (fun a b : Nat => a == b) 3 [1, 2, 3, 4] = true := by rfl
example : containsBy (fun a b : String => a == b) "Ciao" ["Hi", "Ciao"] = true := by rfl

/-
L'implementazione è ancora uniforme: non sa come i valori di tipo `A` sono
rappresentati. Tutto il lavoro specifico del tipo è svolto dall'argomento `equal`.

Il tipo di `containsBy` dice tutto: per ogni `A`, *dato* un modo per confrontare
due `A`, possiamo cercare in una lista di `A`. La parametricità non è violata;
la funzione usa semplicemente un'operazione che fa parte della sua stessa firma.
-/

/-
Scrivere la funzione di confronto a mano ad ogni chiamata è noioso.
Una soluzione più elegante è usare le **classi di tipo** di Lean.
-/

def containsB {A : Type u} [BEq A] (target : A) : List A → Bool
  | []      => false
  | x :: xs => (x == target) || containsB target xs

example : containsB 3 [1, 2, 3, 4] = true := by rfl
example : containsB 8 [1, 2, 3, 4] = false := by rfl

/-
Il parametro `[BEq A]` è un argomento implicito: Lean cerca un'istanza registrata
della classe di tipo `BEq` per il tipo `A`.
Questo è come Lean fornisce l'overloading (*polimorfismo ad hoc*).
Non sono necessari ulteriori dettagli per ora: pensa a `[BEq A]` come
"`A` deve venire con un test di uguaglianza".
-/

end Equality_as_an_argument

end Higher_order_list_functions



section Induction_on_lists

/-
## Dimostrazioni per induzione sulle liste

Le liste sono valori induttivi, quindi le loro proprietà sono comunemente
dimostrate per induzione. Confronta le forme dei numeri naturali e delle liste:

    Nat                         List A
    --------------------        --------------------------
    0     (Nat.zero)            []        (List.nil)
    n+1   (Nat.succ n)          x :: xs   (List.cons x xs)

L'induzione su una lista produce quindi due casi:

* il caso base `[]`;
* il caso induttivo `x :: xs`, con un'ipotesi induttiva su `xs`.

Iniziamo con una proprietà che vale per calcolo.
-/

theorem appendL_nil_left {A : Type} (xs : List A) :
    appendL [] xs = xs := by
  rfl

/-
__Checkpoint 12__  Prevedi se il teorema simmetrico può essere dimostrato con `rfl`.
Pensa prima di decommentare:

-- example {A : Type} (xs : List A) : appendL xs [] = xs := by rfl
-- NO: serve induzione perché `appendL` ricorre sulla prima lista.
-/

/-
Possiamo dimostrare `appendL_nil_right` per induzione sulla struttura della lista.
-/

theorem appendL_nil_right {A : Type} (xs : List A) :
    appendL xs [] = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>   -- ih è l'ipotesi induttiva
      rw [appendL]    -- controlla il contesto nella InfoView
      rw [ih]


/- __Exercise (difficoltà: 2/4)__ Dimostra che l'append di liste è associativo. -/

theorem appendL_associative {A : Type} (xs ys zs : List A) :
    appendL (appendL xs ys) zs = appendL xs (appendL ys zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [appendL]
    rw [appendL]
    rw [appendL]
    rw [ih]


/- __Exercise (difficoltà: 2/4)__ Dimostra che la lunghezza di un append è la
somma delle due lunghezze. -/

theorem lengthL_appendL {A : Type} (xs ys : List A) :
    lengthL (appendL xs ys) = lengthL xs + lengthL ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [appendL]
    rw [lengthL]
    rw [lengthL]
    rw [ih]
    omega


end Induction_on_lists



section Folding_lists

/-
## Folding di una lista

Le funzioni ricorsive `sumL`, `mapL` e molte altre condividono lo stesso pattern
di attraversamento. I combinatori **fold** catturano questo pattern generale.

Prendono tre argomenti:
* una funzione `f`,
* un valore `init`, e
* una lista `l`.
Poi, combinano gli elementi di `l` usando la funzione `f`;
il valore `init` è usato come inizializzatore. L'ordine in cui gli elementi sono
combinati dipende dalla direzione del fold, cioè "destra" o "sinistra".

Il comportamento di `foldRightL f init` è informalmente definito come:

    foldRightL f init [] = init
    foldRightL f init [x₁] = f x₁ init
    foldRightL f init [x₁, x₂] = f x₁ (f x₂ init)
    foldRightL f init [x₁, x₂, x₃] = f x₁ (f x₂ (f x₃ init))
    ...
-/

def foldRightL {A : Type} {B : Type} (f : A → B → B) (init : B) : List A → B
  | []      => init
  | x :: xs => f x (foldRightL f init xs)


/-
Usiamo il nuovo combinatore per definire una funzione `sumFold` che somma tutti
gli elementi di una lista. In questo caso, l'elemento init è 0, mentre la funzione
di combinazione è l'operatore di addizione `Nat.add`.

Secondo la nostra definizione informale, abbiamo:
foldRightL Nat.add 0 [] = 0
foldRightL Nat.add 0 [x₁] = Nat.add x₁ 0 = x₁ + 0 = x₁
foldRightL Nat.add 0 [x₁, x₂] = Nat.add x₁ (Nat.add x₂ 0) = x₁ + (x₂ + 0) = x₁ + x₂
-/

def sumFold : List Nat → Nat :=
  foldRightL Nat.add 0          -- Nat.add := fun x acc => x + acc

example : sumFold [1, 2, 3, 4] = 10 := by rfl


/-
Ora usiamo `foldRightL` per ridefinire il combinatore map.
-/

def mapFold {A : Type} {B : Type} (f : A → B) (xs : List A) : List B :=
  foldRightL (fun x accumulator => f x :: accumulator) [] xs

example : mapFold Nat.succ [1, 2, 3] = [2, 3, 4] := by rfl


/-
__Checkpoint 13__  `foldRightL` ha *due* parametri di tipo: `A` per gli elementi
della lista e `B` per il risultato accumulato. Prevedi i tipi delle seguenti tre
espressioni. In quale di esse `A` e `B` sono diversi?
-/

#check @foldRightL
#check foldRightL (fun (x : Nat) (acc : Nat) => x + acc) 0
#check foldRightL (fun (x : Nat) (acc : Bool) => acc && decide (x > 0)) true
-- A = Nat, B = Bool: diversi!

/-
__Checkpoint 14__  Definisci la lunghezza di una lista usando `foldRightL`. Gli
elementi non sono mai ispezionati, quindi `A` può essere qualsiasi cosa, mentre
l'accumulatore ha tipo `Nat`.
-/

def lengthFold {A : Type} (xs : List A) : Nat :=
  foldRightL (fun _ acc => acc + 1) 0 xs

example : lengthFold ["a", "b", "c"] = 3  := by rfl
example : lengthFold ([] : List Bool) = 0 := by rfl

end Folding_lists



section Pipe_operator

/-
## L'operatore pipe

Ricorda che l'applicazione di funzione associa a sinistra: `f g x` significa
`(f g) x`, non `f (g x)`. Per applicare una funzione al *risultato* di un'altra
chiamata dobbiamo aggiungere parentesi. Ad esempio, supponiamo di voler calcolare
2·(3²)² usando le funzioni `squareN` e `doubleN`:
-/

def doubleN (n : Nat) : Nat := n + n
def squareN (n : Nat) : Nat := n * n

example : doubleN (squareN (squareN 3)) = 162 := by rfl

/-
Nota che man mano che l'espressione diventa più complessa, aggiungere le parentesi
necessarie diventa sempre più soggetto a errori, e l'espressione diventa sempre
meno leggibile.

Lean offre due notazioni che evitano queste parentesi.

La prima è `f <| x`, che significa esattamente `f x`, ma ha una precedenza molto
bassa e associa a destra. Quindi la seguente significa `doubleN (squareN (squareN 3))`:
-/

example : (doubleN <| squareN <| squareN <| 3) = 162 := by rfl

/-
La seconda è l'**operatore pipe** `|>`. Scrive la stessa catena nell'ordine in cui
il calcolo avviene, da sinistra a destra, come una pipeline Unix:
-/

example : (3 |> squareN) = 9 := by rfl
example : (3 |> squareN |> squareN) = 81 := by rfl
example : (3 |> squareN |> squareN |> doubleN) = 162 := by rfl

/-
Come funziona? La notazione `x |> f` è un'abbreviazione per `f x`: Lean la
riscrive prima del type checking. L'operatore associa a sinistra, quindi
`x |> f |> g` significa `g (f x)`.

Per vedere l'idea a livello di funzioni ordinarie, considera la seguente funzione.
Prende un valore `x` di qualsiasi tipo `A` e una funzione di tipo `A → B`, e
applica la funzione al valore:
-/

def pipe {A B : Type} (x : A) (f : A → B) : B := f x

example : pipe 3 squareN = 9 := by rfl
example : (3 |> squareN) = pipe 3 squareN := by rfl

/-
Nota che la nostra `pipe` non è esattamente come Lean implementa `|>`, e
deliberatamente non attacchiamo il simbolo `|>` ad essa. Tuttavia, finché il lato
destro è una funzione, `x |> f` e `pipe x f` si comportano allo stesso modo.

Due dettagli sono importanti in pratica:

1. **Il valore piped diventa l'ultimo argomento.** Più in generale,
   `x |> f a b` è riscritto in `f a b x`. Questo funziona bene con
   l'applicazione parziale: `mapL g` è una funzione di tipo `List A → List B`,
   quindi `xs |> mapL g` è `mapL g xs`. Questo spiega anche perché funzioni come
   `mapL f xs`, `filterL p xs` e `foldRightL f z xs` prendono la lista come loro
   *ultimo* argomento: le rende comode da usare in una pipeline.

2. **Il pipe ha precedenza molto bassa**, più bassa di `+` e persino di `=`.
   Pertanto una pipeline dentro un'espressione più grande deve essere messa tra
   parentesi. Ad esempio, `3 |> squareN = 9` sarebbe letto come `3 |> (squareN = 9)`,
   che è un errore di tipo; questo è il motivo per cui gli esempi sopra sono
   scritti come `(3 |> squareN) = 9`.
-/


/- __Checkpoint 15__ Prevedi i valori delle seguenti pipeline -/

example : (3 |> squareN  |> squareN |> doubleN) = 162 := by rfl
example : (10 |> Nat.sub 3) = 7 := by rfl
example : (10 |> (fun x => Nat.sub x 3)) = 7 := by rfl


/-
Le pipeline sono particolarmente utili per processare liste, combinando le funzioni
`mapL`, `filterL` e i fold.

La seguente pipeline sostituisce ogni elemento pari con `1` e ogni elemento
dispari con `0`, e poi somma i risultati; in altre parole, conta gli elementi pari:
-/

example :
  ([1,2,3,4,5,6,7]
  |> mapL (fun x => if x % 2 = 0 then 1 else 0)
  |> sumFold)
  = 3 := by rfl

/-
Confrontala con l'espressione equivalente senza il pipe, dove le operazioni sono
lette dall'interno verso l'esterno:
-/

example :
  sumFold
    (mapL (fun (x : Nat) => if x % 2 = 0 then 1 else 0)
      [1, 2, 3, 4, 5, 6, 7])
  = 3 := by rfl


/- __Checkpoint 15__ Definisci una funzione `sumSqEven` che calcola la somma dei
quadrati di tutti gli elementi pari di una lista. Combina map, filter e fold con
l'operatore pipe.
-/

def sumSqEven (xs : List Nat) : Nat :=
  xs
  |> filterL (fun x => decide (x % 2 = 0))
  |> mapL (fun x => x * x)
  |> sumFold

example : sumSqEven [] = 0 := by rfl
example : sumSqEven [1, 3, 5] = 0 := by rfl
example : sumSqEven [1, 2, 3, 4, 5] = 20 := by rfl


end Pipe_operator


end Lists