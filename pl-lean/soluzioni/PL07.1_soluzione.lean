set_option autoImplicit false

/-
# Logica proposizionale e isomorfismo di Curry–Howard

Nelle lezioni precedenti abbiamo scritto *programmi* come funzioni tra tipi dati.
In questa lezione scriviamo *dimostrazioni*, e scopriamo che le due attività sono equivalenti:

    una proposizione è un tipo, e una dimostrazione di una proposizione è un programma di quel tipo.

Questa osservazione è l'**isomorfismo di Curry–Howard**.

Questo è il fondamento di Lean e di ogni assistente alla dimostrazione basato
sulla teoria dei tipi.

Ecco la corrispondenza che costruiremo, una riga alla volta:

    Logica                Tipi (programmi)             Lean
    --------------------  ---------------------------  ---------------------------
    P → Q   (implica)     A → B     (funzioni)        P → Q
    P ∧ Q   (e)           A × B     (coppie)          P ∧ Q
    P ∨ Q   (o)           A ⊕ B     (unioni taggate)  P ∨ Q
    True                  Unit                         True
    False                 Empty                        False
    ¬P      (non)         A → Empty                    ¬P   (cioè, P → False)
    P ↔ Q   (sse)         (A → B) × (B → A)            P ↔ Q

Alla fine della lezione dovresti essere in grado di:

* capire cosa significa `p : P` quando `P` è una proposizione;
* dimostrare tautologie proposizionali in **modalità tattica** e in **modalità
  termine**, e tradurre una dimostrazione da una modalità all'altra;
* spiegare perché entrambe le modalità producono lo stesso oggetto;
* enunciare il dizionario di Curry–Howard (implicazione, congiunzione,
  disgiunzione, falsità, negazione) e collegarlo alle regole di tipaggio
  `T-Abs`, `T-App`, `T-Pair`, `T-Proj`, `T-Inl`, `T-Inr`, `T-Case` delle
  lezioni di teoria;
* decidere se una formula proposizionale è dimostrabile *costruttivamente*
  chiedendoti se puoi scrivere un programma del tipo corrispondente.

Le difficoltà degli esercizi usano la stessa scala relativa delle lezioni precedenti:

* **1/4:** un'idea diretta;
* **2/4:** due idee devono essere combinate;
* **3/4:** una costruzione o dimostrazione più sostanziale;
* **4/4:** una sfida opzionale.

Trovi ulteriori esercizi estesi nel file `PL07_PropEx.lean`.

Una particolarità di questa lezione di laboratorio è:

    **Ogni teorema è dimostrato due volte: una in modalità tattica, una in modalità termine.**

Scrivere entrambe le versioni è ciò che rende visibile l'isomorfismo di Curry–Howard.
Gli esercizi quindi vengono in coppie, con nomi che terminano in `_tac` e `_term`.
Dopo aver risolto una coppia, esegui `#print` su entrambi i nomi e confronta ciò
che Lean ti mostra.

Ogni volta che il cursore è dentro una dimostrazione tattica, la infoview mostra
lo *stato della dimostrazione*:

    P Q : Prop
    h : P ∧ Q
    ⊢ Q ∧ P

Sopra la barra `⊢` ci sono le **ipotesi** (il contesto di tipaggio Γ delle lezioni
di teoria); sotto c'è il **goal** (il tipo che dobbiamo abitare). Una tattica
trasforma lo stato della dimostrazione; la dimostrazione è finita quando non
restano goal. Nei commenti di questo file scriviamo uno stato della dimostrazione
su una riga come `h : P ∧ Q ⊢ Q ∧ P`.
-/

section Types_and_proofs

/-
## Tipi e dimostrazioni

Finora, la notazione `e : T` ha espresso che un *termine* `e` ha un *tipo* `T`:

    5 : Nat          true : Bool          [1, 2, 3] : List Nat

In Lean, la stessa notazione ha un significato logico:

* una **proposizione** è un tipo `P` il cui kind è `Prop`;
* una **dimostrazione** di `P` è un termine `p` di tipo `P`. Leggi `p : P` come
  "`p` è una dimostrazione di `P`".
-/

#check Prop
#check (2 + 2 = 4)          -- una proposizione: è un tipo, di kind Prop
#check (rfl : 2 + 2 = 4)    -- una dimostrazione di quella proposizione

/-
In Lean, il comando `theorem` è usato per definire termini tipati come proposizioni,
mentre termini con qualsiasi tipo possono essere definiti con il comando `def`.
-/

theorem two_plus_two : 2 + 2 = 4 := rfl   -- accettato
-- theorem three : Nat := 3               -- rifiutato, poiché `Nat` non è una proposizione.

/-
La corrispondenza tra programmi e logica è riassunta come segue:

    Programmazione        Logica
    ------------------    --------------------------
    tipo  `A : Type`      proposizione  `P : Prop`
    termine  `a : A`      dimostrazione  `p : P`
    scrivere un programma dimostrare un teorema
-/


/-
__Checkpoint 1__  Quale dei seguenti esempi è una *dimostrazione* e quale un *programma*?
`2 + 2 = 5` è una proposizione? Puoi dimostrarla?
-/

example : 2 + 2 = 4 := rfl    -- dimostrazione (proposizione vera)
example : Nat := 2 + 2        -- programma (tipo Nat)
example : Bool := true        -- programma (tipo Bool)

-- `2 + 2 = 5` è una proposizione (falsa), ma non può essere dimostrata.

/-
__Checkpoint 2__  Prevedi i tipi delle seguenti tre espressioni,
poi controllali. Quali funzioni familiari sono? Nota che la seconda e la terza
menzionano `Prop` nel binder: sono *polimorfe* in una proposizione `P`,
esattamente come le funzioni polimorfe del laboratorio precedente erano polimorfe in un tipo.
-/

#check (fun {A : Type} (a : A) => a)       -- {A : Type} → A → A (identità)
#check (fun {P : Prop} (p : P) => p)       -- {P : Prop} → P → P (identità logica)
#check (fun {A B : Type} (a : A) (_ : B) => a)  -- {A B : Type} → A → B → A (K combinator)
#check (fun {P Q : Prop} (p : P) (_ : Q) => p)  -- {P Q : Prop} → P → Q → P (K logico)


end Types_and_proofs



section Implication

/-
## Implicazione

L'interpretazione costruttiva dell'implicazione è:

    una dimostrazione di `P → Q` è una funzione che trasforma qualsiasi dimostrazione di `P` in una dimostrazione di `Q`.

Quindi una dimostrazione di un'implicazione è letteralmente una funzione, e *usare*
un'implicazione è *applicazione di funzione*. Ci sono due modi per scrivere una
tale funzione in Lean:

* **modalità termine**:    scrivi la funzione, `:= fun p => ...`;
* **modalità tattica**:  scrivi `:= by` seguito da una lista di tattiche, e Lean
  costruisce la funzione per noi.

Iniziamo considerando l'implicazione

    A → A

In modalità termine, un abitante di questo tipo è la funzione identità:
-/

def id_term_data {A : Type} : A → A :=
  fun a => a

/-
Quando interpretiamo il tipo A → A come proposizione logica, risulta essere una tautologia:

    P → P

Il codice è identico: cambiano solo i tipi (`Type` vs. `Prop`).
-/
theorem id_term {P : Prop} : P → P :=
  fun p => p

/-
Anche in modalità tattica, le due dimostrazioni sono identiche:
-/

def id_tac_data {A : Type} : A → A := by
  intro a        -- a : A ⊢ A
  exact a

theorem id_tac {P : Prop} : P → P := by
  intro p        -- p : P ⊢ P
  exact p

/-
Due tattiche sono sufficienti per l'implicazione:

* `intro x` — il goal è `A → B`; assumi `x : A` e continua con il goal `B`.
  Questa è la lambda: costruisce `fun x => ?`.
* `exact h` — il termine `h` ha esattamente il tipo del goal: chiudi il goal con esso.
-/


/- Ora considera il tipo:

    A → (B → A)

  Le funzioni che abitano questo tipo prendono un input di tipo A, e restituiscono una funzione in B → A.
  Equivalentemente, prendono un input di tipo A, poi un altro input di tipo B, e restituiscono
  un valore di tipo A.

  Tale funzione può essere definita in vari modi equivalenti:
-/

def k_term_data {A B : Type} : A → B → A :=
  fun (a : A) => fun (_b : B) => a

def k_term_data₂ {A B : Type} : A → B → A :=
  fun (a : A) (_b : B) => a

def k_term_data₃ {A B : Type} : A → B → A :=
  fun a _ => a

/-
Quando interpretiamo il tipo A → B → A come proposizione logica, risulta ancora
una tautologia, nota come **combinatore K**:

    P → (Q → P)

Come prima, possiamo dimostrare tale proposizione usando lo stesso termine:
-/

theorem k_term {P Q : Prop} : P → Q → P :=
  fun p => fun _ => p

/-
__Checkpoint 3__  Dimostra il combinatore K in modalità tattica.
(Suggerimento: dopo `intro p q`, una delle due ipotesi è inutile.)
-/

theorem k_tac {P Q : Prop} : P → Q → P := by
  intro p q
  exact p


/-
Ora considera il tipo:

  (A → B) → (B → C) → A → C

I termini di questo tipo sono funzioni che prendono due input: una funzione `f` in A → B e
una funzione `g` in B → C, e restituiscono una funzione in A → C. Abbiamo già visto che
questo è esattamente il comportamento della composizione di funzioni:
-/

def imp_trans_term_data {A B C : Type} (f : A → B) (g : B → C) : A → C :=
  g ∘ f

/- O, equivalentemente: -/

def imp_trans_term_data₂ {A B C : Type} : (A → B) → (B → C) → A → C :=
  fun f g a => g (f a)

/-
In logica, il tipo sopra è una proposizione che afferma che l'implicazione è transitiva:

  (P → Q) → (Q → R) → P → R

In modalità termine, possiamo dimostrare tale proposizione esattamente come prima:
-/

theorem imp_trans_term {P Q R : Prop} : (P → Q) → (Q → R) → P → R :=
  fun f g p => g (f p)

/-
In modalità tattica, iniziamo introducendo `f`, `g` e `p`. Poi usiamo `apply`,
che ragiona *all'indietro*: riduciamo il goal `R` a `Q` applicando `g : Q → R`.
Poi, riduciamo il nuovo goal `Q` a `P` applicando `f : P → Q`.
Ora il goal è `P`, che è esattamente una delle ipotesi nel contesto.
-/

theorem imp_trans_tac {P Q R : Prop} : (P → Q) → (Q → R) → P → R := by
  intro f g p      -- f : P → Q,  g : Q → R,  p : P  ⊢ R
  apply g          -- ⊢ Q     (goal R, e g : Q → R)
  apply f          -- ⊢ P     (goal Q, e f : P → Q)
  exact p          -- p : P


/-
Le tattiche e i termini corrispondono come segue.

    Tattica       Termine                   Regola del lambda-calcolo
    ------------  ------------------------  ---------------------------
    intro x       fun x => ...              T-Abs
    exact h       h                         T-Var
    apply f       f ?                       T-App (letta all'indietro)
-/


/-
## Esercizio: Modus Ponens (difficoltà: 1/4)

Considera il tipo:

    A → (A → B) → B

È abitato da funzioni che prendono come input un elemento `a : A` e una funzione
`f : A → B`, e restituiscono un elemento di tipo `B`. Costruire tale termine è facile.
-/

theorem mp_term_data {A B : Prop} : A → (A → B) → B :=
  fun a f => f a

/-
In logica, il tipo sopra è una proposizione nota come **modus ponens**:

    P → (P → Q) → Q

Da una dimostrazione di `P` e una dimostrazione di `P → Q`, ottieni una dimostrazione di `Q`.
Scrivi dimostrazioni (sia in modalità termine che in modalità tattica) per essa.
-/

theorem mp_term {P Q : Prop} : P → (P → Q) → Q :=
  fun p f => f p

theorem mp_tac {P Q : Prop} : P → (P → Q) → Q := by
  intro p f
  apply f
  exact p


end Implication



section Conjunction

/-
## Congiunzione

L'interpretazione costruttiva della congiunzione è:

    una dimostrazione di `P ∧ Q` è una coppia `⟨p, q⟩` dove `p` è una dimostrazione di `P` e `q` è una dimostrazione di `Q`.

Questo significa che **dimostrare** una congiunzione è simile a testimoniare un elemento in un
tipo prodotto `A × B`:

* **modalità termine**:    scrivi la coppia `⟨p,q⟩`;
* **modalità tattica**:  dividi la dimostrazione in due casi con `constructor`, e poi dimostriamo
separatamente `p` e `q`.

Simmetricamente, **usare** una congiunzione `h` nel contesto della dimostrazione è simile a proiettare
gli elementi di una coppia in un tipo prodotto:

* **modalità termine**:    scrivi le proiezioni `h.1` o `h.2`;
* **modalità tattica**:  estrai i due congiunti con `rcases h with ⟨p,q⟩`.

Iniziamo considerando l'implicazione

    A × B → A

La dimostriamo prima sui dati e poi sulle proposizioni, sia in modalità termine che in modalità tattica.
-/

def fst_term {A B : Type} : A × B → A :=
  fun p => p.1

/- o, equivalentemente: -/
def fst_term₂ {A B : Type} : A × B → A :=
  fun (a, _) => a

/-
Una nota sulle parentesi angolari `⟨` e `⟩` (digitate `\<` e `\>`).

Se un tipo induttivo ha esattamente un costruttore (per esempio, qualsiasi `structure`), Lean
ci permette di costruire i suoi termini senza scrivere il nome del costruttore, usando la
notazione del *costruttore anonimo* `⟨ ... ⟩`. Per esempio:

* Il prodotto `A × B` è notazione per `Prod A B`, una struttura il cui unico costruttore
  `Prod.mk` prende due argomenti. Quindi `⟨a, b⟩ : A × B` significa `Prod.mk a b`, che è
  anche scritto `(a, b)`.
* La congiunzione `P ∧ Q` è una struttura `And P Q` il cui unico costruttore `And.intro`
  prende una dimostrazione di `P` e una dimostrazione di `Q`. Quindi `⟨p, q⟩ : P ∧ Q` significa `And.intro p q`.

Pertanto, possiamo riscrivere la dimostrazione precedente usando le parentesi angolari:
 -/

def fst_term₃ {A B : Type} : A × B → A :=
  fun ⟨a, _⟩ => a

/- Le stesse dimostrazioni per le proposizioni. `Type` diventa `Prop`, `×` diventa `∧`. -/

theorem and_left_term {P Q : Prop} : P ∧ Q → P :=
  fun h => h.1

theorem and_left_term₂ {P Q : Prop} : P ∧ Q → P :=
  fun ⟨p, _⟩ => p

/-
In modalità tattica, estrarre gli elementi di una coppia può essere fatto con `rcases`:
-/

def fst_tac {A B : Type} : A × B → A := by
  intro p
  rcases p with ⟨a, _⟩
  exact a

/- La stessa dimostrazione per le proposizioni. -/

theorem and_left_tac {P Q : Prop} : P ∧ Q → P := by
  intro h
  rcases h with ⟨p, _⟩
  exact p


/-
Ora usiamo `#print` per vedere cosa sono davvero queste dimostrazioni. Per Lean, una dimostrazione è sempre un *termine*, anche quando l'hai scritta in modalità tattica.
-/

#print and_left_tac
#print and_left_term

/-
Questo è un punto chiave: una dimostrazione tattica è solo una ricetta che costruisce un termine.
Quando le tattiche hanno finito, Lean controlla il termine risultante con il suo
kernel fidato, esattamente come fa per una dimostrazione scritta direttamente in modalità termine.
-/


/-
__Checkpoint 4__  Le due dimostrazioni `and_left_tac` e `and_left_term` sembrano diverse.
Ti aspetti che Lean accetti la seguente affermazione, che dice che sono *uguali*?
E che dire della seconda e della terza affermazione?
-/

-- example : @and_left_tac = @and_left_term := rfl
-- example (a b : Nat) : a = b := rfl
-- example : @fst_term = @fst_tac := rfl

/-
La prima affermazione è accettata. Infatti, Lean tratta tutte le dimostrazioni della stessa proposizione come
definizionalmente uguali (questo è chiamato *proof irrelevance*): per una proposizione, non
importa *come* è stata dimostrata, solo *che* è stata dimostrata. Quindi la dimostrazione tattica e la dimostrazione
termine sono, per Lean, lo stesso oggetto.

La seconda affermazione è (naturalmente) rifiutata: due numeri arbitrari non sono sempre
uguali.

La terza affermazione è accettata, ma non per la proof irrelevance: `A × B` è un tipo di dati, non una proposizione. È accettata perché le due funzioni sono *definizionalmente*
uguali. Srotolando le definizioni, `rcases` produce `Prod.casesOn p (fun a _ => a)`, e Lean lo riduce a `p.1` usando la *structure eta*: una coppia `p` è definizionalmente uguale alla
coppia `(p.1, p.2)` delle sue proiezioni. Per i dati, `rfl` ha successo solo quando l'uguaglianza può essere
controllata per srotolamento e calcolo, che è più forte di "calcolare lo stesso risultato
su ogni input".
-/


/-
Ora considera il tipo:

  (A × B) → (B × A)

I termini di questo tipo sono funzioni che prendono come input una coppia di tipo `A × B` e restituiscono
una coppia scambiata di tipo `B × A`. Sappiamo già come scrivere tale funzione:
-/

def prod_swap_term {A B : Type} : A × B → B × A :=
  fun h => ⟨h.2, h.1⟩

/-
In modalità tattica, diamo due dimostrazioni alternative.
Nella prima dimostrazione, estraiamo le componenti della coppia, e poi dividiamo il goal
in due casi usando `constructor`.
Nella seconda dimostrazione, usiamo `exact` per fornire direttamente un termine con il tipo atteso.
-/

def prod_swap_tac {A B : Type} : A × B → B × A := by
  intro h
  rcases h with ⟨a, b⟩   -- a : A, b : B ⊢ B ∧ A
  constructor
  . exact b
  . exact a

def prod_swap_tac₂ {A B : Type} : A × B → B × A := by
  intro h
  rcases h with ⟨a, b⟩   -- a : A, b : B ⊢ B ∧ A
  exact ⟨b,a⟩

/-
__Checkpoint 5__ Verifica che le stesse dimostrazioni valgano quando si passa dai tipi alle proposizioni.
-/

theorem and_swap_term {P Q : Prop} : P ∧ Q → Q ∧ P :=
  fun h => ⟨h.2, h.1⟩

theorem and_swap_tac {P Q : Prop} : P ∧ Q → Q ∧ P := by
  intro h
  rcases h with ⟨p, q⟩
  constructor
  · exact q
  · exact p


/- ## Esercizio: Currying e uncurrying (difficoltà: 2/4)

Dimostra l'equivalente logico del currying/uncurrying nei tipi, sia in modalità tattica che in modalità termine.
Suggerimento: per usare un'ipotesi `f : P ∧ Q → R` devi prima costruire una dimostrazione di `P ∧ Q`;
per usare `h : P ∧ Q` come argomento di funzione, prendi le sue componenti `h.1` e `h.2`. -/

theorem curry_tac {P Q R : Prop} : (P ∧ Q → R) → P → Q → R := by
  intro f p q
  apply f
  exact ⟨p, q⟩

theorem curry_term {P Q R : Prop} : (P ∧ Q → R) → P → Q → R :=
  fun f p q => f ⟨p, q⟩

theorem uncurry_tac {P Q R : Prop} : (P → Q → R) → P ∧ Q → R := by
  intro f h
  rcases h with ⟨p, q⟩
  apply f
  · exact p
  · exact q

theorem uncurry_term {P Q R : Prop} : (P → Q → R) → P ∧ Q → R :=
  fun f h => f h.1 h.2

end Conjunction



section Disjunction

/-
## Disgiunzione

L'interpretazione costruttiva della disgiunzione è:

    una dimostrazione di `P ∨ Q` è o una dimostrazione di `P` o una dimostrazione di `Q`, taggata con l'informazione di quale delle due è.

I tag sono i due costruttori `Or.inl p` e `Or.inr q`.

Questo significa che **dimostrare** una disgiunzione è simile a testimoniare un elemento in un
tipo somma `A ⊕ B`:

* **modalità termine**:    usa i costruttori di tipo `Sum.inl` e `Sum.inr`;
* **modalità tattica**:  usa la tattica `left` per dimostrare `P`, o la tattica `right` per dimostrare `Q`.

Simmetricamente, **usare** una disgiunzione `h` nel contesto della dimostrazione è simile all'analisi per casi:

* **modalità termine**:    `match h with | ...`;
* **modalità tattica**:  `rcases h with p | q`.

Iniziamo considerando l'implicazione

    A ⊕ B → B ⊕ A

La dimostriamo prima sui dati e poi sulle proposizioni, sia in modalità termine che in modalità tattica.
-/

def sum_swap_term {A B : Type} : A ⊕ B → B ⊕ A :=
  fun s => match s with
  | .inl a => .inr a      -- costruttore implicito Sum
  | .inr b => .inl b

/- Lo stesso termine di dimostrazione può essere usato per dimostrare la proposizione corrispondente: -/
theorem or_swap_term {P Q : Prop} : P ∨ Q → Q ∨ P :=
  fun s => match s with
  | .inl p => .inr p      -- costruttore implicito Or
  | .inr q => .inl q

/- In modalità tattica, dimostriamo o il ramo sinistro o il ramo destro di `B ⊕ A`.
   Il caso effettivo dipende da quale caso vale nell'ipotesi `B ⊕ A`. -/
def sum_swap_tac {A B : Type} : A ⊕ B → B ⊕ A := by
  intro s
  rcases s with a | b
  . right
    exact a
  . left
    exact b

/- La stessa tattica può essere usata per dimostrare la proposizione corrispondente: -/
theorem or_swap_tac {P Q : Prop} : P ∨ Q → Q ∨ P := by
  intro h              -- h : P ∨ Q ⊢ Q ∨ P
  rcases h with p | q  -- due goal:  p : P ⊢ Q ∨ P   e   q : Q ⊢ Q ∨ P
  · right              -- ⊢ P
    exact p
  · left               -- ⊢ Q
    exact q


/-
__Checkpoint 6__  In `or_swap_tac`, metti il cursore dopo la riga
`rcases h with p | q` e leggi la infoview. Quanti goal ci sono?
Quali ipotesi ha ciascun goal? Perché una disgiunzione non può essere usata per dimostrare
qualcosa che richiede sia `p` che `q`?
-/


/-
__Checkpoint 7__  Decidi, senza provare, quali dei seguenti sono dimostrabili.
Chiediti per ciascuno: *posso scrivere una funzione totale di questo tipo?*
(Pensa a cosa riceve la funzione come input, e quali valori può costruire.)

    (a)  P ∧ Q → P          -- SÌ: proiezione sinistra
    (b)  P ∨ Q → P          -- NO: non sai quale dei due vale
    (c)  P → P ∨ Q          -- SÌ: inl
    (d)  P → P ∧ Q          -- NO: non hai Q
    (e)  P ∧ Q → P ∨ Q      -- SÌ: proietta e usa inl
    (f)  P ∨ Q → P ∧ Q      -- NO: non puoi avere entrambi da uno solo
-/


/- ## Esercizio: Regola di eliminazione (difficoltà: 2/4)

Dimostra la *regola di eliminazione* della disgiunzione: se `P` implica `R` e `Q` implica `R`, allora `P ∨ Q` implica `R`. Dimostrazione tattica e dimostrazione termine.
-/

theorem or_elim_tac {P Q R : Prop} : (P → R) → (Q → R) → P ∨ Q → R := by
  intro f g h
  rcases h with p | q
  · apply f
    exact p
  · apply g
    exact q

theorem or_elim_term {P Q R : Prop} : (P → R) → (Q → R) → P ∨ Q → R :=
  fun f g h => match h with
  | .inl p => f p
  | .inr q => g q

end Disjunction



section Falsity_and_negation

/-
## Falsità e negazione

Il tipo di dato `Empty` non è abitato: non ha regole di introduzione.
La regola di eliminazione per il tipo vuoto è:

    Empty.elim : Empty → A

che significa che per qualsiasi tipo A, c'è sempre una funzione da Empty a A:

In modalità tattica, usare un'ipotesi `h` di tipo Empty si fa per analisi per casi su `h`.
Poiché Empty non ha costruttori, ci saranno **zero** casi.

Il corrispondente logico del tipo `Empty` è `False`, una proposizione senza dimostrazione.
La regola di eliminazione per `False` è:

    False.elim : False → P

Questo significa che una contraddizione dimostra qualsiasi cosa ("ex falso quodlibet").
Come per il tipo `Empty`, un `False` nel contesto può essere eliminato per analisi per casi.
-/

def empty_elim_term {A : Type} : Empty → A :=
  fun e => Empty.elim e

theorem false_elim_term {P : Prop} : False → P :=
  fun h => False.elim h

def empty_elim_tac {A : Type} : Empty → A := by
  intro e
  cases e

theorem false_elim_tac {P : Prop} : False → P := by
  intro h
  cases h

/-
Nella logica costruttiva, la negazione `¬P` è definita come `P → False`. Questo vale anche in Lean.

Quindi, una dimostrazione di `¬P` è una funzione che trasforma qualsiasi (ipotetica) dimostrazione di `P`
in una dimostrazione di `False`. Per *dimostrare* `¬P` facciamo `intro` di una dimostrazione di `P` e deriviamo una contraddizione. Per *usare* un'ipotesi `h : ¬P` la applichiamo a una dimostrazione di `P`.
-/

example {P : Prop} : (¬P) = (P → False) := rfl

/-
Dimostriamo che ogni proposizione implica la sua doppia negazione:

    P → ¬¬P.

Espandendo la negazione in `P` implica `False`, questo diventa:

    P → (P → False) → False

Ancora una volta scriviamo prima lo stesso programma sui dati, sostituendo `False` con `Empty`.

In modalità termine, la dimostrazione è diretta.
-/

def not_not_intro_term_data {A : Type} : A → (A → Empty) → Empty :=
  fun a k => k a

theorem not_not_intro_term {P : Prop} : P → ¬¬P :=
  fun p np => np p

/- In modalità tattica, la dimostrazione è essenzialmente la stessa. -/

def not_not_intro_tac_data {A : Type} : A → (A → Empty) → Empty := by
  intro a
  intro na
  exact na a

/- In alternativa, puoi fare ragionamento all'indietro con `apply`. -/
def not_not_intro_tac_data₂ {A : Type} : A → (A → Empty) → Empty := by
  intro a
  intro na
  apply na
  exact a

/- Le stesse tattiche funzionano quando si passa dai tipi alle proposizioni. -/
theorem not_not_intro_tac {P : Prop} : P → ¬¬P := by
  intro p       -- p : P ⊢ ¬¬P
  intro np      -- np : ¬P ⊢ False
  exact np p

/-
In parole: data una dimostrazione `p` di `P`, e una refutazione `np` di `P`, applichiamo la refutazione
alla dimostrazione, e otteniamo una contraddizione.
-/


/- __Checkpoint 8__  La conversa, `¬¬P → P`, è dimostrabile?  Inizia una dimostrazione in modalità tattica:

    theorem dne_attempt {P : Prop} : ¬¬P → P := by
      intro h        -- h : ¬¬P ⊢ P
      ...

Che goal hai? Cosa puoi fare con `h`? Perché sei bloccato?
-/

/- Dimostriamo ora che da una contraddizione segue qualsiasi cosa: `P → ¬P → Q`.  -/

theorem explosion_tac {P Q : Prop} : P → ¬P → Q := by
  intro p np
  have nq : False → Q := by
    intro f
    cases f
  apply nq
  apply np
  exact p

/- In questa dimostrazione, abbiamo esplicitamente sostituito il goal Q con False, e poi abbiamo dimostrato
False usando le assunzioni ¬P e P nel contesto.

La tattica `contradiction` ci permette di dimostrare qualsiasi goal quando ¬P e P sono nel contesto.
-/

theorem explosion_tac_contradiction {P Q : Prop} : P → ¬P → Q := by
  intro p np
  contradiction

/- In modalità termine, la dimostrazione è diretta: prima otteniamo `False` applicando `np` a `p`,
e poi otteniamo `Q` applicando `False.elim` a `False` -/
theorem explosion_term {P Q : Prop} : P → ¬P → Q :=
  fun p np => False.elim (np p)


/- ## Esercizio: Contrappositiva (difficoltà: 2/4)

Dai una dimostrazione tattica e una dimostrazione termine di:

    (P → Q) → ¬Q → ¬P
-/

theorem contrapositive_term {P Q : Prop} : (P → Q) → ¬Q → ¬P :=
  fun f nq p => nq (f p)

theorem contrapositive_tac {P Q : Prop} : (P → Q) → ¬Q → ¬P := by
  intro f nq p
  apply nq
  apply f
  exact p

end Falsity_and_negation


section True

/-
## Unit e True

Il tipo `Unit` è abitato da esattamente un valore, `()`.
-/

def unit_term : Unit := ()

/-
La corrispondenza logica è con la proposizione `True`, che ha una dimostrazione canonica:

    True.intro : True
-/

theorem true_term : True :=
  True.intro

/- La stessa dimostrazione può essere scritta in modalità tattica (possiamo in alternativa usare `trivial`). -/
theorem true_tactic : True := by
  exact True.intro

/- Dimostriamo che il tipo:

    A → Unit

  è abitato da una funzione che scarta l'input e restituisce il valore Unit.
-/

def fun_unit_term {A : Type} : A → Unit :=
  fun _ => ()

/- Possiamo similmente dimostrare che `True` segue da qualsiasi proposizione `P`. -/

theorem imp_true_term {P : Prop} : P → True :=
  fun _ => True.intro

/- La corrispondente dimostrazione tattica introduce l'assunzione e poi la ignora. -/
theorem imp_true_tactic {P : Prop} : P → True := by
  intro _
  trivial

/- __Exercise (difficoltà: 1/4)__ Dimostra che `True` è neutro per la congiunzione.
Conversamente, da una dimostrazione di `P`, possiamo costruire una dimostrazione di `True ∧ P`. -/

theorem true_and_elim {P : Prop} : True ∧ P → P := by
  intro h
  exact h.2

theorem true_and_intro {P : Prop} : P → True ∧ P := by
  intro p
  exact ⟨True.intro, p⟩

end True



section Classical_boundary

/-
## Il confine classico

Diverse tautologie familiari **non** sono dimostrabili nella logica costruttiva che abbiamo
usato finora. Tre importanti sono:

    P ∨ ¬P                  terzo escluso
    ¬¬P → P                 eliminazione della doppia negazione
    ¬(P ∧ Q) → ¬P ∨ ¬Q      la seconda legge di De Morgan

Nella logica costruttiva, una dimostrazione di `P ∨ ¬P` dovrebbe dire *quale* lato vale, cioè
sarebbe un programma che *decide* una proposizione arbitraria `P`. Tale programma non
esiste. (Per `Bool` possiamo decidere per calcolo, come abbiamo fatto nel primo laboratorio: questo
è il motivo per cui `b || !b = true` era dimostrabile per casi. Per una proposizione arbitraria non c'è
nulla da calcolare.)

Lean offre il ragionamento classico come un *assioma*: `Classical.em : ∀ P, P ∨ ¬P`.
Sfruttandolo possiamo dimostrare le implicazioni mancanti:
-/

theorem dne_tac {P : Prop} : ¬¬P → P := by
  intro h
  rcases Classical.em P with p | np
  · exact p
  · exfalso
    exact h np

/-
Lean può dirci da quali assiomi dipende un teorema. Confronta i due comandi sotto:
il teorema costruttivo dovrebbe riportare che non dipende da alcun assioma, mentre quello classico
menziona l'assioma di scelta (da cui deriva `Classical.em`).
-/

#print axioms and_swap_tac
#print axioms dne_tac


/- __Exercise (difficoltà: 3/4)__ Dimostra la conversa della contrappositiva,
`(¬Q → ¬P) → (P → Q)`, che è classica. -/

theorem contrapositive_conv_tac {P Q : Prop} : (¬Q → ¬P) → (P → Q) := by
  intro h p
  rcases Classical.em Q with q | nq
  · exact q
  · exfalso
    apply h nq
    exact p

theorem contrapositive_conv_term {P Q : Prop} : (¬Q → ¬P) → (P → Q) :=
  fun h p => Classical.byContradiction (fun nq => h nq p)

end Classical_boundary