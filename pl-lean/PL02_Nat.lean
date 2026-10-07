/-

# Natural numbers, recursion, and higher-order functions

This file is both a lecture and a Lean program.  Read the comments from top to
bottom, but also place the cursor on each command and inspect Lean's Infoview.
You are encouraged to change expressions, introduce mistakes, and observe
Lean's responses.

In the previous lecture we learned how to:
* inspect and evaluate Lean expressions;
* define constants and pure functions;
* use `Bool`, conditional expressions, and pattern matching;
* use functions as values;
* state simple properties and prove them with basic tactics.

In this lecture we use all of these ideas again, now on the *natural numbers*.
Natural numbers are our first example of an inductive type with infinitely many
values.  They are the simplest place to see how *data*, *recursive functions*,
and *proofs by induction* fit together.

We will learn how to:
* inspect the inductive type `Nat` and its two constructors;
* define functions on `Nat` by pattern matching;
* define recursive functions, and understand structural recursion;
* write arithmetic functions: addition, multiplication, powers, factorial,
  comparison, and subtraction;
* combine `if` expressions with Boolean-valued functions;
* write higher-order functions: functions that take functions as arguments, or
  that return functions as results;
* use anonymous functions and partial application;
* prove simple properties of our programs with `rfl`, `rw`, `simp`, `cases`,
  and `induction`.

-/

set_option autoImplicit false


section Reading_this_file

/-
## How to read this file

As in the previous lecture, comments explain the ideas while the declarations
below them are actual Lean code.

Remember the three commands that are especially useful while learning:

* `#check e` asks Lean for the type of `e`;
* `#eval e` evaluates `e` when Lean can compute its value;
* `#print name` displays a declaration.

We will use all three again below.  We will also use `example`, which states a
fact and asks Lean to check it, without giving the fact a name.

### How the exercises work

Exercises are marked with the word `Exercise`.  In most of them you replace the
placeholder `sorry` with your own solution.  The word `sorry` means "I promise
to fill this in later": Lean accepts it, but shows a warning.

Many programming exercises are followed by a few *tests*, written like this:

    example : tripleN 4 = 12 := by rfl

A test is silent when it passes and shows an error when it fails.  So when you
open this file for the first time, the tests of the exercises are red: this is
expected!  Your goal is to make them silent.  You can always use `#eval` to
experiment while you work.

-/

/-
__Exercise__: before continuing, write in a comment the type of `7`.
What do you expect `#check 7` to report?  Then check your guess.
-/

-- Your answer:

#check 7

/-
Numerals such as `7` could in principle denote many kinds of numbers (natural
numbers, integers, floating-point numbers, ...).  When nothing else says
otherwise, Lean chooses `Nat`.

-/

end Reading_this_file


section Natural_numbers

/-
## Natural numbers

Natural numbers are the numbers

    0, 1, 2, 3, ...

In Lean they form the inductive type `Nat`.

An *inductive type* is defined by listing its *constructors*: the only ways of
building a value of that type.  Conceptually, the constructors of `Nat` are:

* `Nat.zero`, which constructs zero;
* `Nat.succ n`, which constructs the successor of a natural number `n`.

As inference rules, we would write these constructors as:

                  n
--------      ----------
Nat.zero      Nat.succ n

Using these inference rules, we can derive that 3 is in Nat as follows:

--------
Nat.zero
------------------
Nat.succ Nat.zero
-----------------------------
Nat.succ (Nat.succ Nat.zero)
---------------------------------------
Nat.succ (Nat.succ (Nat.succ Nat.zero))

Thus:

    0       = Nat.zero
    1       = Nat.succ Nat.zero
    2       = Nat.succ (Nat.succ Nat.zero)
    3       = Nat.succ (Nat.succ (Nat.succ Nat.zero))

Numerals such as `0`, `1`, `2`, ... are just notation for natural-number values.
The important idea is not the notation itself, but the inductive structure:
starting from zero, every natural number is obtained by repeatedly taking a
successor.

This structure will guide both our programs and our proofs.

-/

#check Nat            --- also types have types!
#check Nat.zero
#check Nat.succ
#check (0 : Nat)
#check (7 : Nat)

#eval (0 : Nat)
#eval (1 : Nat)
#eval (7 : Nat)

#print Nat

/-
For example, `Nat.succ 4` is the natural number 5.
-/

#eval Nat.succ 4

/-
The constructor `Nat.succ` is itself a function in Nat → Nat.  Its type says that, given a
natural number, it produces another natural number:
-/

#check Nat.succ

/-
This is our first important example of an inductive type with a constructor
that has an argument.

Compare it with `Bool` from the previous lecture:

    Bool  has two constructors, `true` and `false`.
    Nat   has two constructors, `zero` and `succ`.

The difference is that `succ` carries another natural number with it.
That makes `Nat` *infinite*: from every natural number we can construct another
one by taking its successor.

-/

/-
### Two ways of writing the successor

Writing `Nat.succ n` is precise but heavy.  Lean also lets us write `n + 1` for
the successor of `n`.  The two expressions are the same number, and Lean
prefers to *print* `n + 1`: you will see it often in the Infoview.

The following facts hold by plain computation, so `rfl` proves them.
-/

example : Nat.succ 4 = 5 := by rfl

example : 3 = Nat.succ (Nat.succ (Nat.succ Nat.zero)) := by rfl

example (n : Nat) : Nat.succ n = n + 1 := by rfl

/-
Note however that `rfl` is not powerful enough to prove that `n + 1 = 1 + n`:
-/
example (n : Nat) : Nat.succ n = 1 + n := by sorry


/-
### Built-in arithmetic

Lean already knows the usual operations on natural numbers.
-/

#eval 7 + 5
#eval 7 * 5
#eval 17 / 5       -- integer division
#eval 17 % 5       -- remainder
#eval 2 ^ 10       -- power
#eval 2 ^ 100      -- no overflow: unlike `int` in C or Java, `Nat` is unbounded

/-
Subtraction deserves a warning.  There are no negative natural numbers, so
subtraction stops at zero:
-/

#eval 7 - 5
#eval 5 - 7

/-
In this lecture we deliberately *re-implement* addition, multiplication, and
so on from scratch (`addN`, `mulN`, ...).  The goal is to learn how recursive
functions on inductive data work, and later to prove things about them.  In real
programs you should of course use the built-in operations, which are much faster.

-/

end Natural_numbers


section Pattern_matching_on_Nat

/-
## Pattern matching on natural numbers

We already used pattern matching with `Bool`.  The same idea works with `Nat`.
A function on natural numbers can describe separately what happens for zero
and for a successor.

For example, the predecessor of zero is defined here to be zero, while the
predecessor of a successor is the number inside the successor.

-/

def predN (n : Nat) : Nat :=
  match n with
  | Nat.zero   => Nat.zero
  | Nat.succ k => k

#eval predN 0
#eval predN 1
#eval predN 7

/-
The pattern `Nat.succ k` does two things at once:

1. it checks that the argument is a successor;
2. it gives a name, `k`, to the number stored inside that successor.

This is exactly the same idea as pattern matching on a Boolean, but with the difference
that now the constructor carries data that we can use in the right-hand side.

Lean also checks that the patterns cover *all* constructors.
__Exercise__: Try commenting the `Nat.zero` case from `predN` and read the error message.

-/

--- The predecessor of the successor of n is always n
theorem pred_succ (n: Nat) : predN (Nat.succ n) = n := by rfl

--- Most of the times, also the successor of the predecessor of a n is n
example : Nat.succ (predN 3) = 3 := by rfl
example : Nat.succ (predN 7) = 7 := by rfl

/-
__Exercise__: but is this *always* true? If not, provide a counterexample
-/
example : let n := sorry                  --- replace this sorry with a natural number
  !(Nat.succ (predN n) = n) := by sorry   --- once done, replace this sorry with rfl


/-
We can also use the compact equation-style syntax introduced in the previous lecture.
-/

def isZero : Nat → Bool
  | 0          => true
  | Nat.succ _ => false

#eval isZero 0
#eval isZero 3

/-
The underscore `_` is a wildcard.  In the successor case we do not need to
remember which natural number occurs inside the successor.

Notice that the pattern `0` is a numeral, which is allowed in patterns.
Patterns may also use the notation `n + 1` instead of `Nat.succ n`.  So
`predN` can be written in a shorter way:
-/

def predN₂ : Nat → Nat
  | 0     => 0
  | n + 1 => n

#eval predN₂ 7

/-
From now on we will mostly use `n + 1` in patterns, since this is what Lean shows us in goals.
However, it must be used consciously: writing `1 + n` in a pattern results in an error!

Patterns can also be *nested*: the pattern `n + 2` means `Nat.succ (Nat.succ n)`,
and it matches every number that is at least two.
We can use it to compute the parity of a number.  A number is even when it is zero;
it is odd when it is one; otherwise we remove two successors and continue.
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
Notice the recursive call `isEven n` in the last case.  The argument of the
recursive call is smaller than the original argument `n + 2`.  Lean can see this
from the pattern: `n` is obtained from the original argument by removing two
constructors.

For example:

    isEven 4  =  isEven 2  =  isEven 0  =  true

This brings us to one of the central ideas of functional programming:
recursive data are naturally processed by recursive functions.

-/

/-
__Exercise__ (`plusTwo`): define a function `plusTwo` that adds 2 to its argument
Hint: not every function needs pattern matching.
-/

def plusTwo (n : Nat) : Nat :=
  sorry

example : plusTwo 0 = 2 := by sorry
example : plusTwo 1 = 3 := by sorry


/-
__Exercise__ (`minusTwo`): define a function `minusTwo` that subtracts two from
its argument, stopping at zero.
-/

def minusTwo (n : Nat) : Nat :=
  sorry

example : minusTwo 0 = 0 := by sorry
example : minusTwo 1 = 0 := by sorry
example : minusTwo 7 = 5 := by sorry


/-
__Exercise__ (`isOdd`): define `isOdd`, which is `true` exactly for the odd
numbers.  You can do it by pattern matching, or by reusing `isEven` together
with Boolean negation `!`.
-/

def isOdd (n : Nat) : Bool := match n with
  | 0     => false
  | 1     => true
  | n + 2 => isOdd n

example : isOdd 0 = false := by rfl
example : isOdd 7 = true := by rfl
example : isOdd 10 = false := by rfl

theorem odd_iff_not_even (n: Nat) : isOdd n ↔ !(isEven n) := by sorry

end Pattern_matching_on_Nat


section Recursion

/-
## Recursive functions

In an imperative language, a familiar way to process a natural number is a loop.
For example, we can add `m` to `n` by counting `m` down to zero:

    result := n
    while m > 0 do
        result := result + 1
        m := m - 1
    return result

In functional programming we express the same idea by recursion.
A function examines the input, handles the base case, and makes a recursive
call on a smaller piece of the input.  There are no variables to update: the
"loop counter" is simply an argument that becomes smaller in each call.

Here is addition, defined recursively on the second argument.

Mathematically:

    n + 0     = n
    n + (m+1) = (n + m) + 1

In Lean, that becomes:
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
The recursive call is `addN n m'`.  The new argument `m'` is smaller than the
original argument `m' + 1`.

Lean evaluates `addN 2 3` by unfolding the definition again and again:

    addN 2 3
    = Nat.succ (addN 2 2)
    = Nat.succ (Nat.succ (addN 2 1))
    = Nat.succ (Nat.succ (Nat.succ (addN 2 0)))
    = Nat.succ (Nat.succ (Nat.succ 2))
    = 5

Reading such a trace is a very good way to understand a recursive function.
When you are unsure about a definition, try to produce a trace by hand.

The definition follows a very useful pattern:

    match n with
    | base case      => result for the base case
    | recursive case => result built from a smaller recursive call

This is called *structural recursion*: the recursive calls are made on pieces
of the input obtained by removing constructors.  Lean accepts a recursive
definition only if it can check that the recursion terminates.  This is not
just a technicality.  Lean is also a proof assistant, and a function that
never terminates would allow us to prove false statements.  For instance,
Lean rejects the following definition, because the recursive call is on a
*bigger* number (try it in a scratch file and read the error message):

    def bad (n : Nat) : Nat :=
      bad (n + 1)

-/

/-
We can write the same definition using equation-style pattern matching.
-/

def addN₂ : Nat → Nat → Nat
  | n, 0      => n
  | n, m' + 1 => Nat.succ (addN₂ n m')

#eval addN₂ 4 5

/-
The two functions compute the same operation.  Later we will *prove* this.

For now, try to predict the result of each expression before asking Lean to
compute it.
-/

#eval addN 3 4
#eval addN (addN 1 2) 3

/-
A function can of course call a previously defined function.  We do not need
to repeat the implementation of addition every time we want to add numbers.
This is one of the main reasons for defining small reusable functions.
-/

def doubleN (n : Nat) : Nat :=
  addN n n

#eval doubleN 0
#eval doubleN 5

/-
### Multiplication

Multiplication can be defined as repeated addition:

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
Read the recursive case from the inside out:

    mulN n m'

computes `n * m'`.  We then add one more copy of `n`:

    addN (mulN n m') n

The structure of the program mirrors the mathematical definition.

-/

/-
### Exponentiation

Exponentiation is repeated multiplication, recursively on the exponent:

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
### Factorial

The factorial function is defined mathematically by

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
The recursive call `factorial n` is again on a smaller natural number.

The examples above illustrate a general principle:

* inductive data suggest recursive definitions;
* recursive definitions reduce inductive data until a base case is reached.

-/

end Recursion


section Exercises_after_recursion

/-
## Exercises

Before continuing, solve these small exercises.  They reinforce pattern
matching and recursion.

-/

/-
__Exercise__ (`tripleN`): define a function `tripleN` that computes three times
its argument.  Reuse `doubleN` and `addN` instead of writing a recursive
definition.
-/

def tripleN (n : Nat) : Nat :=
  sorry

example : tripleN 0 = 0  := by sorry
example : tripleN 4 = 12 := by sorry

/-
__Exercise__ (`sumUpTo`): define `sumUpTo` recursively so that

    sumUpTo 0       = 0
    sumUpTo (n + 1) = (n + 1) + sumUpTo n

For instance, `sumUpTo 4` is `4 + 3 + 2 + 1 + 0`.
You may use Lean's built-in `+` here.
-/

def sumUpTo (n : Nat) : Nat :=
  sorry

example : sumUpTo 0 = 0   := by sorry
example : sumUpTo 4 = 10  := by sorry
example : sumUpTo 10 = 55 := by sorry

/-
__Exercise__ (`fibN`): define the Fibonacci function:

    fibN 0       = 0
    fibN 1       = 1
    fibN (n + 2) = fibN n + fibN (n + 1)

Observe that this definition has two base cases and *two* recursive calls.
Lean accepts it because both calls are on smaller arguments.
-/

def fibN (n : Nat) : Nat :=
  sorry

example : fibN 0 = 0    := by sorry
example : fibN 1 = 1    := by sorry
example : fibN 7 = 13   := by sorry
example : fibN 10 = 55  := by sorry

end Exercises_after_recursion


section Comparing_numbers

/-
## Comparing numbers

Functions with several arguments can match on several arguments at once.
Here are three classic examples:

* `eqN n m` tests whether `n` and `m` are equal;
* `leN n m` tests whether `n` is less than or equal to `m`;
* `subN n m` computes `n - m`, stopping at zero.

Each of the first two returns a `Bool`, so we will be able to use them as
conditions of an `if`.  In the patterns below, `_ + 1` means "any successor,
whose predecessor we do not need to name".
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
In each case the last equation removes one constructor from *both* arguments.
Hence the recursive call is on smaller arguments.

Lean also provides built-in comparisons: `==` computes a `Bool`, and `≤`, `<`
are statements that Lean can decide, so they can be used directly in an `if`:
-/

#eval 3 == 3
#eval if 3 ≤ 5 then "yes" else "no"

/-
__Exercise__ (`ltN`): define `ltN n m`, which tests whether `n < m`.
Hint: `n < m` holds exactly when `n + 1 ≤ m`.  Reuse `leN`.
-/

def ltN (n m : Nat) : Bool :=
  sorry

example : ltN 2 3 = true  := by sorry
example : ltN 3 3 = false := by sorry
example : ltN 4 3 = false := by sorry

end Comparing_numbers


section Conditionals_with_Nat

/-
## Conditional expressions with natural numbers

The conditional expression from the previous lecture is still useful.
Remember that `if` is an expression: it computes a value.

Now we can combine it with a Boolean-valued function on natural numbers.
For example, `isEven n` returns a `Bool`, so it can be used as the condition
of an `if`.
-/

def nextIfEven (n : Nat) : Nat :=
  if isEven n then Nat.succ n else n

#eval nextIfEven 0
#eval nextIfEven 1
#eval nextIfEven 2
#eval nextIfEven 7

/-
This is a useful reminder that pattern matching and `if` are complementary:

* use pattern matching when you want to describe the different constructors
  of a datatype;
* use `if` when you already have a Boolean condition and want to choose
  between two results.

Here `leN` provides the condition:
-/

def minN (n m : Nat) : Nat :=
  if leN n m then n else m

#eval minN 3 8
#eval minN 9 4

/-
Conditionals can be chained with `else if`.  The following function computes
a description of a number as a `String`.
-/

def describe (n : Nat) : String :=
  if eqN n 0 then "zero"
  else if isEven n then "even"
  else "odd"

#eval describe 0
#eval describe 7
#eval describe 10

/-
One more example, mixing our own functions with Lean's built-in operations.
The *Collatz step* halves an even number, and maps an odd number `n` to
`3n + 1`.  Repeating this step is the subject of a famous open problem!
-/

def collatzStep (n : Nat) : Nat :=
  if isEven n then n / 2 else 3 * n + 1

#eval collatzStep 6
#eval collatzStep 7

/-
__Exercise__ (`zeroIfEven`): define `zeroIfEven` so that it returns `0` for even
inputs and returns the original number for odd inputs.
-/

def zeroIfEven (n : Nat) : Nat :=
  sorry

example : zeroIfEven 4 = 0 := by sorry
example : zeroIfEven 5 = 5 := by sorry

/-
__Exercise__ (`maxN`): define `maxN n m`, the larger of two numbers, using `if`
and `leN`.
-/

def maxN (n m : Nat) : Nat :=
  sorry

example : maxN 3 8 = 8 := by sorry
example : maxN 9 4 = 9 := by sorry
example : maxN 5 5 = 5 := by sorry

end Conditionals_with_Nat


section Higher_order_functions

/-
## Functions as values: now with natural numbers

In the previous lecture, we saw that functions are values and can be passed as
arguments.  With natural numbers this idea becomes much more interesting,
because we can use higher-order functions to describe repeated computation.

A *higher-order function* is a function that takes another function as an
argument, returns a function, or both.

First, the simplest example: apply a function twice.
-/

def applyTwiceN (f : Nat → Nat) (n : Nat) : Nat :=
  f (f n)

#check applyTwiceN
#eval applyTwiceN Nat.succ 5
#eval applyTwiceN doubleN 3

/-
The parameter `f` has a function type:

    Nat → Nat

It is used just like any other value.  In `applyTwiceN f n`, the expression
`f n` computes one application, and `f (f n)` computes two applications.

-/

/-
We can pass an anonymous function too.
-/

#eval applyTwiceN (fun n : Nat => n + 1) 5
#eval applyTwiceN (fun n : Nat => n * 2) 3

/-
The anonymous function

    fun n : Nat => n + 1

has type `Nat → Nat`.

As in the previous lecture, the parameter type can often be inferred in a
context where Lean already knows the expected function type.  Lean also has a
shorter notation: a dot `·` marks the missing argument, so `(· + 1)` means
`fun x => x + 1`.
-/

#check (fun n : Nat => n + 1)
#eval applyTwiceN (fun n => n * 2) 3
#eval applyTwiceN (· + 10) 1

/-
### Repeating a function

`applyTwiceN` always repeats exactly two times.  We can generalize it by using
a natural number to say how many times the function should be applied.
This is the functional counterpart of a `for` loop that runs `k` times:

    for i in 1 .. k do
        n := f n
    return n

The base case is important:

    applying a function zero times leaves the input unchanged.

For the successor case, we apply the function `k'` times and then apply it
once more.
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
There are three roles in `iterateN`:

* `f` is the operation we want to repeat;
* `k` says how many times to repeat it;
* `n` is the starting value.

For example, here is how Lean unfolds a call with `k = 3`:

    iterateN f 3 n
    = f (iterateN f 2 n)
    = f (f (iterateN f 1 n))
    = f (f (f (iterateN f 0 n)))
    = f (f (f n))

This is a typical higher-order functional-programming pattern: recursion is
used to control repetition, while the actual operation is supplied as data.

(One could also define `iterateN` by calling itself on `f n`, instead of
applying `f` at the end.  The results are the same, but proofs about the
version above turn out to be a bit simpler.)

-/

/-
We can recover `applyTwiceN` from `iterateN`:
-/

def applyTwiceN₂ (f : Nat → Nat) (n : Nat) : Nat :=
  iterateN f 2 n

#eval applyTwiceN₂ Nat.succ 5
#eval applyTwiceN₂ doubleN 3

/-
Since `iterateN` takes any function of type `Nat → Nat`, we can use it with
the Collatz step defined above.  Starting from 6, five steps give

    6 -> 3 -> 10 -> 5 -> 16 -> 8
-/

#eval iterateN collatzStep 5 6

/-
### Partial application

Recall from the previous lecture that function types associate to the right.
Thus

    Nat → Nat → Nat

means

    Nat → (Nat → Nat)

A function can therefore be given its arguments one at a time.

For example, `addN 5` is itself a function from natural numbers to natural
numbers: it adds 5 to its argument.
-/

#check addN 5
#eval (addN 5) 3
#eval (addN 10) 2

/-
We can give a name to this partially applied function.
-/

def addFive : Nat → Nat :=
  addN 5

#check addFive
#eval addFive 0
#eval addFive 7

/-
This is another central functional-programming idea: functions are ordinary
values, so we can store a partially applied function in a name and pass it to
another function.
-/

#eval iterateN addFive 3 0

/-
__Exercise__ (`addTen`): define `addTen` by partial application of `addN`.
Then use it with `iterateN`: applying `addTen` three times to 10 must give 40.
-/

def addTen : Nat → Nat :=
  sorry

example : addTen 5 = 15 := by sorry
example : iterateN addTen 3 10 = 40 := by sorry

end Higher_order_functions


section Functions_returning_functions

/-
## Functions that return functions

We can also define functions that *return* functions.

For example, `makeAdder a` returns a function that adds `a` to its argument.
-/

def makeAdder (a : Nat) : Nat → Nat :=
  fun n => addN a n

#check makeAdder
#check makeAdder 7
#eval makeAdder 7 3

/-
Because `makeAdder 7` is a function, we can pass it directly to `iterateN`.
-/

#eval iterateN (makeAdder 2) 5 0

/-
This style is useful when a computation has a fixed parameter and a parameter
that will be supplied later.  (Of course, `makeAdder a` behaves exactly like
the partial application `addN a`.)

The same idea works with multiplication.
-/

def makeMultiplier (a : Nat) : Nat → Nat :=
  fun n => mulN a n

#eval makeMultiplier 3 4
#eval iterateN (makeMultiplier 2) 4 1

/-
The last expression starts at 1 and doubles four times:

    1 -> 2 -> 4 -> 8 -> 16

So higher-order functions let us describe a process without hard-coding the
operation into the process itself.

-/

/-
__Exercise__ (`makePower`): define `makePower e`, which returns the function
that raises its argument to the power `e`.  For instance, `makePower 2` is the
squaring function.  Reuse `powN`.

Then predict, and check with `#eval`, the value of `iterateN (makePower 2) 3 2`.
-/

def makePower (e : Nat) : Nat → Nat :=
  sorry

example : makePower 2 5 = 25 := by sorry
example : makePower 3 2 = 8  := by sorry
example : makePower 0 9 = 1  := by sorry

/-
### Composition

Another standard higher-order operation is function composition.
Given

    f : Nat → Nat
    g : Nat → Nat

we can build a new function that first applies `g` and then `f`.
-/

def composeN (f g : Nat → Nat) : Nat → Nat :=
  fun n => f (g n)

#check composeN
#eval composeN Nat.succ doubleN 3
#eval composeN doubleN Nat.succ 3

/-
The first result is 7 and the second is 8: the order matters.  In general:

    composeN f g n = f (g n)

so `g` is applied first.

Lean has a built-in composition operator, written `∘` (type `\comp`):
-/

#eval ((fun n : Nat => n + 1) ∘ (fun n : Nat => n * 2)) 5

/-
__Exercise__ (composition): write an expression, without defining a new named
function, that applies `doubleN` and then `Nat.succ` to the number 5.  Evaluate it
with `#eval`; the result should be 11.  Find two different ways to write it.
-/

end Functions_returning_functions


section Higher_order_functions_over_ranges

/-
## Higher-order functions that loop over numbers

Natural numbers can also describe *how many times* or *over which range* a
computation happens.  In an imperative language we would write a loop such as

    total := 0
    for i in 0 .. n-1 do
        total := total + f i
    return total

The functional version is a recursive function that takes `f` as an argument.
-/

def sumBelow (f : Nat → Nat) (n : Nat) : Nat :=
  match n with
  | 0      => 0
  | n' + 1 => sumBelow f n' + f n'

/-
`sumBelow f n` computes `f 0 + f 1 + ... + f (n-1)`.  Different choices of `f`
give different sums:
-/

#eval sumBelow (fun i => i) 5          -- 0 + 1 + 2 + 3 + 4
#eval sumBelow (fun i => i * i) 4      -- 0 + 1 + 4 + 9
#eval sumBelow (fun _ => 1) 7          -- counts the terms

/-
The next function combines recursion, `if`, and a *predicate*: a function that
returns a `Bool`.  It counts how many numbers below `n` satisfy the predicate.
-/

def countBelow (p : Nat → Bool) (n : Nat) : Nat :=
  match n with
  | 0      => 0
  | n' + 1 => if p n' then countBelow p n' + 1 else countBelow p n'

#eval countBelow isEven 10                 -- 0, 2, 4, 6, 8
#eval countBelow (fun i => leN 3 i) 10     -- 3, 4, ..., 9

/-
Notice that we passed our own function `isEven` as an argument.  Functions
we define are ordinary values, usable everywhere.

-/

/-
__Exercise__ (`anyBelow`): define `anyBelow p n`, which returns `true` if *some*
number below `n` satisfies the predicate `p`, and `false` otherwise.
Use `if` in the recursive case.
-/

def anyBelow (p : Nat → Bool) (n : Nat) : Bool :=
  sorry

example : anyBelow (fun i => eqN i 3) 5 = true := by sorry
example : anyBelow (fun i => eqN i 7) 5 = false := by sorry
example : anyBelow isEven 0 = false := by sorry

/-
__Exercise__ (`sumOfSquares`): define `sumOfSquares n`, the sum of the squares
of the numbers below `n`, by reusing `sumBelow` with an anonymous function.
-/

def sumOfSquares (n : Nat) : Nat :=
  sorry

example : sumOfSquares 0 = 0 := by sorry
example : sumOfSquares 4 = 14 := by sorry

end Higher_order_functions_over_ranges


section Arithmetic_by_iteration

/-
## Arithmetic as iteration

We can combine the ideas from the lecture.  Arithmetic operations are
repeated applications of simpler ones:

* adding `m` means taking the successor `m` times;
* multiplying by `m` means adding `n` repeatedly, `m` times, starting from 0;
* raising to the power `e` means multiplying by `b` repeatedly, `e` times,
  starting from 1.

Using `iterateN`, each of these is a one-line definition.  The operation that
is repeated is passed explicitly, often by partial application or by an
anonymous function.
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
This is an example of two different implementations expressing the same idea:

* `powN` follows the usual recursive mathematical definition of exponentiation;
* `powByIterate` separates the control of repetition (`iterateN`) from the
  operation being repeated (`mulN b`).

The second definition is particularly interesting from a functional-programming
point of view because the operation is passed explicitly as a function.
We will prove below that, for `addN` and `powN`, the two styles agree.

-/

end Arithmetic_by_iteration


section Proofs_by_simplification

/-
Most proofs we have seen so far just compute functions on concrete values and check equality:
-/

example : addN 1 1 = 2 := by rfl

/-
Here the tactic `rfl` works because both sides reduce by computation to the same number.
-/

/-
The definition of `addN` recurses on its *second* argument.  So the following
two equations can be read directly off the definition, and `rfl` proves them
even though `n` and `m` are arbitrary natural numbers.
-/

theorem addN_zero (n : Nat) : addN n 0 = n := by
  rfl

theorem addN_succ (n m : Nat) : addN n (m + 1) = (addN n m) + 1 := by
  rfl

/-
Similarly for multiplication:
-/

theorem mulN_succ (n m : Nat) : mulN n (m + 1) = addN (mulN n m) n := by
  rfl

/-
__Exercise__: prove the corresponding theorem for `mulN` and zero on the right.
-/

theorem mulN_zero (n : Nat) : mulN n 0 = 0 := by
  sorry

end Proofs_by_simplification



section Proofs_by_rewriting

/-
### Rewriting

Theorems are not only to be proved: they can be *used*.  The tactic `rw [h]`,
where `h` is an equation `a = b`, replaces `a` by `b` in the goal.  If the goal
becomes of the form `x = x`, `rw` closes it automatically.
-/

theorem succ_addN_zero : ∀ n : Nat, Nat.succ (addN n 0) = Nat.succ n := by
  intros n
  rw [addN_zero]    --- addN n 0 = n


/- bart: TODO COMMENT?? -/
theorem plus_id_example : ∀ n m : Nat,
  n = m →
  n + n = m + m := by
  intros n m        --- choose names for universally quantified variables
  intros h          --- move the antecedent of the implication into the hypotheses
  rw [h]            --- rewrite h in the goal using the hypothesis h

/-
### Facts that do *not* hold by computation

What about the symmetric statement

    addN 0 n = n

where `n` is an arbitrary natural number?  The expression `addN 0 n` cannot
be computed until we know which natural number `n` is, because `addN` inspects
its second argument.  If you try

    example (n : Nat) : addN 0 n = n := by
      rfl

Lean reports an error.  We need a new idea: reason by *cases* or by *induction*.

-/

/-
### Case analysis

The `cases` tactic is the proof analogue of pattern matching.  For a natural
number `n` there are two cases:

* `n = 0`;
* `n = k + 1` for some natural number `k`.

Lean creates one goal for each case.  Consider the statement that `leN n 0` is
true exactly when `n` is zero, expressed by comparing it with `isZero n`.  Neither
side can be computed while `n` is unknown, but each case can be.
-/

theorem leN_zero_right (n : Nat) : leN n 0 = isZero n := by
  cases n with
  | zero   => rfl
  | succ _ => rfl

/-
After `cases n with`, we write one alternative for each constructor.  In the
`succ` case Lean would give a name to the number inside the successor; here
we do not need it, so we write `_`.

__Exercise__: prove in the same way that `isZero n = eqN n 0`.
-/

theorem isZero_eq_eqN (n : Nat) : isZero n = eqN n 0 := by
  sorry

end Proofs_by_rewriting


section Induction

/-
## Induction: the proof counterpart of recursion

Case analysis is not enough for `addN 0 n = n`: in the successor case we
get the goal for `k + 1`, but to solve it we need to know the result for `k`.
This is exactly what *mathematical induction* provides.

Suppose we want to prove a property `P n` for every natural number `n`.
The induction principle says that it is enough to prove:

1. `P 0`                       -- the base case;
2. `P n -> P (n + 1)`          -- the successor case.

The second part says that if the property is true for an arbitrary `n`, then
it is true for its successor.

In Lean, the `induction` tactic exposes exactly these cases.  In the successor
case, we also get the *induction hypothesis* `ih`: the statement for the smaller
number.

-/

theorem zero_addN (n : Nat) : addN 0 n = n := by
  induction n with
  | zero => rfl
  | succ n' ih => rw [addN_succ, ih]

/-
Let us follow the proof.  After `induction n with`, Lean shows two goals:

    case zero:   addN 0 0 = 0
    case succ:   ih : addN 0 n' = n'
                 ⊢ addN 0 (n' + 1) = n' + 1

* The first goal follows by computation, so `rfl` works.
* In the second goal, `rw [addN_succ]` rewrites `addN 0 (n' + 1)` into
  `addN 0 n' + 1`.  Then `rw [ih]` replaces `addN 0 n'` by `n'`, and the goal
  becomes `n' + 1 = n' + 1`, which `rw` closes by itself.

This is a very important correspondence:

    PROGRAMMING                  PROVING
    ------------------------------------------------
    match n with ...             cases n with ...
    recursive call on n'         induction hypothesis about n'
    base case                    base case
    recursive case               successor case

The proof has the same shape as the recursive function it talks about.

-/

/-
Another example, with the successor on the *left* of an addition.  We induct
on `m`, since `addN` is recursive on its second argument.
-/

theorem addN_succ_left (n m : Nat) : addN (n + 1) m = addN n m + 1 := by
  induction m with
  | zero => rfl
  | succ m' ih => rw [addN_succ, addN_succ, ih]

/-
The first `rw [addN_succ]` unfolds one of the two additions, the second one
unfolds the other, and `ih` finishes the job.

Tactic proofs of this shape are often written in a shorter way using `simp`,
which repeatedly rewrites using the definitions and lemmas we give it.  For
example, the successor case above could be written

    | succ m' ih => simp [addN, ih]

We will use both styles.  The explicit `rw` version is better for understanding
the proof, `simp` is faster to write.

-/

/-
We can now prove commutativity of our addition function.  This is a slightly
larger proof, and it shows how earlier lemmas are reused.
-/

theorem addN_comm (n m : Nat) : addN n m = addN m n := by
  induction m with
  | zero => rw [addN_zero, zero_addN]
  | succ m' ih => rw [addN_succ, addN_succ_left, ih]

/-
The proof above is a useful milestone.  We have gone from a short recursive
program to a mathematical property about the program, and Lean has checked the
proof mechanically.

We do not need to know every tactic in Lean to do this.  A small toolkit is
already enough for many elementary proofs:

* `rfl`       -- close an equality that follows by computation;
* `rw [h]`    -- rewrite the goal using the equation `h`;
* `simp`      -- repeatedly simplify using definitions and known lemmas;
* `cases`     -- split an inductive value into its constructors;
* `induction` -- reason recursively about an inductive value.

-/

/-
__Exercise__ (`zero_mulN`): prove that `mulN 0 n = 0`.

Hint: induction on `n`.  The successor case needs `mulN_succ`, `addN_zero`, and
the induction hypothesis `ih`.  You can use them with `rw [...]` or inside
`simp [...]`.
-/

theorem zero_mulN (n : Nat) : mulN 0 n = 0 := by
  sorry

end Induction


section Proofs_about_higher_order_functions

/-
## Proving facts about higher-order functions

Higher-order functions are ordinary functions, so we can reason about them in
the same way.

First, `applyTwiceN` is just `iterateN` with two repetitions.  Both sides compute
to `f (f n)`, so `rfl` suffices:
-/

theorem applyTwiceN_eq_iterateN (f : Nat → Nat) (n : Nat) :
    applyTwiceN f n = iterateN f 2 n := by
  rfl

/-
Second, we prove what we claimed in the section on arithmetic by iteration:
adding `m` really is taking the successor `m` times.  The statement is about
an arbitrary number `m`, hence we use induction.
-/

theorem iterate_succ (n m : Nat) : iterateN Nat.succ m n = addN n m := by
  induction m with
  | zero => rfl
  | succ m' ih => simp [iterateN, addN, ih]

/-
Here `simp` unfolds both sides of the successor case, rewrites with `ih`, and
the two sides become identical.

The same proof structure works for powers.  Repeatedly multiplying by `b`,
starting from 1, is exponentiation: the two implementations `powByIterate`
and `powN` agree.
-/

theorem iterate_mulN (b e : Nat) : iterateN (mulN b) e 1 = powN b e := by
  induction e with
  | zero => rfl
  | succ e' ih => simp [iterateN, powN, ih]

/-
Notice how these theorems connect what we have learned: recursion defines
`iterateN`, higher-order arguments describe the repeated operation, and
induction proves that the result coincides with the direct definition.

-/

end Proofs_about_higher_order_functions


section Exercises

/-
## Exercises

The following exercises collect the main ideas of the lecture.
Try to solve them without looking back at the earlier definitions first.

As before, programming exercises come with tests (or `#eval` lines whose
expected result is given in a comment).  For proofs, Lean accepts the
exercise when `sorry` has been replaced by a complete proof.

-/

/-
### Exercise 1: repeated addition as a higher-order function

Define `repeatAdd k a`, a *function* that adds `a` to its argument, `k` times.
Its type should have the form

    Nat → Nat → Nat → Nat

Use `iterateN` and partial application (or an anonymous function).
-/

def repeatAdd (k a : Nat) : Nat → Nat :=
  sorry

example : repeatAdd 3 5 10 = 25 := by sorry
example : repeatAdd 0 5 10 = 10 := by sorry

/-
### Exercise 2: powers of two

Define `powerOfTwo k`, which computes `2 ^ k` by iterating `doubleN` starting
from 1.  Do not use `powN`.
-/

def powerOfTwo (k : Nat) : Nat :=
  sorry

example : powerOfTwo 0 = 1  := by sorry
example : powerOfTwo 6 = 64 := by sorry

/-
### Exercise 3: prime numbers

A number is prime when it has exactly two divisors: 1 and itself.

(a) Define `countDivisors n`, the number of divisors of `n` between 1 and `n`.

    Hint: reuse `countBelow`.  The test `d` divides `n` is `n % d == 0`.
    Since `countBelow p n` looks at the numbers `0, ..., n-1`, the divisor to
    test is `d + 1`.

(b) Define `isPrimeN n`, which is `true` exactly when `countDivisors n` is 2.
-/

def countDivisors (n : Nat) : Nat :=
  sorry

def isPrimeN (n : Nat) : Bool :=
  sorry

-- #eval countDivisors 6      -- expected: 4  (1, 2, 3, 6)
-- #eval countDivisors 7      -- expected: 2
-- #eval countDivisors 12     -- expected: 6
-- #eval isPrimeN 0           -- expected: false
-- #eval isPrimeN 1           -- expected: false
-- #eval isPrimeN 7           -- expected: true
-- #eval isPrimeN 9           -- expected: false
-- #eval isPrimeN 13          -- expected: true

/-
### Exercise 4: compare two implementations

We have two definitions of addition, `addN` and `addN₂`.  Prove that they
compute the same function.

Hint: induction on the second argument is a natural choice.  Compare the two
definitions: the successor case should be solved by `simp [addN, addN₂, ih]`,
or by an explicit `rw`.
-/

theorem addN_eq_addN₂ (n m : Nat) : addN n m = addN₂ n m := by
  sorry

/-
### Exercise 5: iterating the identity

Prove that applying the identity function any number of times does not change
its argument.  Hint: induction on the number of iterations `k`.
-/

def identityN (n : Nat) : Nat :=
  n

theorem iterate_identity (k n : Nat) : iterateN identityN k n = n := by
  sorry

/-
### Exercise 6: composition is associative

Prove that composing three functions does not depend on how we put the
parentheses.  Both sides are functions, and they have the same definition
after unfolding `composeN`.  No induction is needed.
-/

theorem composeN_assoc (f g h : Nat → Nat) :
    composeN (composeN f g) h = composeN f (composeN g h) := by
  sorry

/-
### Exercise 7 (challenge): associativity of addition

Prove that `addN` is associative.

Hint: induction on `k`.  In the successor case, unfold the additions with
`addN_succ`, and finish with the induction hypothesis.
-/

theorem addN_assoc (n m k : Nat) :
    addN (addN n m) k = addN n (addN m k) := by
  sorry

/-
### Exercise 8: design your own function

Choose a useful function on natural numbers that can be defined recursively.
Examples include a function that counts how many times an even number can be
halved, a function computing the sum of the first `n` odd numbers, or a
higher-order function of your own invention.

Write:

1. its type;
2. its recursive definition;
3. three `#eval` examples;
4. one simple theorem about it, with a proof.

Keep the function small enough that you can understand every recursive call.

-/

end Exercises
