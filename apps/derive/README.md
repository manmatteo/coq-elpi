# Derive

The `derive` command automatically synthesizes a bunch of useful lemmas
given an inductive type declaration.

## In a nutshell

```coq
From elpi.apps Require Import derive.std.
 
derive Inductive peano := Zero | Succ (p : peano).

Print peano.
(* Notation peano := peano.peano *)
Print peano.peano.
(* Inductive peano : Type :=  Zero : peano | Succ : peano -> peano *)

Eval compute in peano.eqb Zero (Succ Zero).
(* = false : bool *)

About peano.eqb_OK.
(*
peano.eqb_OK : forall x1 x2 : peano, Bool.reflect (x1 = x2) (peano.eqb x1 x2)

peano.eqb_OK is not universe polymorphic
Arguments peano.eqb_OK x1 x2
peano.eqb_OK is opaque
*)
```

See also [examples/usage.v](examples/usage.v)

:warning: The line `From elpi.apps Require Import derive.std.` sets globally 
`Uniform Inductive Parameters`.
See the [documentation of that option in the Coq reference manual](https://coq.inria.fr/refman/language/core/inductive.html#coq:flag.Uniform-Inductive-Parameters).

## Documentation

Elpi's `derive` app is a little framework to register derivations.
Currently there are 3 groups:
- `derive.std` contains well tested derivations including:
  + `eqb` and `eqbOK` generate sound boolean equality test in linear time/space, see
     [Practical and sound equality tests, automatically](https://hal.inria.fr/hal-03800154)
  + `eqbOK` generates its soundness proof in linear time/space
  + `induction` generates deep induction principles, see
     [Stronger Induction Principles for Containers](http://drops.dagstuhl.de/opus/volltexte/2019/11084/)
  + `param1` and `param2` generate the unary and binary parametricity translations
  + `map` map over a container
  + `param1_functor` functoriality lemmas (map over the param1 translation)
  + `lens` and `lens_laws` generate lenses focusing on record fields and some
    equations governing setter/setters
- `derive.legacy` contains derivations superseded by `std`:
  + `eq` and `eqOK` generate sound equality tests in quadratic time/space, see
     [Deriving proved equality tests in Coq-elpi](http://drops.dagstuhl.de/opus/volltexte/2019/11084/)
- `derive.experimental` contains derivations not suitable for mainstream use:
  + `idx2inv` generates an inductive type where indexes are replaced by
    non uniform parameters and equations


The `elpi/` directory contains the elpi files implementing various automatic
derivation of terms.  The corresponding .v files, defining the Coq commands,
are in `theories/derive/`.

Single steps of the derivation are available as separate commands.
Only the main entry point `derive` comes with an handy syntax; the other
commands have to be invoked mentioning `Elpi` and only accept an already
declared inductive as input.

## Derivations

<details><summary>std (click to expand)</summary><p>

### `map`

Map a container over its parameters. 

```coq
Elpi derive.map list.
Check list_map : forall A B, (A -> B) -> list A -> list B.
```

### `lens`
See also [theories/derive/lens.v](theories/derive/lens.v) for the `Lens` definition and the support constants `view`, `set` and `over`.
```coq
Elpi derive.lens pa_record.
Check _f3 : forall A, Lens (pa_record A) (pa_record A) peano peano. 
```

### `lens_laws`
See also [theories/derive/lens_laws.v](theories/derive/lens_laws.v) for the statements of the 4 laws (set_set, view_set, set_view, exchange).
```coq
Elpi derive.lens_laws pa_record.
Check _f3_view_set : forall A (r : pa_record A) x, view _f3 (set _f3 x r) = x.
```

### `param1`

Unary parametricity translation.

```coq
Elpi derive.param1 nat.
Print is_nat. (*
Inductive is_nat : nat -> Type :=
| is_O : is_nat 0
| is_S : forall n : nat, is_nat n -> is_nat (S n) *)
```

### `param1_functor`

```coq
Elpi derive.param1.functor is_list.
Check is_list_functor : forall A PA QA,
  (forall x, PA x -> QA x) -> forall l, is_list A PA l -> list A QA l.
```

### `param1_trivial`

```coq
Elpi derive.param1.trivial is_nat.
Check is_nat_trivial : forall x : nat, { p : is_nat x & forall q, p = q }.
Check is_nat_witness : forall x : nat, is_nat x.
```

### `induction`

Induction principle for `T` based on `is_T`

```coq
Elpi derive.induction list.
Check list_induction :
  forall (A : Type) (PA : A -> Type) P,
    P (nil A) ->
    (forall x : A, PA x -> forall xs, P xs -> P (cons A x xs)) ->
    forall l, is_list A PA l -> P l.
```

### `tag`

```coq
Elpi derive.tag peano.
Check peano_tag : peano -> positive.

```

### `fields`

```coq
Elpi derive.fields peano.
Check peano_fields_t : positive -> Type. 
Check peano_fields : forall (n:peano), peano_fields_t (peano_tag n). 
Check peano_construct : forall (p: positive),  peano_fields_t p -> Datatypes.option peano.
Check peano_constructP : forall (n:peano), peano_construct (peano_tag n) (peano_fields n) = Datatypes.Some n.
```

### `eqb`

```coq
Elpi derive.eqb peano.
Check peano_eqb : peano -> peano -> bool.

```

### `eqbcorrect`

```coq
Elpi derive.eqbcorrect peano.
Check peano_eqb_correct : forall n m, peano_eqb n m = true -> n = m.
Check peano_eqb_refl : forall n, peano_eqb n n = true.
```

### `eqbOK`

```coq
Elpi derive.eqbOK peano. 
Check peano_eqb_OK : forall n m, reflect (n = m) (peano_eqb n m).
```

### `param1_congr`

```coq
Elpi derive.param1.congr is_nat.
Check is_Succ congr : forall x (px qx : is_nat x),
  px = qx -> 
  is_Succ x px = is_Succ x qx.
```

</p></details>

<details><summary>legacy (click to expand)</summary><p>

See [Deriving proved equality tests in Coq-elpi: Stronger Induction Principles for
Containers](http://drops.dagstuhl.de/opus/volltexte/2019/11084/) for a
description of most of these components.


<img align="right" src="https://github.com/LPCIC/coq-elpi/blob/master/apps/derive/derive.svg" width="40%" />

### `isK`

Given an inductive type it generates for each constructor a function that
tests if a term is a specific constructor.

Example: 
```coq
Elpi derive.isK list.
Print list_is_nil. (*
list_is_nil = 
  fun (A : Type) (i : list A) =>
    match i with
    | nil => true
    | _ => false
    end
*)
```

### `projK`

Given an inductive type it generates for each constructor `K` and argument
`i` of this constructor a function extracting that argument (provided enough
default values).

```coq
Elpi derive.projK Vector.t.
Check projcons1. (*
projcons1 
 : forall (A : Type) (H : nat),
          A -> forall n : nat, Vector.t A n ->
          Vector.t A H -> A
```
The intended use is to perform injection, i.e. one aleady has a term of the
shape `K args` and can just use these args to provide the default values.

If the projected argument's type depends on the value of other arguments, then it
is boxed using `existT`.
```coq
Check projcons3. (*
projcons3
     : forall (A : Type) (H : nat),
       A -> forall n : nat, Vector.t A n ->
       Vector.t A H -> {i1 : nat & Vector.t A i1}
*)
```

### injection

`injection H EqAB PL` given an equation `H` of type `EqAB` returns a list
of equations `PL`. `EqAB` is expected to be of the form `K .. = K ..` for
a constructor `K`.

coverage: does not do the smart thing when the obtained equations are like `{ i : nat & Vector.t A i } = ...` in which case, given that `nat` is `eqType` one could obtain systematically the two equalities.

Note: this is not a real derivation, since it generates no constant, but it a piece of
code used by derivations.

### discriminate

`discriminate H EqAB G PG` given an equation `H` of type `EqAB` and
a goal `G` it provides a proof `PG`. It asserts that `EqAB` is of
the form `K1 .. = K2 ..` when `K1` is a constructor different from `K2`.

Note: this is not a real derivation, since it generates no constant, but it a piece of
code used by derivations.

### `bcongr`

We call a boolean congruence lemma an instance of the `reflect` predicate
on a proposition `K x1..xn = K y1..yn` and a boolean expression `b1 && .. bn`.

```coq
Elpi derive.bcongr list.
Check nil_congr : forall A, reflect (@nil A = @nil A) true.
Check cons_congr :
  forall A,
  forall (x y : A) b1, reflect (x = y) b1 ->
  forall (xs ys : list A) b2, reflect (xs = ys) b2 ->
    reflect (cons x xs = cons y ys) (b1 && b2).
```

### `eq`

Generates a boolean comparison function.

```coq
Elpi derive.eq list. 
Check list_eq. (*
list_eq
     : forall A : Type,
       (A -> A -> bool) -> list A -> list A -> bool
*)
```

### `eqK`

Generates, for each constructor, the correctness lemma for the comparison
function.

```coq
Elpi derive.eqK list.

Check eq_axiom_nil : forall A fa, axiom (list A) (list_eq A fa) (@nil A).

Check eq_axiom_cons : forall A fa,
  forall x, axiom A fa x ->
  forall xs, axiom (list A) (list_eq A fa) xs ->
    axiom (list A) (list_eq A fa) (cons x xs).
```

### `eqcorrect`

Correctness of equality test using reified type information.

```coq
Elpi derive.eqcorrect list.
Check list_eq_correct :
  forall A f l, is_list A (eq_axiom A f) l -> eq_axiom (list A) (list_eq A f) l.
```

### `eqOK`

Correctness of equality test.

```coq
Elpi derive.eqOK list.
Check list_eq_OK :
  forall A f, (forall a, axiom A f a) -> (forall l, eq_axiom (list A) (list_eq A f) l).
```

## Coverage

This is the list of inductive types we use for testing, and the table with the result of each derivation (:sunny: = OK, :bug: = does not work but might, :cloud: = looks like this can't possible work)


```coq
Inductive empty := .
Inductive unit := tt.
Inductive peano := Zero | Succ (n : peano).
Inductive option A := None | Some (_ : A).
Inductive pair A B := Comma (a : A) (b : B).
Inductive seq A := Nil | Cons (x : A) (xs : seq A).
Inductive rose (A : Type) := Leaf | Node (sib : seq (rose A)).
Inductive nest A := NilN | ConsN (x : A) (xs : nest (pair A A)).
Fail Inductive bush A := BNil | BCons (x : A) (xs : bush (bush A)).
Inductive w A := via (f : A -> w A).
Inductive vect A : peano -> Type := VNil : vect A Zero | VCons (x : A) n (xs : vect A n) : vect A (Succ n).
Inductive dyn := box (T : Type) (t : T).
Inductive zeta Sender (Receiver := Sender) := Envelope (a : Sender) (ReplyTo := a) (c : Receiver).
Inductive beta (A : (fun x : Type => x) Type) := Redex (a : (fun x : Type => x) A).
Inductive iota := Why n (a : match n in peano return Type with Zero => peano | Succ _ => unit end).
Inductive large := K1 (_ : unit) | K2 (_ : unit) (_ : unit) | ...
Inductive prim_int := PI (i : Int63.int).
Inductive prim_float := PF (f : PrimFloat.float).
Record fo_record := { f1 : peano; f2 : unit; }.
Record pa_record A := { f3 : peano; f4 : A; }.
Record pr_record A := { pf3 : peano; pf4 : A; }. (* with primitive projections *)
Record dep_record := { f5 : peano; f6 : vect unit f5; }.
Variant enum := E1 | E2 | E3.
```

test       | eq      | param1  | map     | induction | isK     | projK   | bcongr  | eqK     | eqcorrect | eqOK    | lens_laws
-----------|---------|---------|---------|-----------|---------|---------|---------|---------|-----------|---------|----------
empty      | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :cloud:
unit       | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :cloud:
peano      | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :cloud:
option     | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :cloud:
pair       | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :cloud:
seq        | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :cloud:
rose       | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :cloud:
nest       | :cloud: | :sunny: | :cloud: | :sunny:   | :sunny: | :sunny: | :sunny: | :bug:   | :bug:     | :bug:   | :cloud:
w          | :cloud: | :sunny: | :bug:   | :sunny:   | :sunny: | :sunny: | :sunny: | :bug:   | :bug:     | :bug:   | :cloud:
vect       | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :bug:   | :bug:   | :bug:     | :bug:   | :cloud:
dyn        | :cloud: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :bug:   | :bug:   | :bug:     | :bug:   | :cloud:
zeta       | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :cloud:
beta       | :sunny: | :sunny: | :bug:   | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :bug:     | :sunny: | :cloud:
iota       | :cloud: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :cloud: | :bug:   | :cloud:   | :cloud: | :cloud:
large      | :sunny: | :sunny: | :bug:   | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :cloud:
prim_int   | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :cloud:
prim_float | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :cloud:   | :cloud: | :cloud:
fo_record  | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny:
pa_record  | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny:
pr_record  | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny:
dep_record | :bug:   | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :bug:   | :bug:   | :bug:     | :bug:   | :cloud:  
enum       | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :sunny: | :sunny: | :sunny: | :sunny:   | :sunny: | :cloud:


test      | functor | inhab   | congr     | trivial |
----------|---------|---------|-----------|---------|
is_empty  | :sunny: | :sunny: | :sunny:   | :sunny: |
is_unit   | :sunny: | :sunny: | :sunny:   | :sunny: |
is_peano  | :sunny: | :sunny: | :sunny:   | :sunny: |
is_option | :sunny: | :sunny: | :sunny:   | :sunny: |
is_pair   | :sunny: | :sunny: | :sunny:   | :sunny: |
is_seq    | :sunny: | :sunny: | :sunny:   | :sunny: |
is_rose   | :sunny: | :sunny: | :sunny:   | :sunny: |
is_nest   | :bug:   | :bug:   | :cloud:   | :cloud: |
is_w      | :bug:   | :sunny: | :sunny:   | :bug:   |
is_vect   | :sunny: | :bug:   | :cloud:   | :bug:   |
is_dyn    | :sunny: | :cloud: | :cloud:   | :bug:   |
is_zeta   | :sunny: | :sunny: | :sunny:   | :sunny: |
is_beta   | :sunny: | :sunny: | :sunny:   | :sunny: |
is_iota   | :sunny: | :bug:   | :cloud:   | :bug:   |
is_large  | :sunny: | :sunny: | :bug:     | :bug:   |
is_prim_int  | :sunny: | :sunny: | :sunny:   | :sunny: |
is_is_prim_float| :sunny: | :sunny: | :sunny:   | :sunny: |
is_fo_record | :sunny: | :sunny: | :sunny:   | :sunny: |
is_pa_record | :sunny: | :sunny: | :sunny:   | :sunny: |
is_pr_record | :sunny: | :sunny: | :sunny:   | :sunny: |
is_dep_record| :sunny: | :bug:   | :sunny:   | :bug:   |
is_enum      | :sunny: | :sunny: | :sunny:   | :sunny: |

</p></details>

<details><summary>experimental (click to expand)</summary><p>


### `invert`

```coq
Inductive is_list A PA : list A -> Type :=
  | nilR : is_list (@nil A)
  | consR : forall a : A, PA a ->
            forall xs : list A, is_list xs -> is_list (cons a xs).

Elpi derive.invert is_list.
Print is_list_inv. (*
Inductive is_list_inv (A : Type) (PA : A -> Type) (idx0 : list A) : Type :=
	| nilR_inv : idx0 = nil -> is_list_inv A PA idx0
  | consR_inv : forall a : A, PA a ->
                forall xs : list A, is_list_inv A PA xs ->
                idx0 = (cons a xs) ->
                is_list_inv A PA idx0.
*)
```

## `idx2inv`

```coq
Elpi derive.idx2inv is_list.
Check is_list_to_is_list_inv :
  forall A PA l, is_list A PA l -> is_list_inv A PA l.
```

</p></details>




