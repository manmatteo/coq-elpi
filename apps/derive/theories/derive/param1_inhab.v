(* Given an inductive type I and its unary parametricity translation is_I it
   generates a proof IP that "forall i : I, is_U i".

   license: GNU Lesser General Public License Version 2.1 or later
   ------------------------------------------------------------------------- *)
From elpi.apps.derive Extra Dependency "paramX_lib.elpi" as paramX.
From elpi.apps.derive Extra Dependency "param1.elpi" as param1.
From elpi.apps.derive Extra Dependency "param1_inhab.elpi" as param1_inhab.

From elpi Require Export elpi.
From elpi.apps Require Export derive.param1.

Definition is_uint63_witness x : is_uint63 x. Proof. constructor. Defined.
Register is_uint63_witness as elpi.derive.is_uint63_witness.

Definition is_float64_witness x : is_float64 x. Proof. constructor. Defined.
Register is_float64_witness as elpi.derive.is_float64_witness.

Elpi Db derive.param1.inhab.db lp:{{
type param1-inhab-db term -> term -> prop.

param1-inhab-db {{ lib:elpi.derive.is_uint63 }} {{ lib:elpi.derive.is_uint63_witness }}.
param1-inhab-db {{ lib:elpi.derive.is_float64 }} {{ lib:elpi.derive.is_float64_witness }}.

param1-inhab-db (fun `f` (prod `_` S _\ T) f\
            prod `x` S x\ prod `px` (RS x) _)
           (fun `f` (prod `_` S _\ T) f\
             fun `x` S x\
              fun `px` (RS x) _\ P f x) :-
           pi f x\
             reali T R,
             param1-inhab-db R PT,
             coq.mk-app PT [{coq.mk-app f [x]}] (P f x).

param1-inhab-db (app [Hd|Args]) (app[P|PArgs]) :-
  param1-inhab-db Hd P,
  param1-inhab-db-args Args PArgs.

type param1-inhab-db-args list term -> list term -> prop.
param1-inhab-db-args [] [].
param1-inhab-db-args [T,P|Args] [T,P,Q|PArgs] :- param1-inhab-db P Q, param1-inhab-db-args Args PArgs.
}}.

Elpi Command derive.param1.inhab.
Elpi Accumulate File paramX.
Elpi Accumulate File param1.
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1.inhab.db.
Elpi Accumulate File param1_inhab.
Elpi Accumulate lp:{{
  main [str I, str O] :- !, coq.locate I (indt GR), derive.param1.inhab.main GR O _.
  main [str I] :- !, coq.locate I (indt GR), derive.param1.inhab.main GR "_witness" _.
  main _ :- usage.

  usage :-
    coq.error "Usage: derive.param1P <inductive type name> [<output suffix>]".
}}.
Elpi Typecheck.