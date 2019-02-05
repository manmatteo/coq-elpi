From elpi Require Import test_derive_stdlib derive.projK.

Import test_derive_stdlib.Coverage.

Module Coverage.
Elpi derive.projK empty.
Elpi derive.projK unit.
Elpi derive.projK peano.
Elpi derive.projK option.
Elpi derive.projK pair.
Elpi derive.projK seq.
Elpi derive.projK rose.
Elpi derive.projK nest.
Elpi derive.projK w.
Elpi derive.projK vect.
Elpi derive.projK dyn.
Elpi derive.projK zeta.
Elpi derive.projK beta.
Elpi derive.projK iota.
Elpi derive.projK large.
End Coverage.

Import Coverage.

Check projSucc1 : peano -> peano -> peano.
Check projSome1 : forall A, A -> option A -> A.
Check projComma1 : forall A B, A -> B -> pair A B -> A.
Check projComma2 : forall A B, A -> B -> pair A B -> B.
Check projCons1 : forall A, A -> seq A -> seq A -> A.
Check projCons2 : forall A, A -> seq A -> seq A -> seq A.
Check projLeaf1 : forall A, A -> rose A -> A.
Check projNode1 : forall A, seq (rose A) -> rose A -> seq (rose A).
Check projConsN1 : forall A, A -> nest (pair A A) -> nest A -> A.
Check projConsN2 : forall A, A -> nest (pair A A) -> nest A -> nest (pair A A).
Check projvia1 : forall A, (A -> w A) -> w A -> (A -> w A).
Check projVCons1 : forall A i, A -> forall j, vect A j -> vect A i -> A.
Check projVCons2 : forall A i, A -> forall j, vect A j -> vect A i -> peano.
Check projVCons3 : forall A i, A -> forall j, vect A j -> vect A i -> { w & vect A w }.
Check projbox1 : forall T, T -> dyn -> Type.
Check projbox2 : forall T, T -> dyn -> { T : Type & T }.
Check projEnvelope1 : forall A, A -> A -> zeta A -> A.
Check projEnvelope2 : forall A, A -> A -> zeta A -> A.
Check projRedex1 : forall A, A -> beta A -> A.
Check projWhy1 : forall n : peano, match n return Type with 
                    | Zero => peano
                    | Succ _ => unit
                    end -> iota -> peano.
Check projWhy2 : forall n : peano, match n return Type with 
                    | Zero => peano
                    | Succ _ => unit
                    end -> iota -> { i : peano & match i with Zero => peano | Succ _ => unit end }.