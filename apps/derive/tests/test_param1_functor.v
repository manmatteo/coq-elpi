From elpi.apps Require Import derive.param1_functor.

From elpi.apps.derive.tests Require Import test_derive_stdlib test_param1.
Import test_derive_stdlib.Coverage.
Import test_param1.Coverage.

Module Coverage.

Elpi derive.param1.functor is_empty.
Elpi derive.param1.functor is_unit.
Elpi derive.param1.functor is_peano.
Elpi derive.param1.functor is_option.
Elpi derive.param1.functor is_pair.
Elpi derive.param1.functor is_seq.
Elpi derive.param1.functor is_box_peano.
Elpi derive.param1.functor is_rose.
Elpi derive.param1.functor is_rose_p.
Elpi derive.param1.functor is_rose_o.
Elpi derive.param1.functor is_nest.
Fail Elpi derive.param1.functor is_w.
Elpi derive.param1.functor is_vect.
Elpi derive.param1.functor is_dyn.
Elpi derive.param1.functor is_zeta.
Elpi derive.param1.functor is_beta.
Elpi derive.param1.functor is_iota.
Elpi derive.param1.functor is_large.
Elpi derive.param1.functor is_prim_int.
Elpi derive.param1.functor is_prim_float.
Elpi derive.param1.functor is_fo_record.
Elpi derive.param1.functor is_pa_record.
Elpi derive.param1.functor is_pr_record.
Elpi derive.param1.functor is_dep_record.
Elpi derive.param1.functor is_enum.
Fail Elpi derive.param1.functor param1.is_eq.
Elpi derive.param1.functor is_bool.
Elpi derive.param1.functor is_sigma_bool.
Elpi derive.param1.functor is_ord.
Elpi derive.param1.functor is_ord2.
Elpi derive.param1.functor is_val.

End Coverage.

Local Notation func isT := (forall x, isT x -> isT x).
Local Notation func1 isT := (forall A P Q, (forall y : A, P y -> Q y) -> forall x, isT A P x -> isT A Q x).
Local Notation func2 isT := (forall A P Q, (forall y : A, P y -> Q y) -> forall A1 P1 Q1, (forall y : A1, P1 y -> Q1 y) -> forall x, isT A P A1 P1 x -> isT A Q A1 Q1 x).

Import Coverage.

Check is_empty_functor : func is_empty.
Check is_unit_functor : func is_unit.
Check is_peano_functor : func is_peano.
Check is_option_functor : func1 is_option.
Check is_pair_functor : func2 is_pair.
Check is_seq_functor : func1 is_seq.
Check is_rose_functor : func1 is_rose.
Fail Check is_nest_functor : func1 is_nest.
Fail Check is_w_functor.

Check is_vect_functor : forall A P Q, (forall y : A, P y -> Q y) -> forall i p (v : vect A i), is_vect A P i p v -> is_vect A Q i p v.
Check is_dyn_functor : func is_dyn.
Check is_zeta_functor : func1 is_zeta.
Check is_beta_functor : func1 is_beta.
Check is_iota_functor : func is_iota.
Check is_large_functor : func is_large.
Check is_prim_int_functor : func is_prim_int.
Check is_prim_float_functor : func is_prim_float.

Check is_fo_record_functor : func is_fo_record.
Check is_pa_record_functor : func1 is_pa_record.
Check is_pr_record_functor : func1 is_pr_record.
Check is_enum_functor : func is_enum.
Check is_ord_functor : forall n pn, func (is_ord n pn).
Check is_ord2_functor : forall n pn, func (is_ord2 n pn).
Check is_val_functor : func is_val.
