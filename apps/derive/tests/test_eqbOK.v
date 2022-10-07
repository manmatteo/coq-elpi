From elpi.apps Require Import derive.eqbOK.

From elpi.apps.derive.tests Require Import test_derive_stdlib test_eqb test_eqbcorrect.

Import test_derive_stdlib.Coverage 
       test_eqb.Coverage
       test_eqbcorrect.Coverage.

Module Coverage.

Elpi derive.eqbOK empty.
Elpi derive.eqbOK unit.
Elpi derive.eqbOK peano.
Elpi derive.eqbOK option.
Elpi derive.eqbOK pair.
Elpi derive.eqbOK seq.
Elpi derive.eqbOK box_peano.
Elpi derive.eqbOK rose.
Elpi derive.eqbOK rose_p.
Elpi derive.eqbOK rose_o.
Fail Elpi derive.eqbOK nest.
Fail Elpi derive.eqbOK w.
Fail Elpi derive.eqbOK vect.
Fail Elpi derive.eqbOK dyn.
Fail Elpi derive.eqbOK zeta.
Elpi derive.eqbOK beta.
Fail Elpi derive.eqbOK iota.
(*
Elpi derive.eqbOK large.
*)
Elpi derive.eqbOK prim_int.
Fail Elpi derive.eqbOK prim_float.
Elpi derive.eqbOK fo_record.
Elpi derive.eqbOK pa_record.
Elpi derive.eqbOK pr_record.
Fail Elpi derive.eqbOK dep_record.
Elpi derive.eqbOK enum.
Fail Elpi derive.eqbOK eq.
Elpi derive.eqbOK bool.
Elpi derive.eqbOK sigma_bool.

Check fun (a : peano) (eqA : eq_test2 a a)
(H : forall (x1 : _) (x2 : _), Bool.reflect (x1 = x2) (eqA x1 x2)) =>
eqb_core_defs.iffP2
(ord_eqb_correct a eqA (fun a1 a2 : a => ssrbool.elimT (H a1 a2)))
(ord_eqb_refl a eqA (fun a1 : a => ssrbool.introT (H a1 a1) eq_refl))
Elpi derive.eqbOK ord.
Elpi derive.eqbOK ord2.
Elpi derive.eqbOK val.

End Coverage.

Import Coverage.

Check peano_eqb_OK : forall n m, reflect (n = m) (peano_eqb n m).
