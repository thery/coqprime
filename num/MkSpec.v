
Require Import ZArith.
Require Import ZnZ.
Require Import ZAux.
Require Import ZDivModAux.
Require Import ZPowerAux.
Require Import Zn2Z.
Require Import Zn2Z_for_Proof.
Require Import Zn2ZProof.

Open Local Scope Z_scope.

 (* ********************************************************** *)
 (* **                    Build a 2 words spec                            *)
 (* ********************************************************** *)

Section MkSpec.
 Variable w:Set.
 Variable w_op : znz_op w.
 Variable op_spec : znz_spec w_op.

 Lemma mk_znz2_spec : znz_spec (mk_zn2z_op w_op).
 Proof.
  change (znz_spec (mk_zn2z_op_for_proof w_op)).
  apply mk_znz_spec.
  refine (spec_ww_to_Z _); auto.
  refine (spec_ww_of_pos _); auto.
  refine (spec_ww_0 _); auto.
  refine (spec_ww_1 _); auto.
  refine (spec_ww_Bm1 _); auto.
  refine (spec_ww_WW _); auto.
  refine (spec_ww_CW _); auto.
  refine (spec_ww_compare _); auto.
  refine (spec_ww_opp_c _); auto.
  refine (spec_ww_opp _);auto.
  refine (spec_ww_opp_carry _); auto.

  refine (spec_ww_succ_c _); auto.
  refine (spec_ww_add_c _); auto.
  refine (spec_ww_add_carry_c _); auto.
  refine (spec_ww_succ _); auto.
  refine (spec_ww_add _); auto.
  refine (spec_ww_add_carry _); auto.
  
  refine (spec_ww_pred_c _); auto.
  refine (spec_ww_sub_c _); auto.
  refine (spec_ww_sub_carry_c _); auto.
  refine (spec_ww_pred _); auto.
  refine (spec_ww_sub _); auto.
  refine (spec_ww_sub_carry _); auto.

  refine (spec_ww_mul_c _); auto.
  refine (spec_ww_mul _); auto.
  refine (spec_ww_square_c _); auto.
 
  refine (spec_ww_div21 _); auto.
  refine (spec_ww_divn1 _); auto.
  refine (spec_ww_div_gt _); auto.
  refine (spec_ww_div _); auto.
  refine (spec_ww_modn1 _); auto.
  refine (spec_ww_mod_gt _); auto.
  refine (spec_ww_mod _); auto.
    
  refine (spec_ww_gcd_gt _);auto.
  refine (spec_ww_gcd _);auto.

  refine (spec_ww_head0 _); auto.
  apply (spec_ww_add_mul_div op_spec); auto.
  apply (spec_ww_pos_mod op_spec); auto.
  Qed.


 Lemma mk_znz2_karatsuba_spec : znz_spec (mk_zn2z_op_karatsuba w_op).
 Proof.
  change (znz_spec (mk_zn2z_op_karatsuba_for_proof w_op)).
  apply mk_znz_spec.
  refine (spec_ww_to_Z _); auto.
  refine (spec_ww_of_pos _); auto.
  refine (spec_ww_0 _); auto.
  refine (spec_ww_1 _); auto.
  refine (spec_ww_Bm1 _); auto.
  refine (spec_ww_WW _); auto.
  refine (spec_ww_CW _); auto.
  refine (spec_ww_compare _); auto.
  refine (spec_ww_opp_c _); auto.
  refine (spec_ww_opp _);auto.
  refine (spec_ww_opp_carry _); auto.

  refine (spec_ww_succ_c _); auto.
  refine (spec_ww_add_c _); auto.
  refine (spec_ww_add_carry_c _); auto.
  refine (spec_ww_succ _); auto.
  refine (spec_ww_add _); auto.
  refine (spec_ww_add_carry _); auto.
  
  refine (spec_ww_pred_c _); auto.
  refine (spec_ww_sub_c _); auto.
  refine (spec_ww_sub_carry_c _); auto.
  refine (spec_ww_pred _); auto.
  refine (spec_ww_sub _); auto.
  refine (spec_ww_sub_carry _); auto.
 
  refine (spec_ww_karatsuba_c _); auto.
  refine (spec_ww_mul _); auto.
  refine (spec_ww_square_c _); auto.
 
  refine (spec_ww_div21 _); auto.
  refine (spec_ww_divn1 _); auto.
  refine (spec_ww_div_gt _); auto.
  refine (spec_ww_div _); auto.
  refine (spec_ww_modn1 _); auto.
  refine (spec_ww_mod_gt _); auto.
  refine (spec_ww_mod _); auto.
    
  refine (spec_ww_gcd_gt _);auto.
  refine (spec_ww_gcd _);auto.

  refine (spec_ww_head0 _); auto.
  apply (spec_ww_add_mul_div op_spec); auto.
  apply (spec_ww_pos_mod op_spec); auto.
 Qed. 

End MkSpec.
