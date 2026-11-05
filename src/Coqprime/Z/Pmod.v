
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

From Stdlib Require Export ZArith Lia Zwf.
From Coqprime Require Export ZCmisc.

(* Compatibility with Coq versions not supporting hint localities *)
Set Warnings "-unsupported-attributes".

Local Open Scope positive_scope.

Local Open Scope P_scope.

(* [div_eucl a b] return [(q,r)] such that a = q*b + r *)
Fixpoint div_eucl (a b : positive) {struct a} : N * N :=
  match a with
  | xH => if 1 ?< b then (0%N, 1%N) else (1%N, 0%N)
  | xO a' =>
    let (q, r) := div_eucl a' b in
    match q, r with
    | N0, N0 => (0%N, 0%N) (* n'arrive jamais *)
    | N0, Npos r =>
      if (xO r) ?< b then (0%N, Npos (xO r))
      else (1%N,PminusN (xO r) b)
    | Npos q, N0 => (Npos (xO q), 0%N)
    | Npos q, Npos r =>
      if (xO r) ?< b then (Npos (xO q), Npos (xO r))
      else (Npos (xI q),PminusN (xO r) b)
    end
  | xI a' =>
    let (q, r) := div_eucl a' b in
    match q, r with
    | N0, N0 => (0%N, 0%N)                 (* Impossible *)
    | N0, Npos r =>
      if (xI r) ?< b then (0%N, Npos (xI r))
      else (1%N,PminusN (xI r) b)
    | Npos q, N0 => if 1 ?< b then (Npos (xO q), 1%N) else (Npos (xI q), 0%N)
    | Npos q, Npos r =>
      if (xI r) ?< b then (Npos (xO q), Npos (xI r))
      else (Npos (xI q),PminusN (xI r) b)
    end
  end.
Infix "/" := div_eucl : P_scope.

Open Scope Z_scope.

Lemma div_eucl_spec : forall a b,
          Zpos a = fst (a/b)%P * b + snd (a/b)%P
       /\ snd (a/b)%P < b.
Proof.
intro a; induction a as [a IHa|a IHa|]; simpl.
intros b; generalize (IHa b); destruct ((a / b)%P) as [[|q] [|r]].
  unfold fst, snd; lia.
  generalize (is_lt_spec r~1 b);destruct (r~1 ?< b).
    unfold fst, snd; lia.
    unfold fst, snd; intros; rewrite !PminusN_le; try lia.
  generalize (is_lt_spec 1 b);destruct (1 ?< b); unfold fst, snd; lia.
  generalize (is_lt_spec r~1 b);destruct (r~1 ?< b).
    unfold fst, snd; lia.
    unfold fst, snd; intros; rewrite !PminusN_le; try lia.
intros b; generalize (IHa b); destruct ((a / b)%P) as [[|q] [|r]].
  unfold fst, snd; lia.
  generalize (is_lt_spec r~0 b);destruct (r~0 ?< b).
    unfold fst, snd; lia.
    unfold fst, snd; intros; rewrite !PminusN_le; try lia.
  unfold fst, snd; lia.
  generalize (is_lt_spec r~0 b);destruct (r~0 ?< b).
    unfold fst, snd; lia.
    unfold fst, snd; intros; rewrite !PminusN_le; try lia.
intro b; destruct b; simpl; lia.
Qed.

(******** Definition du modulo ************)

(* [mod a b] return [a] modulo [b] *)
Fixpoint Pmod (a b : positive) {struct a} : N :=
  match a with
  | xH => if 1 ?< b then 1%N else 0%N
  | xO a' =>
    let r := Pmod a' b in
    match r with
    | N0 => 0%N
    | Npos r' =>
      if (xO r') ?< b then Npos (xO r')
      else PminusN (xO r') b
    end
  | xI a' =>
    let r := Pmod a' b in
    match r with
    | N0 => if 1 ?< b then 1%N else 0%N
    | Npos r' =>
      if (xI r') ?< b then Npos (xI r')
      else PminusN (xI r') b
    end
  end.

Infix "mod" := Pmod (at level 40, no associativity) : P_scope.
Local Open Scope P_scope.

Lemma Pmod_div_eucl : forall a b, a mod b = snd (a/b).
Proof.
 intros a b;generalize a;clear a;induction a;simpl;
 try (rewrite IHa;
  assert (H1 := div_eucl_spec a b); destruct (a/b) as [q r];
  destruct q as [|q];destruct r as [|r];simpl in *;
  match goal with
   | [|- context [ ?xx ?< b ]] =>
      assert (H2 := is_lt_spec xx b);destruct (xx ?< b)
  | _ => idtac
  end;simpl); auto.
 destruct H1 as [H3 H4];discriminate H3.
 destruct (1 ?< b); simpl; auto.
Qed.

Lemma mod1: forall a, a mod 1 = 0%N.
Proof. induction a;simpl;try rewrite IHa;trivial. Qed.

Lemma mod_a_a_0 : forall a, a mod a = N0.
Proof.
 intros a;generalize (div_eucl_spec a a);rewrite <- Pmod_div_eucl.
 destruct (fst (a / a));unfold Z_of_N at 1.
 rewrite Zmult_0_l;intros (H1,H2);exfalso;lia.
 assert (a<=p*a).
  pattern (Zpos a) at 1;rewrite <- (Zmult_1_l a).
  assert (H1:= Zlt_0_pos p);assert (H2:= Zle_0_pos a);
   apply Zmult_le_compat;trivial;try lia.
 destruct (a mod a)%P;auto with zarith.
 unfold Z_of_N;assert (H1:= Zlt_0_pos p0);intros (H2,H3);exfalso;lia.
Qed.

Lemma mod_le_2r : forall (a b r: positive) (q:N),
                    Zpos a = b*q + r -> b <= a -> r < b -> 2*r <= a.
Proof.
 intros a b r q H0 H1 H2.
 assert (H3:=Zlt_0_pos a). assert (H4:=Zlt_0_pos b). assert (H5:=Zlt_0_pos r).
 destruct q as [|q].  rewrite Zmult_0_r in H0. exfalso;lia.
 assert (H6:=Zlt_0_pos q).  unfold Z_of_N in H0.
 assert (Zpos r = a - b*q). lia.
 simpl;zsimpl. pattern r at 2;rewrite H.
 assert (b <= b * q).
  pattern (Zpos b) at 1;rewrite <- (Zmult_1_r b).
  apply Zmult_le_compat;try lia.
 apply Z.le_trans with (a - b * q + b). lia.
 apply Z.le_trans with (a - b + b);lia.
Qed.

Lemma mod_lt : forall a b r, a mod b = Npos r -> r < b.
Proof.
 intros a b r H;generalize (div_eucl_spec a b);rewrite <- Pmod_div_eucl;
  rewrite H;simpl;intros (H1,H2);lia.
Qed.

Lemma mod_le : forall a b r, a mod b = Npos r -> r <= b.
Proof. intros a b r H;assert (H1:= mod_lt _ _ _ H);lia. Qed.

Lemma mod_le_a : forall a b r, a mod b = r -> r <= a.
Proof.
 intros a b r H;generalize (div_eucl_spec a b);rewrite <- Pmod_div_eucl;
  rewrite H;simpl;intros (H1,H2).
 assert (0 <= fst (a / b) * b).
  destruct (fst (a / b));simpl;auto with zarith.
 auto with zarith.
Qed.

Lemma lt_mod : forall a b, Zpos a < Zpos b -> (a mod b)%P = Npos a.
Proof.
  intros a b H; rewrite Pmod_div_eucl. case (div_eucl_spec a b).
  assert (0 <= snd(a/b)). destruct (snd(a/b));simpl;auto with zarith.
  destruct (fst (a/b)).
  unfold Z_of_N at 1;rewrite Zmult_0_l;rewrite Zplus_0_l.
  destruct (snd (a/b));simpl; intros H1 H2;inversion H1;trivial.
  unfold Z_of_N at 1;assert (b <= p*b).
  pattern (Zpos b) at 1; rewrite <- (Zmult_1_l (Zpos b)).
   assert (H1 := Zlt_0_pos p);apply Zmult_le_compat;try lia.
  lia.
Qed.

Fixpoint gcd_log2 (a b c:positive) {struct c}: option positive :=
 match a mod b with
 | N0  => Some b
 | Npos r =>
   match b mod r, c with
   | N0, _ => Some r
   | Npos r', xH    => None
   | Npos r', xO c' => gcd_log2 r r' c'
   | Npos r', xI c' => gcd_log2 r r' c'
   end
 end.

Fixpoint egcd_log2 (a b c:positive) {struct c}:
    option (Z * Z * positive) :=
 match a/b with
 |    (_, N0)  => Some (0, 1, b)
 | (q, Npos r) =>
   match b/r, c with
   | (_, N0), _ => Some (1, -q, r)
   | (q', Npos r'), xH    => None
   | (q', Npos r'), xO c' =>
        match egcd_log2 r r' c' with
          None => None
        | Some (u', v', w') =>
               let u := u' - v' * q' in
               Some (u, v' - q * u, w')
        end
   | (q', Npos r'), xI c' =>
        match egcd_log2 r r' c' with
          None => None
        | Some (u', v', w') =>
               let u := u' - v' * q' in
               Some (u, v' - q * u, w')
        end
   end
 end.

Lemma egcd_gcd_log2: forall c a b,
  match egcd_log2 a b c, gcd_log2 a b c with
    None, None => True
  | Some (u,v,r), Some r' => r = r'
  | _, _ => False
  end.
Proof.
induction c; simpl; auto; try
 (intros a b; generalize (Pmod_div_eucl a b); case (a/b); simpl;
  intros q r1 H; subst; case (a mod b); auto;
  intros r; generalize (Pmod_div_eucl b r); case (b/r); simpl;
  intros q' r1 H; subst; case (b mod r); auto;
  intros r'; generalize (IHc r r'); case egcd_log2; auto;
  intros ((p1,p2),p3); case gcd_log2; auto).
Qed.

Ltac rew l :=
  match l with
   | (?r, ?r1) =>
       match type of r with
         True => rewrite <- r1
      |  _ => rew r; rew r1
      end
  | ?r => rewrite r
  end.

Lemma egcd_log2_ok: forall c a b,
  match egcd_log2 a b c with
    None => True
  | Some (u,v,r) => u * a + v * b = r
  end.
Proof.
induction c; simpl; auto;
 intros a b; generalize (div_eucl_spec a b); case (a/b);
  simpl fst; simpl snd; intros q r1; case r1; try (intros; ring);
  simpl; intros r (Hr1, Hr2); clear r1;
  generalize (div_eucl_spec b r); case (b/r);
  simpl fst; simpl snd; intros q' r1; case r1;
    try (intros; rewrite Hr1; ring);
  simpl; intros r' (Hr'1, Hr'2); clear r1; auto;
  generalize (IHc r r'); case egcd_log2; auto;
  intros ((u',v'),w'); case gcd_log2; auto; intros;
  rew ((I, H), Hr1, Hr'1); ring.
Qed.


Fixpoint log2 (a:positive) : positive :=
 match a with
 | xH => xH
 | xO a => Pos.succ (log2 a)
 | xI a => Pos.succ (log2 a)
 end.

Lemma gcd_log2_1: forall a c, gcd_log2  a xH c = Some xH.
Proof. destruct c;simpl;try rewrite mod1;trivial. Qed.

Lemma log2_Zle :forall a b, Zpos a <= Zpos b -> log2 a <= log2 b.
Proof.
 induction a;destruct b;zsimpl;intros;simpl; try lia;
  (assert (log2 a <= log2 b) by now apply IHa; lia); lia.
Qed.

Lemma log2_1_inv : forall a, Zpos (log2 a) = 1 -> a = xH.
Proof.
 destruct a;simpl;zsimpl;intros;trivial.
 assert (H1:= Zlt_0_pos (log2 a));exfalso;lia.
 assert (H1:= Zlt_0_pos (log2 a));exfalso;lia.
Qed.

Lemma mod_log2 :
  forall a b r:positive, a mod b = Npos r -> b <= a -> log2 r + 1 <= log2 a.
Proof.
 intros; cut (log2 (xO r) <= log2 a). simpl;zsimpl;trivial.
 apply log2_Zle.
 replace (Zpos (xO r)) with (2 * r)%Z;trivial.
 generalize (div_eucl_spec a b);rewrite <- Pmod_div_eucl;rewrite H.
 rewrite Zmult_comm;intros [H1 H2];apply mod_le_2r with b (fst (a/b));trivial.
Qed.

Lemma gcd_log2_None_aux :
  forall c a b, Zpos b <= Zpos a -> log2 b <= log2 c ->
   gcd_log2 a b c <> None.
Proof.
 induction c;simpl;intros;
 (CaseEq (a mod b);[intros Heq|intros r Heq];try (intro;discriminate));
 (CaseEq (b mod r);[intros Heq'|intros r' Heq'];try (intro;discriminate)).
 apply IHc. apply mod_le with b;trivial.
 generalize H0 (mod_log2 _ _ _ Heq' (mod_le _ _ _ Heq));zsimpl;intros;lia.
 apply IHc. apply mod_le with b;trivial.
 generalize H0 (mod_log2 _ _ _ Heq' (mod_le _ _ _ Heq));zsimpl;intros;lia.
 assert (Zpos (log2 b) = 1).
  assert (H1 := Zlt_0_pos (log2 b));lia.
 rewrite (log2_1_inv _ H1) in Heq;rewrite mod1 in Heq;discriminate Heq.
Qed.

Lemma gcd_log2_None : forall a b, Zpos b <= Zpos a -> gcd_log2 a b b <> None.
Proof. intros;apply gcd_log2_None_aux;auto with zarith. Qed.

Lemma gcd_log2_Zle :
   forall c1 c2 a b, log2 c1 <= log2 c2 ->
      gcd_log2 a b c1 <> None -> gcd_log2 a b c2 = gcd_log2 a b c1.
Proof.
 induction c1;destruct c2;simpl;intros;
   (destruct (a mod b) as [|r];[idtac | destruct (b mod r)]); auto; try lia.
 apply IHc1;trivial. generalize H;zsimpl;intros;lia.
 apply IHc1;trivial. generalize H;zsimpl;intros;lia.
 apply IHc1;trivial. generalize H;zsimpl;intros;lia.
 apply IHc1;trivial. generalize H;zsimpl;intros;lia.
 elim H0;trivial. elim H0;trivial.
Qed.

Lemma gcd_log2_Zle_log :
   forall a b c, log2 b <= log2 c -> Zpos b <= Zpos a ->
      gcd_log2 a b c = gcd_log2 a b b.
Proof.
 intros a b c H1 H2; apply gcd_log2_Zle; trivial.
 apply gcd_log2_None; trivial.
Qed.

Lemma gcd_log2_mod0 :
  forall a b c, a mod b = N0 -> gcd_log2 a b c = Some b.
Proof. intros a b c H;destruct c;simpl;rewrite H;trivial. Qed.

Lemma Zwf_pos : well_founded (fun x y => Zpos x < Zpos y).
Proof.
 unfold well_founded.
 assert (forall x a ,x = Zpos a -> Acc (fun x y : positive => x < y) a).
 intros x;assert (Hacc := Zwf_well_founded 0 x);induction Hacc;intros;subst x.
 constructor;intros. apply H0 with (Zpos y);trivial.
 split;auto with zarith.
 intros a;apply H with (Zpos a);trivial.
Qed.

Lemma gcd_log2_mod : forall a b, Zpos b <= Zpos a ->
  forall r, a mod b = Npos r -> gcd_log2 a b b = gcd_log2 b r r.
Proof.
 intros a b;generalize a;clear a; assert (Hacc := Zwf_pos b).
 induction Hacc; intros a Hle r Hmod.
 rename x into b. destruct b; unfold gcd_log2; fold gcd_log2; rewrite Hmod.
 CaseEq (xI b mod r)%P;intros. rewrite gcd_log2_mod0;trivial.
 assert (H2 := mod_le _ _ _ H1);assert (H3 := mod_lt _ _ _ Hmod);
  assert (H4 := mod_le _ _ _ Hmod).
 rewrite (gcd_log2_Zle_log r p b);trivial.
 symmetry;apply H0;trivial.
 generalize (mod_log2 _ _ _ H1 H4);simpl;zsimpl;intros;lia.
 CaseEq (xO b mod r)%P;intros. rewrite gcd_log2_mod0;trivial.
 assert (H2 := mod_le _ _ _ H1);assert (H3 := mod_lt _ _ _ Hmod);
  assert (H4 := mod_le _ _ _ Hmod).
 rewrite (gcd_log2_Zle_log r p b);trivial.
 symmetry;apply H0;trivial.
 generalize (mod_log2 _ _ _ H1 H4);simpl;zsimpl;intros;lia.
 rewrite mod1 in Hmod;discriminate Hmod.
Qed.

Lemma gcd_log2_xO_Zle :
 forall a b, Zpos b <= Zpos a -> gcd_log2 a b (xO b) = gcd_log2 a b b.
Proof.
 intros a b Hle;apply gcd_log2_Zle.
 simpl;zsimpl;auto with zarith.
 apply gcd_log2_None_aux;auto with zarith.
Qed.

Lemma gcd_log2_xO_Zlt :
 forall a b, Zpos a < Zpos b -> gcd_log2 a b (xO b) = gcd_log2 b a a.
Proof.
 intros a b H;simpl. assert (Hlt := Zlt_0_pos a).
 assert (H0 := lt_mod _ _ H).
 rewrite H0;simpl.
 CaseEq (b mod a)%P;intros;simpl.
 symmetry;apply gcd_log2_mod0;trivial.
 assert (H2 := mod_lt _ _ _ H1).
 rewrite (gcd_log2_Zle_log a p b);auto with zarith.
 symmetry;apply gcd_log2_mod;auto with zarith.
 apply log2_Zle.
 replace (Zpos p) with (Z_of_N (Npos p));trivial.
 apply mod_le_a with a;trivial.
Qed.

Lemma gcd_log2_x0 : forall a b, gcd_log2 a b (xO b) <> None.
Proof.
 intros;simpl;CaseEq (a mod b)%P;intros. intro;discriminate.
 CaseEq (b mod p)%P;intros. intro;discriminate.
 assert (H1 := mod_le_a _ _ _ H0). unfold Z_of_N in H1.
 assert (H2 := mod_le _ _ _ H0).
 apply gcd_log2_None_aux. trivial.
 apply log2_Zle. trivial.
Qed.

Lemma egcd_log2_x0 : forall a b, egcd_log2 a b (xO b) <> None.
Proof.
intros a b H; generalize (egcd_gcd_log2 (xO b) a b) (gcd_log2_x0 a b);
  rew H; case gcd_log2; auto.
Qed.

Definition gcd a b :=
  match gcd_log2 a b (xO b) with
  | Some p => p
  | None => (* can not appear *) 1%positive
  end.

Definition egcd a b :=
  match egcd_log2 a b (xO b) with
  | Some p => p
  | None => (* can not appear *) (1,1,1%positive)
  end.


Lemma gcd_mod0 : forall a b, (a mod b)%P = N0 -> gcd a b = b.
Proof.
 intros a b H;unfold gcd.
 pattern (gcd_log2 a b (xO b)) at 1;
  rewrite (gcd_log2_mod0 _ _ (xO b) H);trivial.
Qed.

Lemma gcd1 : forall a, gcd a xH = xH.
Proof. intros a;rewrite gcd_mod0;[trivial|apply mod1]. Qed.

Lemma gcd_mod : forall a b r, (a mod b)%P = Npos r ->
                     gcd a b = gcd b r.
Proof.
 intros a b r H;unfold gcd.
 assert (log2 r <= log2 (xO r)). simpl;zsimpl;lia.
 assert (H1 := mod_lt _ _ _ H).
 pattern (gcd_log2 b r (xO r)) at 1; rewrite gcd_log2_Zle_log;auto with zarith.
 destruct (Z_lt_le_dec a b) as [z|z].
 pattern (gcd_log2 a b (xO b)) at 1; rewrite gcd_log2_xO_Zlt;trivial.
 rewrite (lt_mod _ _ z) in H;inversion H.
 assert  (r <= b). lia.
 generalize (gcd_log2_None _ _ H2).
 destruct (gcd_log2 b r r);intros;trivial.
 assert (log2 b <= log2 (xO b)). simpl;zsimpl;lia.
 pattern (gcd_log2 a b (xO b)) at 1; rewrite gcd_log2_Zle_log;auto with zarith.
 pattern (gcd_log2 a b b) at 1;rewrite (gcd_log2_mod _ _ z _ H).
 assert  (r <= b). lia.
 generalize (gcd_log2_None _ _ H3).
 destruct (gcd_log2 b r r);intros;trivial.
Qed.

From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.

#[global]
Hint Rewrite  Zpos_mult times_Zmult square_Zmult Psucc_Zplus: zmisc.

Ltac mauto :=
  trivial;autorewrite with zmisc;trivial;auto with zarith.

Lemma gcd_Z_gcd : forall a b: positive, Z.gcd b a = gcd b a.
Proof.
 intros a;assert (Hacc := Zwf_pos a);induction Hacc as [a H1 H2].
 intros b.
 generalize (div_eucl_spec b a); mauto.
 rewrite <- (Pmod_div_eucl b a).
 CaseEq (b mod a)%P;[intros Heq|intros r Heq]; intros (Hb,Hlt).
 simpl in Hb;rewrite Zplus_0_r in Hb.
 rewrite Hb, Z.gcd_comm, Z.mul_comm, Z.gcd_mul_diag_l; try lia.
 rewrite (gcd_mod0 _ _ Heq); trivial; lia.
 rewrite (gcd_mod _ _ _ Heq).
 rewrite Hb, Z.add_comm, Z.gcd_comm, Z.gcd_add_mult_diag_r.
 apply H2; lia.
Qed.

Lemma egcd_Zis_gcd : forall a b:positive,
   let (uv,w) := egcd a b in
   let  (u,v) := uv in
     u * a + v * b = w /\ Z.gcd a b = w.
Proof.
 intros a b; unfold egcd.
 generalize (egcd_log2_ok (xO b) a b) (egcd_gcd_log2 (xO b) a b)
            (egcd_log2_x0 a b) (gcd_Z_gcd b a); unfold egcd, gcd.
 case egcd_log2; try (intros ((u,v),w)); case gcd_log2;
 try (intros; match goal with H: False |- _ => case H end);
 try (intros _ _ H1; case H1; auto; fail).
 intros; subst; lia.
Qed.

Definition Zgcd a b :=
  match a, b with
  | Z0, _ => Z.abs b
  | _, Z0 => Z.abs a
  | Zpos a, Zneg b => Zpos (gcd a b)
  | Zneg a, Zpos b => Zpos (gcd a b)
  | Zpos a, Zpos b => Zpos (gcd a b)
  | Zneg a, Zneg b => Zpos (gcd a b)
  end.


Lemma Zgcd_Z_gcd : forall x y, Z.gcd x y = Zgcd x y.
Proof.
 destruct x;destruct y;simpl; auto.
 now rewrite <- gcd_Z_gcd.
 now rewrite <- gcd_Z_gcd.
 now rewrite <- gcd_Z_gcd.
 now rewrite <- gcd_Z_gcd.
Qed.

Definition Zegcd a b :=
  match a, b with
  | Z0, Z0 => (0,0,0)
  | Zpos _, Z0 => (1,0,a)
  | Zneg _, Z0 => (-1,0,-a)
  | Z0, Zpos _ => (0,1,b)
  | Z0, Zneg _ => (0,-1,-b)
  | Zpos a, Zneg b =>
     match egcd a b with (u,v,w) => (u,-v, Zpos w) end
  | Zneg a, Zpos b =>
     match egcd a b with (u,v,w) => (-u,v, Zpos w) end
  | Zpos a, Zpos b =>
     match egcd a b with (u,v,w) => (u,v, Zpos w) end
  | Zneg a, Zneg b =>
     match egcd a b with (u,v,w) => (-u,-v, Zpos w) end
  end.

Lemma Zegcd_Z_gcd : forall x y,
  match Zegcd x y with
   (u, v, w) => u * x + v * y = Z.gcd x y /\ w = Z.gcd x y
  end.
Proof.
 assert (zx0: forall x, Zneg x = -x).
    simpl; auto.
 assert (zx1: forall x, -(-x) = x).
   intro x; case x; simpl; auto.
 destruct x as [|p|p];destruct y as [|q|q];simpl; try (split; [idtac|split]);
  auto; try (red; simpl; intros; discriminate); auto.
generalize (egcd_Zis_gcd p q); destruct egcd as [[u v] k].
  rewrite Pos2Z.inj_gcd; lia.
generalize (egcd_Zis_gcd p q); destruct egcd as [[u v] k].
  rewrite Pos2Z.inj_gcd; lia.
generalize (egcd_Zis_gcd p q); destruct egcd as [[u v] k].
  rewrite Pos2Z.inj_gcd; lia.
generalize (egcd_Zis_gcd p q); destruct egcd as [[u v] k].
  rewrite Pos2Z.inj_gcd; lia.
Qed.
