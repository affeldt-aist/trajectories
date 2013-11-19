Require Import BigQ.
Import BigQ.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import div finfun bigop prime binomial ssralg finset fingroup finalg.
Require Import mxalgebra perm zmodp matrix ssrint refinements funperm.
Require Import seq seqpoly pol square_free casteljau desc rat QArith.

Require Import ssrnum ssrint realalg poly.
Import GRing.

(* Viewing p1 and p2 (list of rationals as representing polynomials,
  with coefficients of lower degree appearing first. *)
Fixpoint addp (p1 p2 : seq bigQ) :=
  match p1, p2 with
  | (a :: p1'), (b :: p2') => (a + b)%bigQ::addp p1' p2'
  | [::], _ => p2
  | _, [::] => p1
  end.

Section addp_correct.

Fixpoint pos_to_R (p : positive) : realalg :=
  match p with
    xH => (1%R : realalg)
  | xO p' => (pos_to_R p' + pos_to_R p')%R
  | xI p' => (pos_to_R p' + pos_to_R p' + 1)%R
  end.

Lemma pos_to_RS :
  {morph pos_to_R : x / Pos.succ x >-> (1 + x)%R}.
elim => [x IH | x IH | ] //=; first by rewrite IH addrAC !addrA.
by rewrite addrC.
Qed.

Lemma pos_to_RD : 
  {morph pos_to_R : x y / (x + y)%positive >-> (x + y)%R}.
Proof.
by elim=> [x IH | x IH | ][y | y | ] //=; 
rewrite ?Pos.add_carry_spec ?pos_to_RS ?IH !addrA ?(addrC 1%R) ?(addrAC _ 1%R);
congr (_ + _)%R; rewrite ?(addrAC _ (pos_to_R y)).
Qed.

Lemma pos_to_RM : 
  {morph pos_to_R : x y / (x * y)%positive >-> (x * y)%R}.
Proof.
by elim=>[x IH | x IH | ] y /=;
 rewrite ?pos_to_RD /= ?IH ?mulrDl ?mul1r // addrC.
Qed.

Lemma pos_to_Rp : forall p, (0 < pos_to_R p)%R.
Proof.
elim=> [p IH | p IH | ]; rewrite /=;
  repeat apply: Num.Theory.addr_gt0 => //; apply: Num.Theory.ltr01.
Qed.

Lemma pos_to_R_lt :
  forall x y, (x < y)%positive -> (pos_to_R x < pos_to_R y)%R.
Proof.
move=> x y xy; case: (Pos.lt_iff_add x y) => t _; case: (t xy) => z <-.
by rewrite pos_to_RD -Num.Theory.subr_gt0 addrAC addrN add0r pos_to_Rp.
Qed.

Lemma pos_to_R_lt_q :
  forall x y, (x < y)%positive <-> (pos_to_R x < pos_to_R y)%R.
Proof.
move=> x y; split; first by apply: pos_to_R_lt.
move=> xy; case t : (x ?= y)%positive => //.
  by move: xy; rewrite (Pos.compare_eq _ _ t) Num.Theory.ltrr.
have t' : (pos_to_R y < pos_to_R x)%R by apply/pos_to_R_lt/Pos.gt_lt.
move: {t} t'; rewrite Num.Theory.ltrNge.
move: xy; rewrite Num.Theory.ltr_def.
by case: (pos_to_R x <= pos_to_R y)%R => //; rewrite andbF.
Qed.

Lemma pos_to_R_inj : injective pos_to_R.
Proof.
move=> x y; move/eqP=> xy ; case t: (x ?= y)%positive.
    by apply: Pos.compare_eq.
  by have := (pos_to_R_lt _ _ t); rewrite Num.Theory.ltr_def eq_sym xy negbF.
have := (pos_to_R_lt _ _ (Pos.gt_lt _ _ t)).
by rewrite Num.Theory.ltr_def xy negbF.
Qed.

Definition Z_to_R (z : Z) : realalg :=
  match z with 
    Z0 => 0%R
  | Zpos p => pos_to_R p
  | Zneg p => (-pos_to_R p)%R
  end.

Definition bigZ_to_R (z : bigZ) : realalg :=
  Z_to_R [z]%bigZ.
  
Lemma Z_to_RD :
  {morph Z_to_R : x y / (Zplus x y) >-> (x + y)%R}.
Proof.
move=> x y /=.
case hx : x => [ | p | p]; first by rewrite Z.add_0_l add0r.
  case hy : y => [ | q | q]; first by rewrite Z.add_0_r addr0.
    by rewrite /= pos_to_RD.
  rewrite /= Z.pos_sub_spec.
  case hpq : (p ?= q)%positive.
      by rewrite (Pos.compare_eq _ _ hpq) addrN.
    apply/oppr_inj/eqP; rewrite opprK opprB eq_sym subr_eq -pos_to_RD.
    by rewrite Pos.sub_add.
  apply/eqP; rewrite eq_sym subr_eq -pos_to_RD Pos.sub_add //.
  by apply: Pos.gt_lt.
case hy : y => [ | q | q]; first by rewrite Z.add_0_r addr0.
    rewrite /= Z.pos_sub_spec.
    case hpq : (q ?= p)%positive.
      by rewrite (Pos.compare_eq _ _ hpq) addNr.
    apply/oppr_inj/eqP; rewrite opprK addrC opprB eq_sym subr_eq -pos_to_RD.
    by rewrite Pos.sub_add.
  apply/eqP; rewrite eq_sym addrC subr_eq -pos_to_RD Pos.sub_add //.
  by apply: Pos.gt_lt.
by rewrite /= pos_to_RD opprD.
Qed.

Lemma Z_to_RM : {morph Z_to_R : x y / (Zmult x y) >-> (x * y)%R}.
Proof.
  move=> [| x | x] [| y | y] /=; rewrite ?pos_to_RM ?mul0r ?mulr0 ?mulrN
   ?mulNr ?opprK //.
Qed.

Lemma Z_to_RN : {morph Z_to_R : x / (Zopp x) >-> (- x)%R}.
move=> [| x | x] //=; first by rewrite oppr0.
by rewrite opprK.
Qed.

Lemma bigZ_to_RD : {morph bigZ_to_R : x y / (x + y)%bigZ >-> (x + y)%R}.
Proof.
by move=> x y /=; rewrite /bigZ_to_R BigZ.spec_add Z_to_RD.
Qed.

Lemma bigZ_to_RM : {morph bigZ_to_R : x y / (x * y)%bigZ >-> (x * y)%R}.
Proof.
by move=> x y /=; rewrite /bigZ_to_R BigZ.spec_mul Z_to_RM.
Qed.

Lemma Z_to_R_inj : injective Z_to_R.
move=>[ | x | x].
    move=> [|y | y] //=.
      move/eqP=> py.
      have : pos_to_R y != 0%R by rewrite Num.Theory.neqr_lt pos_to_Rp orbT.
      by rewrite eq_sym py.
    rewrite -oppr0;move/oppr_inj/eqP=>py.
    have : pos_to_R y != 0%R by rewrite Num.Theory.neqr_lt pos_to_Rp orbT.
    by rewrite eq_sym py.
  move=> [| y | y] //=.
      move/eqP=> py.
      have : pos_to_R x != 0%R by rewrite Num.Theory.neqr_lt pos_to_Rp orbT.
      by rewrite py.
    by move/pos_to_R_inj => ->.
  move=> t.
  have : (0 < pos_to_R x)%R by apply: pos_to_Rp.
  rewrite Num.Theory.ltrNge t Num.Theory.oppr_le0.
  by move=>h; have := pos_to_Rp y; rewrite Num.Theory.ltr_def (negbTE h) andbF.
move=>[| y | y] //=.
    move/eqP; rewrite oppr_eq0 => t.
    by have := pos_to_Rp x; rewrite Num.Theory.ltr_def t.
  move=> t; have:= pos_to_Rp y; rewrite -t {t}.
  rewrite Num.Theory.oppr_gt0 Num.Theory.ltrNge => t.
  by have := pos_to_Rp x; rewrite Num.Theory.ltr_def (negbTE t) andbF.
by move/oppr_inj/pos_to_R_inj=> ->.
Qed.
    
Definition Q_to_R (q : Q) : realalg :=
   (Z_to_R (Qnum q) / pos_to_R (Qden q))%R.

Lemma Q_to_RP : forall q1 q2, q1 == q2 <-> (Q_to_R q1 == Q_to_R q2)%B.
Proof.
move=> q1 q2; rewrite /Q_to_R.
have qd1' : (pos_to_R (Qden q1) != 0)%R.
  by rewrite Num.Theory.neqr_lt pos_to_Rp orbT.
have qd2' : (pos_to_R (Qden q2) != 0)%R.
  by rewrite Num.Theory.neqr_lt pos_to_Rp orbT.
case: q1 qd1' => x1 y1 /=; case: q2 qd2' => x2 y2 /=; rewrite /Qeq /=.
move=> qd2' qd1'; split.
  move=> prd; apply/eqP/(mulIf qd1')/(mulIf qd2').
  rewrite mulfVK // (mulrAC _ (pos_to_R y2)^-1) mulfVK //. 
  by rewrite -(Z_to_RM _ (Zpos y2)) prd Z_to_RM.
have t : (pos_to_R y1 * pos_to_R y2 != 0)%R.
  by rewrite Num.Theory.neqr_lt -pos_to_RM pos_to_Rp orbT.
move=> qf.
apply: Z_to_R_inj; rewrite !Z_to_RM /=.
apply/(mulIf (invr_neq0 t)).
by rewrite invfM // !mulrA mulfK // mulrAC mulfK //; apply/eqP.
Qed.

Definition bigQ_to_R (u : bigQ) : realalg := Q_to_R [u].

Lemma bigQ_to_RP :
  forall q1 q2, (q1 == q2)%bigQ <-> (bigQ_to_R q1 == bigQ_to_R q2)%B.
Proof.
move=> q1 q2; rewrite /eq Q_to_RP /bigQ_to_R; by split => //;  move/eqP.
Qed.

Lemma Q_to_RM : forall x y, Q_to_R (x * y) = (Q_to_R x * Q_to_R y)%R.
Proof.
move=> x y; rewrite /Q_to_R Z_to_RM pos_to_RM invfM !mulrA mulrAC.
rewrite -!mulrA; congr (_ * _)%R; rewrite !mulrA.
by rewrite -(mulrA (pos_to_R (Qden x))^-1) (mulrC _ (_ * _)%R).
Qed.

Lemma bigQ_to_RM : {morph bigQ_to_R : x y / (x * y)%bigQ >-> (x * y)%R}.
Proof.
move=> x y /=; rewrite /bigQ_to_R; rewrite -Q_to_RM. 
by apply/eqP/Q_to_RP/spec_mul. 
Qed.

Lemma Q_to_RD : forall x y, Q_to_R (x + y) = (Q_to_R x + Q_to_R y)%R.
Proof.
move=> [x xd] [y yd]; rewrite /Q_to_R /=.
have t : pos_to_R (xd * yd) != 0%R.
  by rewrite Num.Theory.neqr_lt pos_to_Rp orbT.
apply: (mulIf t); rewrite -mulrA mulVf //.
have ty : pos_to_R yd != 0%R.
  by rewrite Num.Theory.neqr_lt pos_to_Rp orbT.
have tx : pos_to_R xd != 0%R.
  by rewrite Num.Theory.neqr_lt pos_to_Rp orbT.
rewrite Pmult_comm pos_to_RM mulrA mulrDl -(mulrA (Z_to_R y)) mulVf // !mulr1.
by rewrite mulrAC mulrDl -!mulrA mulVf // mulr1 Z_to_RD !Z_to_RM.
Qed.

Lemma Q_to_RN : forall x, Q_to_R (- x) = (- Q_to_R x)%R.
Proof.
move=> [] [ | x | x ] d /=; rewrite /Q_to_R /=; first by rewrite !mul0r oppr0.
  by rewrite mulNr.
by rewrite mulNr opprK.
Qed.

Lemma bigQ_to_RD : {morph bigQ_to_R : x y / (x + y)%bigQ >-> (x + y)%R}.
Proof.
by move=> x y /=; rewrite /bigQ_to_R -Q_to_RD; apply/eqP/Q_to_RP/spec_add.
Qed.

Lemma bigQ_toRN : {morph bigQ_to_R : x / (- x)%bigQ >-> (- x)%R}.
Proof.
move=> x /=; rewrite /bigQ_to_R -Q_to_RN; apply/eqP/Q_to_RP/spec_opp.
Qed.

Lemma Q_to_RV : forall x, Q_to_R(/x) = ((Q_to_R x)^-1)%R.
Proof.
move=>[][ | x | x] d; rewrite /Q_to_R /=.
    by rewrite !mul0r invr0.
  by rewrite invfM invrK mulrC.
by rewrite invfM invrK invrN !mulNr mulrC.
Qed.

Lemma bigQ_to_RV : {morph bigQ_to_R : x / (BigQ.inv x)%bigQ >-> (x ^-1)%R}.
Proof.
move=> x /=; rewrite /bigQ_to_R -Q_to_RV; apply/eqP/Q_to_RP/spec_inv.
Qed.

Lemma Q_to_R1 : Q_to_R 1 = 1%R.
Proof. by rewrite /Q_to_R /=; rewrite invr1 mulr1. Qed.

Lemma Q_to_R0 : Q_to_R 0 = 0%R.
Proof. by rewrite /Q_to_R /=; rewrite mul0r. Qed.

Lemma bigQ_to_R0 : bigQ_to_R 0 = 0%R.
Proof. by rewrite /bigQ_to_R Q_to_R0. Qed.

Fixpoint sbQ_to_p (l : seq bigQ) : {poly realalg} :=
match l with
  nil => 0%R
| a::tl => ((bigQ_to_R a)%:P + 'X * sbQ_to_p tl)%R
end.

Lemma addpP : {morph sbQ_to_p : l1 l2 / (addp l1 l2) >-> (l1 + l2)%R}.
elim=> [ | a tl IH] l2 /=; first by rewrite add0r.
case: l2 => [ | b tl2] /=.
  by rewrite addr0.
rewrite !addrA (addrAC (bigQ_to_R a)%:P) IH mulrDr addrA bigQ_to_RD. 
by rewrite polyC_add.
Qed.

End addp_correct.

(* Multiplication by a scalar. *)
Fixpoint scal a p :=
  match p with
  | b::p' => (a * b)%bigQ::scal a p'
  | [::] => [::]
  end.

(* Multiplication between two polynomials, naive algorithm. *)
Fixpoint mulp p1 p2 :=
  match p1 with
  | a::p1' => addp (scal a p2)  (0%bigQ::mulp p1' p2)
  | [::] => [::]
  end.

Section mulp_correct.

Lemma scalP (a : bigQ) (l : seq bigQ) :
    sbQ_to_p (scal a l) = (bigQ_to_R a *: sbQ_to_p l)%R.
Proof.
elim: l =>[ | b tl IH] /=.
  by rewrite scaler0.
by rewrite scalerDr -mul_polyC -polyC_mul bigQ_to_RM scalerAr IH.
Qed.

Lemma mulpP : {morph sbQ_to_p : x y / (mulp x y) >-> (x * y)%R}.
Proof.
elim=> [ | a x IH] y /=.
  by rewrite mul0r.
by rewrite addpP scalP /= IH /bigQ_to_R Q_to_R0 add0r mulrDl mul_polyC mulrA.
Qed.

End mulp_correct.

(* Composition of two polynomials, Horner style *)
Fixpoint compp p1 p2 :=
  match p1 with
  | [::] => [::]
  | [:: a] => p1
  | a :: p1' => addp [:: a] (mulp p2 (compp p1' p2))
  end.

Section compp_correct.

Lemma comppP : {morph sbQ_to_p : x y / compp x y >-> (x \Po y)}.
Proof.
elim=>[|a p1 IH] p2 /=; first by rewrite comp_poly0.
case: p1 IH => [ | b p1] IH.
  by rewrite /= mulr0 linearD /= comp_poly0 !addr0 comp_polyC.
rewrite -[X in X = _]/(sbQ_to_p (addp [:: a] (mulp p2 (compp (b :: p1) p2)))).
rewrite addpP mulpP IH /= mulr0 addr0 {IH} !linearD /= !comp_polyC.
by rewrite !rmorphM linearD !rmorphM /= !comp_polyC !comp_polyX.
Qed.

End compp_correct.

Fixpoint is_zero_pol (p : seq bigQ) :=
  match p with
    [::] => true
  | x::p' => match (x ?= 0)%bigQ with Eq => is_zero_pol p' | _ => false end
  end.

Fixpoint normalize p :=
  match p with
    [::] => [::]
  | x::p' => 
    if is_zero_pol p then nil else x::normalize p'
  end.

(* Translation by a is composition with (X + a) *)
Definition theta a p := compp p (a::1::nil)%bigQ.

(* Expansion by factor k is composition with (k X) *)
Definition chi k (p : seq bigQ) := compp p (0::k::nil)%bigQ.

(* Inversion *)

Definition rho l := rev (normalize l).

Definition tau l r p := map red (theta 1 (rho (chi (r - l) (theta l p)))).

Section tau_correct.

Lemma sbQ_to_p_redP : forall l, sbQ_to_p (map red l) = sbQ_to_p l.
Proof.
elim=> [ | a tl IH] /=; first by [].
rewrite IH; congr (_ + _)%R; congr (_ %:P). 
apply/eqP/bigQ_to_RP; exact: spec_red.
Qed.

Lemma chiP : forall a p, sbQ_to_p (chi a p) = sbQ_to_p p \scale bigQ_to_R a.
Proof.
move=> a p; rewrite /chi /scaleX_poly comppP /= /bigQ_to_R Q_to_R0.
by rewrite add0r mulr0 addr0.
Qed.

Lemma thetaP : forall a p, sbQ_to_p (theta a p) = sbQ_to_p p \shift bigQ_to_R a.
Proof.
move=> a p; rewrite /theta /shift_poly comppP /= /bigQ_to_R Q_to_R1.
by rewrite mulr0 addr0 mulr1 addrC.
Qed.

Lemma is_zero_polP : forall p, is_zero_pol p = (sbQ_to_p p == 0%R)%bool.
Proof.
elim=> [ | a p IH] /=; first by rewrite eqxx.
case h: (a ?= 0)%bigQ =>//.
    have h' : bigQ_to_R a = bigQ_to_R 0.
      by apply/eqP/bigQ_to_RP/eqb_correct; rewrite /eq_bool h.
    rewrite h' /bigQ_to_R Q_to_R0 add0r.
    case h2:(is_zero_pol p).
      by move: (sym_equal IH); rewrite h2 => /eqP => ->; rewrite mulr0 eqxx.
    rewrite -size_poly_eq0 mulrC size_mulX; first by [].
    by rewrite -IH h2.
  rewrite addrC mulrC - cons_poly_def -size_poly_eq0 size_cons_poly.
  have -> : (bigQ_to_R a == 0%R)%B = false; last by rewrite andbF.
  rewrite -[0%R](_ : bigQ_to_R 0 = 0%R); last first.
    by rewrite /bigQ_to_R /Q_to_R /= mul0r.
  apply/negP/bigQ_to_RP=> t.
  by have := (eqb_complete _ _ t); rewrite /eq_bool h.
rewrite addrC mulrC - cons_poly_def -size_poly_eq0 size_cons_poly.
have -> : (bigQ_to_R a == 0%R)%B = false; last by rewrite andbF.
rewrite -bigQ_to_R0.
by apply/negP/bigQ_to_RP=> t; have := (eqb_complete _ _ t); rewrite /eq_bool h.
Qed.

Lemma size_sbQ : forall p, size (sbQ_to_p p) = size (normalize p).
Proof.
elim=> [ | a p IH] /=; first by rewrite size_poly0.
case h: (a ?= 0)%bigQ.
    have h' : bigQ_to_R a = bigQ_to_R 0.
      by apply/eqP/bigQ_to_RP/eqb_correct; rewrite /eq_bool h.
    rewrite h' bigQ_to_R0 add0r.
    case t : (is_zero_pol p).
      move: t; rewrite (is_zero_polP p) =>/eqP=> ->.
      by rewrite mulr0 size_poly0.
    rewrite /= -IH mulrC size_mulX; first by [].
    by rewrite -is_zero_polP t.
  rewrite /= addrC mulrC - cons_poly_def size_cons_poly -bigQ_to_R0.
  have -> : (bigQ_to_R a == bigQ_to_R 0)%B = false; last first.
    by rewrite andbF IH.
  by apply/negP/bigQ_to_RP=>t; have:= (eqb_complete _ _ t); rewrite /eq_bool h.
rewrite /= addrC mulrC - cons_poly_def size_cons_poly -bigQ_to_R0.
have -> : (bigQ_to_R a == bigQ_to_R 0)%B = false; last first.
  by rewrite andbF IH.
by apply/negP/bigQ_to_RP=>t; have:= (eqb_complete _ _ t); rewrite /eq_bool h.
Qed.

Lemma normalizeP : forall p, sbQ_to_p (normalize p) = sbQ_to_p p.
Proof.
elim=>[ | a p IH]; first by [].
rewrite /=; case h : (a ?=0)%bigQ; try (rewrite /= IH; by []).
case t : (is_zero_pol p).
  have h' : (bigQ_to_R a == bigQ_to_R 0)%B = true.
    by apply/bigQ_to_RP; apply: eqb_correct; rewrite /eq_bool h.
  rewrite (eqP h') bigQ_to_R0 add0r (_: sbQ_to_p p = 0%R) ?mulr0 //.
  by apply/eqP; rewrite -is_zero_polP.
by rewrite /= IH.
Qed.

Lemma sbQ_nth :
  forall p, sbQ_to_p p = \poly_(i < size p) bigQ_to_R (nth 0%bigQ p i).
Proof.
elim=>[|a p IH] /=; first by rewrite poly_def big_ord0.
rewrite poly_def big_ord_recl expr0 /= alg_polyC.
have h : forall i:'I_(size p), true ->
    bigQ_to_R (nth 0%bigQ p i) *: 'X^(bump 0 i) =
                         ('X * (bigQ_to_R (nth 0%bigQ p i) *: 'X^i))%R.
  by move=> i _; rewrite /bump leq0n exprD scalerAr expr1.
rewrite (eq_bigr (fun i : 'I_(size p) =>
            ('X * (bigQ_to_R (nth 0%bigQ p i) *: 'X^i))%R) h).
by rewrite IH poly_def big_distrr.
Qed.

Lemma rhoP : forall p, sbQ_to_p (rho p) = reciprocal_pol (sbQ_to_p p).
Proof.
move=> p; rewrite /rho /reciprocal_pol.
rewrite sbQ_nth size_sbQ size_rev !poly_def; apply: eq_bigr => /= i _.
rewrite -normalizeP nth_rev; last by case:i.
by congr (_ *: _); rewrite sbQ_nth coef_poly rev_ord_proof.
Qed.

Lemma tauP : forall l r p, sbQ_to_p (tau l r p) = 
   Mobius (sbQ_to_p p) (bigQ_to_R l) (bigQ_to_R r).
Proof.
move=> l r p; rewrite /tau /Mobius.
rewrite sbQ_to_p_redP thetaP; congr (_ \shift _).
  by rewrite /bigQ_to_R Q_to_R1.
rewrite rhoP chiP thetaP; congr reciprocal_pol; congr scaleX_poly.
by rewrite bigQ_to_RD bigQ_toRN.
Qed.

End tau_correct.

(* Computing binomial coefficients in the filed bigQ *)
Fixpoint fact_aux (count : nat) (n : bigQ) :=
  match count with
  | 0%nat => n
  | 1%nat => n
  | S p => (n * fact_aux p (n + 1))%bigQ
  end. 

Definition fact (n : nat) : bigQ := fact_aux n 1.

Definition binomial n i := red ((fact n) / (fact i * fact (n - i)))%bigQ.

(* The scalar product between sequences of numbers, the size of
  the result is the minimum of the input sizes. *)
Definition product l1 l2 := map (fun c => (c.1 * c.2)%bigQ) (zip l1 l2).

(* Defining a function that returns the list of natural numbers, in
 increasing order. *)

Definition binvs n := map (fun i => (1/binomial n i)%bigQ) (iota 0 (S n)).

(* Computing the initial list of Bernstein coefficients for a polynomial
  and an interval.  The first argument is degree of the polynomial. *)
Definition b_coefs n l r p := rev (product (binvs n) (tau l r p)).

(* Bernstein coefficients for half intervals can be computed using the
 algorithm by de Casteljau. *)
Fixpoint casteljau l (n : nat) :=
  match n with
    O => fun j => nth 0%bigQ l j
  | S p => fun j => ((casteljau l p j + casteljau l p j.+1)/2)%bigQ
  end.

(* This computes the Bernstein coefficients for the left hand side
  half. *)
Definition dicho_l n l :=
  map (fun i => red (casteljau l i 0)) (iota 0 (S n)).

Definition dicho_r n l :=
  map (fun i => red (casteljau l (n - i) i)) (iota 0 (S n)).

Fixpoint seqn0 l :=
  match l with
  | [::] => [::]
  | a::l' => if (eq_bool a 0) then seqn0 l' else a::seqn0 l'
  end.

Definition ch_at a b :=
  match (a ?= 0)%bigQ with
  | Eq => 0%nat
  | Gt => match (b ?= 0)%bigQ with Lt => 1%nat | _ => 0%nat end
  | Lt => match (b ?= 0)%bigQ with Gt => 1%nat | _ => 0%nat end
  end.

Fixpoint ch_r a l : nat :=
  match l with | nil => 0%nat | b::l' => (ch_at a b + ch_r b l')%nat end.

Definition changes l :=
  match l with | [::] => 0%nat | a::l' => ch_r a l' end.

Inductive root_info := 
  | Exact (x : bigQ)
  | One_in (x y : bigQ)
  | Zero_in (x y : bigQ)
  | Unknown (x y : bigQ).

Fixpoint isol_rec n d a b l acc : seq root_info :=
  match n with
    O => Unknown a b::acc
  | S p =>
    match changes l with
    | 0%nat => Zero_in a b::acc
    | 1%nat => One_in a b::acc
    | _ =>
    let c := red ((a + b)/2) in
    let l2 := dicho_r d l in
    isol_rec p d a c (dicho_l d l)
        (if eq_bool (head 0%bigQ l2) 0 then
           Exact c::isol_rec p d c b l2 acc
        else isol_rec p d c b l2 acc)
    end
  end.
    
Definition big_num := 500%nat.

(* Returns the last element of the sequence of coefficients, i.e.
  the lead coefficient if the sequence is normal. *)
Definition lead_coef p := last 0%bigQ p.

Fixpoint chomp {A : Type} (p : list A) :=
  match p with
    [::] => [::]
  | x::nil => nil
  | x::p' => x::chomp p'
  end.

Definition belast1 (p : seq bigQ) :=
  match p with [::] => [::] | a::tl => belast a tl end.

(* To be used with a monic divisor d, of degree dd *)

Fixpoint divp_r (p d : seq bigQ) (dd : nat) : seq bigQ * seq bigQ :=
  if NPeano.Nat.leb (size p) dd
  then ([::], p)
  else 
    match p with
      [::] => ([::], p)
    | a::p' => let (q, r) := divp_r p' d dd in
      let y := nth a (a::r) dd in
        (y::q, addp (a::r) (scal ((-1) * y) d))
    end.

Definition divp p d :=
  let d' := normalize d in
  let dd := (size d').-1 in
  let lc := lead_coef d' in
  match d' with
    [::] => ([::], p)
  | _::_ => let (q, r) := divp_r p (map (fun x => x/lc)%bigQ d') dd in
    (map (fun x => x/lc)%bigQ q, normalize r)
  end.

(* Correctness proof. *)

Search _ Q.
Definition repr (l : list bigQ) : poly rat :=
  
  
    

Definition clean_divp p d :=
  let (a, b) := divp p d in (map red (normalize a), map red (normalize b)).

Fixpoint gcd_r n (p q : seq bigQ) : seq bigQ :=
  match n with
    0 => p
  | S n' =>
    let (_, r) := clean_divp p q in
      match r with nil => q | _ => gcd_r n' q r end
  end.

Definition gcd (p q : seq bigQ) :=
  let r := gcd_r (maxn (size p) (size q)).+1 p q in
  let lc := lead_coef r in
  map (fun x => red (x/lc)) r.

Compute (clean_divp [::3;1] [::4;1])%bigQ.
Compute (clean_divp [::3;2;1] [::1])%bigQ.
Compute (gcd_r 4 [::3;1] [::4;1])%bigQ.

Fixpoint bigQ_of_nat (n : nat) :=
  match n with 0%nat => 0%bigQ | S p => (1 + bigQ_of_nat p)%bigQ end.

Definition derive p := 
  match product (map bigQ_of_nat (iota 0 (size p))) p with
    _::p' => p' | _ => nil
  end.

Definition no_square p :=
  fst (clean_divp p (gcd p (derive p))).

Definition isolate a b p : seq root_info :=
  let l := no_square p in
  let deg := (size l).-1 in
  let coefs := b_coefs deg a b l in
  let b_is_root :=
    if eq_bool (last 0%bigQ coefs) 0 then [:: Exact b] else [::] in
  let result := isol_rec big_num deg a b coefs b_is_root in
  if eq_bool (head 0%bigQ l) 0 then Exact a::result else result.

Fixpoint horner x p :=
  match p with
    nil => 0%bigQ
  | a::p' => (a + x * horner x p')%bigQ
  end.

Fixpoint ref_rec n a b pol :=
  match n with
    O => One_in (red a) (red b)
  | S p =>
    let c := ((a + b)/2)%bigQ in
    let v := horner c pol in
    match (v ?= 0)%bigQ with
      Lt =>  ref_rec p c b pol
    | Gt =>  ref_rec p a c pol
    | Eq => Exact (red c)
    end
  end.

Fixpoint first_sign l :=
  match l with
    nil => 1%bigQ
  | a::tl =>
   match (a ?= 0) with Eq => first_sign tl | Lt => -1 | Gt => 1 end%bigQ
  end.

Definition refine n a b p :=
  let deg := (List.length p).-1 in
  let coefs := b_coefs deg a b p in
  ref_rec n a b (scal (-1 * first_sign coefs) p).

(* This polynomial has 1,2, and 3 as roots. *)
Definition pol2 : list bigQ := ((-6)::11::(-6)::1::nil)%bigQ.

(* This polynomial as 1 and 2 as roots, with respective multiplicities
  1 and 2. *)

Fixpoint no_root (l : list root_info) : bool :=
  match l with
    nil => true
  | Zero_in a b::l' => no_root l'
  | _ => false
  end.


Definition pol3 : list bigQ := ((-4)::8::(-5)::1::nil)%bigQ.

(* this polynomial has only one root, but the curve comes close to
  the x axis around 2.5: this forces the dichotomy process a few times. *)
Definition mypol : list bigQ := ((-28/5)::11::(-6)::1::nil)%bigQ.

Compute mypol.
Compute clean_divp mypol [::1]%bigQ.
Compute no_square mypol.
Compute b_coefs 3 0 4 (no_square mypol).


(* The following isolates the single root of mypol in (0,4) *)
Compute isolate 0 4 mypol.

(* The following computation proves that mypol has no roots in (2,4) *)
Compute b_coefs 3 2 4 mypol.
Compute map (fun p => p.1 ?= p.2)%bigQ 
    (zip (dicho_r 3 (b_coefs 3 2 4 mypol)) (b_coefs 3 3 4 mypol)).
Compute changes (b_coefs 3 3 4 mypol).
Compute isol_rec big_num 3 2 3 (b_coefs 3 2 3 mypol) [::].
Compute isol_rec big_num 3 0 4 (b_coefs 3 0 4 mypol) [::].

Compute isolate 2 4 mypol.


Time Compute refine 20 0 2 mypol.

Compute (horner (110139 # 131072) mypol).
Compute (horner (440557 # 524288) mypol).

(* Polynomial pol2 actually has roots in 1, 2, and 3 *)
Compute isolate 0 4 pol2.

Compute isolate 0 4 pol3.

(* When the path of computation touches the roots, they are recognized
 as such. *)
Compute isolate 1 3 pol2.

Compute refine 10 (11#10) 3 pol2.

Compute ((10000 * 20479 / 10240)%bigZ, (10000 * 10249 / 5120)%bigZ).

(* Without type information, this gives an error message that looks like a
  bug. *)

Compute clean_divp ((-2)::1::1::nil)%bigQ (4::2::nil)%bigQ.

Compute let p := ((-2)::1::1::nil)%bigQ in
        let d := (2::1::nil)%bigQ in
        let (q, r) := divp p d in
        (q, r, normalize (addp p (scal (-1) (addp (mulp q d) r)))).

Compute let p := ((-2)::1::1::nil)%bigQ in
        let q := ((-1)::3::(-3)::1::nil)%bigQ in
        gcd p q.

Compute derive ((-1)::3::(-3)::1::nil)%bigQ.

Compute gcd ((-1)::3::(-3)::1::nil)%bigQ (derive ((-1)::3::(-3)::1::nil)%bigQ).

Compute clean_divp ((-1)::3::(-3)::1::nil)%bigQ
             (1::(-2)::1::nil)%bigQ.

Time Compute no_square ((-1)::3::(-3)::1::nil)%bigQ.

(* This is a poor man's correctness proof for the decision procedure,
  but it should actually be extended to be used in any real-closed field. *)
