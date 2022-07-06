From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat binomial seq choice order.
From mathcomp Require Import fintype bigop ssralg poly ssrnum ssrint rat ssrnum.
From mathcomp Require Import polyrcf qe_rcf_th realalg.
Require Import pol poly_normal desc.
From HB Require Import structures.

(******************************************************************************)
(*  de_casteljau == De Casteljau's algorithm                                  *)
(*    dicho' b i := de_casteljau b i 0                                        *)
(*   dicho p b i := de_casteljau b (p - i) i                                  *)
(* bernp a b p i == Bernstein polynomial of degree p for a, b for 0 <= i <= p *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Import GRing.Theory.
Import Num.Theory Num.Def.
Local Open Scope ring_scope.

(* A technical binomial identity for the proof of de Casteljau *)
Lemma util_C : forall n i j : nat, (i <= j)%nat -> (j <= n)%nat ->
    ('C(n, i) * 'C(n-i, j-i) = 'C(j, i) * 'C(n, j))%nat.
Proof.
move => n i j ij jn.
apply/eqP; rewrite -(@eqn_pmul2r ( i`! * (n - i) `!));
  last by rewrite muln_gt0; apply/andP; split; apply: fact_gt0.
rewrite -(@eqn_pmul2r ((j - i)`! * ((n - i)-(j - i))`!)); last first.
  by rewrite muln_gt0; apply/andP; split; apply: fact_gt0.
have ilen : (i <= n)%nat by apply: leq_trans jn.
rewrite (mulnAC 'C(n, i)) -mulnA !bin_fact //; last by apply: leq_sub2r.
rewrite !mulnA (mulnAC _ _ (i`!)) 2!(mulnAC _ _ ((j-i)`!)) -(mulnA 'C(j, i)).
rewrite bin_fact // -subnDA subnKC // mulnAC (mulnC j`!) -(mulnA _ j`!).
by rewrite bin_fact.
Qed.

Section ToBeAddedInOrderedAlg.

Variable F : numFieldType.

Lemma normr_sum : forall m  (G : nat -> F),
  `|\sum_(i < m) G i| <= \sum_(i < m) `|G i|.
Proof.
elim=> [|m ihm] G; first by rewrite !big_ord0 normr0.
rewrite !big_ord_recr /=; apply: le_trans (ler_norm_add _ _) _=> /=.
by rewrite ler_add2r; apply: ihm.
Qed.

Lemma expf_gt1 : forall m (x : F), x > 1 -> x^+m.+1 > 1.
Proof.
elim => [|m ihm] x hx; first by rewrite expr1.
apply: lt_trans (hx) _ => /=; rewrite exprS -{1}(mulr1 x).
rewrite ltr_pmul2l; first exact: ihm.
apply: lt_trans hx; exact: ltr01.
Qed.

Lemma expf_ge1 : forall m (x : F), x >= 1 -> x^+m >= 1.
Proof.
elim => [|m ihm] x hx; first by rewrite expr0 lexx.
apply: le_trans (hx) _ => /=; rewrite exprS. (* -{1}(mulr1 x). *)
rewrite ler_pmulr; first exact: ihm.
apply: lt_le_trans hx; exact: ltr01.
Qed.

End ToBeAddedInOrderedAlg.

Section ToBeAddedInPoly.

Variable R : idomainType.

(* A remark, lemma size_Xma should be with addition *)
Lemma size_factor_expr : forall (t : R)(n : nat),
  size (('X + t%:P)^+n) = n.+1.
Proof.
move=> t; elim=> [|n ihn]; first by rewrite expr0 size_polyC oner_eq0.
rewrite exprS size_monicM //; last first.
    by rewrite -size_poly_eq0 ihn; apply/negP; move/eqP.
  by rewrite  -(opprK t%:P) -polyCN monicXsubC.
by rewrite ihn -(opprK t%:P) -polyCN size_XsubC.
Qed.

Lemma size_amul_expr : forall (t c : R)(i : nat),
  c != 0 -> size (('X * c%:P + t%:P) ^+ i) = i.+1.
Proof.
move=> t c; elim=> [| i ih] cn0; first by rewrite expr0 size_poly1.
have hn0 : size ('X * c%:P + t%:P) = 2.
  rewrite mulrC size_MXaddC polyC_eq0.
  move: cn0; rewrite -eqbF_neg=> /eqP => cn0.
  by rewrite size_polyC cn0 andFb.
by rewrite exprS size_mul // ?expf_eq0 -?size_poly_eq0 hn0 ?andbF // ih.
Qed.

Lemma size_factor : forall x : R, size ('X + x%:P) = 2.
Proof.
 by move=> x; rewrite size_addl ?size_polyX // size_polyC /=; case: (x == 0).
Qed.

Lemma size_polyX_mul : forall p : {poly R},
  size ('X * p) = if p == 0 then 0%nat else (size p).+1.
Proof.
move=> p; rewrite (_ : 'X * p = p * 'X + 0%:P); last by rewrite mulrC addr0.
  by rewrite size_MXaddC eqxx andbT.
Qed.

Lemma coef_poly0 : forall p q : {poly R}, (p * q)`_0 = p`_0 * q`_0.
Proof.
by move=> p q; rewrite coef_mul_poly big_ord_recl big_ord0 sub0n addr0.
Qed.

End ToBeAddedInPoly.
(* We prove the Cauchy bound in any ordered field *)

Section CauchyBound.

Variable F : realFieldType.

Variables (n : nat)(E : nat -> F).

Hypothesis pnz : E n != 0.

Lemma CauchyBound x: (\poly_(i < n.+1) E i).[x] = 0 ->
  `| x | <= `|E n|^-1 * \sum_(i < n.+1) `|E i|.
Proof.
move=> px0; case: (lerP `|x| 1)=> cx1.
  set C := _ * _; suff leC1 : 1 <= C by apply: le_trans leC1.
  have h1 : `|E n| > 0 by rewrite  normr_gt0.
  rewrite -(ler_pmul2l h1) /= mulr1 /C mulrA mulfV ?normr_eq0 // mul1r.
  by rewrite big_ord_recr /= -{1}(add0r `|E n|) ler_add2r sumr_ge0.
case e: n=> [| m].
  move: pnz; rewrite -px0 e horner_poly big_ord_recl big_ord0 /=.
  by rewrite addr0 expr0 mulr1 /= eqxx.
have h1 : E  m.+1 * x^+m.+1 = - \sum_(i < m.+1) E i * x^+ i.
  apply/eqP; rewrite -subr_eq0 opprK -{2}px0 horner_poly (big_ord_recr n).
  by rewrite e //= addrC.
case x0 : (x == 0).
  by rewrite (eqP x0) normr0 mulr_ge0 ?sumr_ge0// invr_gte0.
have {h1} h2 : E m.+1 * x =  - \sum_(i < m.+1) E i * x^-(m - i).
have xmn0 : ~~ (x^+m == 0) by rewrite expf_eq0 x0 andbF.
  apply: (mulIf xmn0); rewrite mulNr big_distrl /= -mulrA -exprS h1.
  congr (- _); apply: congr_big; [by [] | by [] |] => [[i hi]] _ /=.
  have mi : m = (m - i + i)%N by rewrite subnK.
  rewrite {2}mi exprD -!mulrA; congr (_ * _); rewrite mulrA mulVf ?mul1r //.
  by rewrite expf_eq0 x0 andbF.
have h3 : `|\sum_(i < m.+1) E i / x ^+ (m - i) | <= \sum_(i < m.+2) `|E i|.
  apply: le_trans (normr_sum m.+1 (fun i =>  E i / x ^+ (m - i))) _.
  apply: (@le_trans _ _ (\sum_(i < m.+1) `|E i|)); last first.
    by rewrite (big_ord_recr m.+1) /= ler_addl /= normr_ge0.
  suff h: forall i, (i < m.+1)%N -> `|E i/x^+(m-i)| <= `|E i|.
    by apply: ler_sum => //= i _; exact: h.
  move=> i lti; rewrite normrM -{2}(mulr1 (`|E i|)) ler_wpmul2l ?normr_ge0 //.
  rewrite normfV normrX invf_le1; first by rewrite exprn_cp1 // ltW.
  by rewrite exprn_gt0 // (lt_trans ltr01).
rewrite lter_pdivl_mull; last by rewrite normr_gt0 -e.
by apply: le_trans h3=> /=; rewrite -normrM h2 normrN lexx.
Qed.

End CauchyBound.

(*
Section TranslateProps.

(* First linearity lemma : translate complies with scalar product for *)
(* elements of the basis *)

(*
(* Second linearity lemma : translate complies with addition *)
Lemma translate_add : forall l1 l2 c,
  size l1 = size l2 ->
  shift_poly (map (fun x : Qcb * Qcb => x.1 + x.2) (zip l1 l2)) c =
    map (fun x => x.1 + x.2) (zip (shift_poly l1 c) (shift_poly l2 c)).
Proof.
move=> l1 l2 c e; apply: (@eq_from_nth _ 0); rewrite size_shift_poly !size_map.
  by rewrite !size1_zip ?size_shift_poly // e.
move=> i; rewrite size1_zip ?e // => his; rewrite translate_nth; last first.
  by rewrite size_map size2_zip // e.
rewrite size_map size1_zip ?e //= (nth_map (0, 0)); last first.
  by rewrite size2_zip ?size_shift_poly // e /=.
rewrite nth_zip ?size_shift_poly // !translate_nth // ?e //=.
rewrite -big_split /=; apply: congr_big=> // [[k hk]] _ /=.
rewrite (nth_map (0, 0)) ?size2_zip // ?e // nth_zip //= mulr_addl.
by rewrite mulrn_addl.
Qed.

Lemma translate_mulX : forall (q1 q2 : {poly Qcb}) c, 
  q2 != 0 -> q1 != 0 ->
  shift_poly q2 c = q1 -> shift_poly ('X * q2) c = ('X + c%:P) * q1.
Proof.
  move=> q1 q2 c q2n0 q1n0 e.
  have sp1 : size (shift_poly ('X * q2) c) = (size q2).+1.
    by rewrite size_shift_poly size_mul_id // -?size_poly_eq0 ?size_polyX.
  have sp2 : size ('X * q2) = (size q2).+1.
    by rewrite mulrC size_mul_monic ?monicX // size_polyX !addnS addn0.
  apply: (@eq_from_nth _ 0).
    by rewrite sp1 size_mul_id // -?size_poly_eq0 ?size_factor // -e size_shift_poly.
  rewrite sp1 => [[_|j hj]].
    rewrite translate_nth ?size_polyX_mul ?(negPf q2n0) //.
    rewrite coef_poly0 coef_add coefC eqxx coefX add0r -e /shift_poly.
    rewrite !nth_mkseq ?lt0n ?size_poly_eq0 // -?size_poly_eq0 ?sp2 //.
    rewrite big_distrr big_ord_recl coef_Xmul eqxx mul0r mul0rn add0r.
    apply: congr_big=> // [[k hk]] _.
    rewrite  !bin0 !subn0 !mulr1n -[('X * q2)`__]/(('X * q2)`_k.+1).
    rewrite [GRing.muloid _ _]/= [c * _]mulrC.
    rewrite -mulrA [_ * c]mulrC -exprS; congr (_ * _).
    (* we  should really put a nosimpl on `_ *)
    by rewrite coef_Xmul /=.
  rewrite /shift_poly nth_mkseq ?sp2 //.
  rewrite coef_mul; apply: sym_eq; rewrite 2!big_ord_recl big1; last first.
    case=> k hk _; rewrite -[('X + c%:P)`_ _]/(('X + c%:P)`_ k.+2).
    by rewrite coef_add coefC coefX /= addr0 mul0r.
  rewrite [nat_of_ord _]/= !subn0 addr0 -[nat_of_ord _]/1%N.
  rewrite !coef_add !coefX !coefC !eqxx -![_ == _]/false add0r addr0 mul1r.
  rewrite -e /shift_poly.
  rewrite big_ord_recl coef_Xmul eqxx mul0r mul0rn add0r subSS subn0.
  move: hj; rewrite ltnS leq_eqVlt; case/orP.
    move/eqP=> ej; rewrite ej nth_default ?size_mkseq ?leqnn // mulr0 add0r.
    rewrite nth_mkseq -?ej //; apply: congr_big => // [[k hk]] _.
    rewrite -[('X * q2)`_ _]/(('X * q2)`_k.+1) subSS coef_Xmul -[_ == 0%N]/false /=.
    move: hk; rewrite ltnS leq_eqVlt; case/orP; first by move/eqP->; rewrite !binn.
    move=> hkj; rewrite !bin_small //.
  move=> hjs. rewrite !nth_mkseq //; last by apply: ltn_trans hjs.
  rewrite big_distrr -big_split; apply: congr_big=> // [[k hk]] _.
  rewrite  -[('X * q2)`_ _]/(('X * q2)`_k.+1) coef_Xmul /= subSS.
  rewrite -mulrnAl mulrC -mulrA [_ * c]mulrC -exprS {hjs hk}.
  case: (ltngtP k j) => ekj.
  - by rewrite !bin_small //; apply: ltn_trans ekj _.
  - by rewrite -ltn_subS // mulrnAl -mulrn_addr -binS.
  - rewrite ekj !binn subnn bin_small // (_ : j - j.+1 = 0)%N; last first.
       by apply/eqP; rewrite subn_eq0.
    by rewrite !mulr0n mul0r add0r expr0.
Qed.

Lemma shift_polyXn : forall (c : Qcb) i,
  (shift_poly 'X^i c) = ('X + c%:P)^+i.
Proof.
move=> c i; rewrite -(mulr1 'X^i); elim: i => [| i ihi].
  rewrite !expr0 mulr1 /shift_poly size_polyC oner_eq0 /=.
  rewrite /mkseq /= big_ord_recl big_ord0 subn0 bin0 addr0 expr0 mulr1 mulr1n.
  by rewrite -polyC1 coefC eqxx polyseqC oner_eq0.
rewrite exprS -mulrA.
rewrite (translate_mulX _ _ _ _ _ ihi) ?exprS // ?mulr1 -size_poly_eq0.
  by rewrite size_polyXn.
by rewrite size_factor_expr.
Qed.

Lemma translate_mulXn : forall n (q1 q2 : {poly Qcb}) c, q2 != 0 -> q1 != 0 ->
   q2 \shift c = q1 ->
   ('X^n * q2) \shift c = ('X + c%:P)^+n * q1.
Proof.
elim=> [|n ihn] q1 q2 c nq20 nq10 e; first by rewrite expr0 !mul1r.
rewrite exprS -mulrA.
have h : shift_poly ('X^n * q2) c = ('X + c%:P) ^+ n * q1.
  by rewrite (ihn q1 q2).
rewrite (translate_mulX _ _ _ _ _ h); first by rewrite mulrA -exprS.
  rewrite -size_poly_eq0 mulrC size_mul_monic ?monicXn // size_polyXn !addnS /=.
  by rewrite addn_eq0 negb_and size_poly_eq0 nq20.
rewrite -size_poly_eq0 size_mul_id // -?size_poly_eq0 ?size_polyXn size_factor_expr //=.
by rewrite addn_eq0 negb_and size_poly_eq0 nq10 orbT.
Qed.

(* to be cleaned: a simple induction is probably enough *)
Lemma translate_padded_l : forall (i : nat) (q : seq Qcb)(c : Qcb) ,
  shift_poly (q ++ (nseq i 0)) c = (shift_poly q c) ++ (nseq i 0).
Proof.
move=> n; elim: n {-2}n (leqnn n) => [| i hi] n hn q c.
 by move: hn; rewrite leqn0; move/eqP->; rewrite !cats0.
move: hn; rewrite leq_eqVlt; case/orP; last by move=> hn; rewrite hi //.
move/eqP->; rewrite -[q ++ _]/(q ++ nseq 1 0 ++ nseq i 0) catA hi //.
rewrite /shift_poly size_cat size_nseq addnS addn0.
rewrite -[nseq i.+1 0]/([:: 0] ++ nseq i 0) catA; congr (_ ++ _).
apply: (@eq_from_nth _ 0).
  by rewrite size_cat /= !size_mkseq size_map size_iota addn1.
rewrite size_mkseq => j; rewrite ltnS leq_eqVlt; case/orP=> hj.
  rewrite (eqP hj) nth_mkseq // nth_cat size_mkseq ltnn subnn /= big1 //.
  case=> k /=; rewrite ltnS leq_eqVlt; case/orP=> hk _.
    rewrite (eqP hk) nth_cat ltnn subnn /= mul0r mul0rn //.
  by rewrite nth_cat hk bin_small // mulrn0.
rewrite nth_cat size_mkseq hj !nth_mkseq //; last by apply: ltn_trans hj _.
rewrite big_ord_recr /= nth_cat ltnn subnn mul0r mul0rn addr0.
by apply: congr_big; [by [] | by [] |] => [[k hk]] _ /=; rewrite nth_cat hk.
Qed.

Lemma translateXn_addr : forall c1 c2 n,
  shift_poly (shift_poly 'X^n c1) c2 = shift_poly 'X^n (c1 + c2).
Proof.
move=> c1 c2 n.
apply:  (@eq_from_nth _ 0); rewrite ?size_shift_poly //.
rewrite size_polyXn => i hi.
rewrite /shift_poly nth_mkseq ?size_mkseq ?size_polyXn // nth_mkseq //.
apply: trans_equal (_ :
  \sum_(k < n.+1) (\sum_(k0 < n.+1)'X^n`_k0 * c1 ^+ (k0 - k) *+
    'C(k0, k) * c2 ^+ (k - i) *+ 'C(k, i)) = _).
  apply: congr_big => // [[k hk]] _ /=; rewrite nth_mkseq //.
  by rewrite big_distrl /= -sumr_muln.
rewrite exchange_big /=.
apply: trans_equal (_ :
\sum_(j < n.+1)
\sum_(i0 < n.+1) 'X^n`_j * (c1 ^+ (j - i0) *+ 'C(j, i0) * c2 ^+ (i0 - i) *+ 'C(i0, i)) = _).
  apply: congr_big=> // [[k hk]] _ /=; apply: congr_big=> // [[j hj]] _ /=.
  by rewrite !mulrnAr !mulrA mulrnAr.
apply: congr_big=> // [[k hk]] _ /=; rewrite -big_distrr /=.
rewrite -mulrnAr; congr (_ * _).
rewrite -(subnKC hk) big_split_ord /= addrC big1; last first.
  case=> j hj _ /=; rewrite bin_small; last by apply: ltn_addr.
  by rewrite mulr0n mul0r mul0rn.
rewrite add0r; case: (ltngtP k.+1 i) => hki.
  -rewrite bin_small //; last by apply: ltn_trans hki.
  rewrite mulr0n big1 // => [[j hj]] _ /=; rewrite (@bin_small j); last first.
    by apply: ltn_trans hj _.
  by rewrite mulr0n.
  - rewrite ltnS in hki. rewrite -{-  7 11 12}(subnKC hki) -addnS big_split_ord /= big1; last first.
      by case=> j hj _ /=; rewrite (@bin_small j).
    rewrite add0r exprn_addl -sumr_muln; apply: congr_big => // [[j hj]] _ /=.
  rewrite subnKC // -subnDA [(i + _)%N]addnC -addn_subA // subnn addn0.
  rewrite mulrnAl -!mulrnA;  congr (_ *+ _).
  rewrite [(_ * 'C(k, i))%N]mulnC {3}(_ : j = j + i - i)%N; last first.
    by rewrite -addn_subA // subnn addn0.
  by rewrite util_C 1?mulnC // ?leq_addl // -(subnK hki) leq_add2r.
  - rewrite -hki bin_small // mulr0n big1 // => [[j hj]] /= _.
    by rewrite (@bin_small j).
Qed.
*)
End TranslateProps.
*)

(*
Section ReciprocateProps.

Lemma reciprocate_padded :  forall (i : nat) (q : seq Qcb),
  reciprocate_pol (q ++ (nseq i 0)) = (nseq i 0) ++ (reciprocate_pol q).
Proof.
move=> i q; rewrite /reciprocate_pol rev_cat; congr (_ ++_).
apply: (@eq_from_nth _ 0); rewrite size_rev size_nseq // => j hij.
rewrite nth_rev ?size_nseq // !nth_ncons.
by case: i hij=> // i hij; rewrite ltnS subSS leq_subr hij.
Qed.

End ReciprocateProps.

*)

(*
Section ExpandProps.

Lemma expand_padded :  forall (i : nat) (q : seq Qcb)(c : Qcb) ,
  expand (q ++ (nseq i 0)) c = (expand q c) ++ (nseq i 0).
Proof.
elim=> [| i ih] q c; first  by rewrite !cats0.
rewrite -[q ++ _]/(q ++ [:: 0] ++ nseq i 0) catA ih.
suff {ih} -> :  expand (q ++ cons 0 [::]) c = expand q c ++ [:: 0] by rewrite -catA.
apply: (@eq_from_nth _ 0); first by rewrite size_cat /expand !size_mkseq  !size_cat.
rewrite /expand size_mkseq size_cat addnS addn0=> {i} i.
rewrite ltnS leq_eqVlt; case/orP.
  move/eqP->; rewrite nth_cat nth_mkseq // size_mkseq ltnn subnn nth_cat ltnn.
  by rewrite subnn /= mul0r.
move=> ltis; rewrite nth_mkseq; last by apply: ltn_trans ltis _.
by rewrite !nth_cat size_mkseq ltis nth_mkseq.
Qed.

End ExpandProps.

*)

(* b gives the coefficients of a polynomial on some bounded interval [a, b].
de_casteljau computest all the coefficients in the triangle for a, m, n, with
l := m - a and r := b - m.

invariant : l + r = b - a *)

Section DeCasteljauAlgo.

Variable R : comRingType.

Variables l r : R.

Fixpoint de_casteljau (b : nat -> R) (n : nat) :=
  match n with
    O => b
  | i.+1 => fun j =>
    (l * de_casteljau b i j + r * de_casteljau b i j.+1)%R
  end.

(* b gives the B. coefficients of a polynomial on some bounded interval [a, b].
computes the B. coefficients on [a, a + l] si b - a = l + r *)
Definition dicho' b i := de_casteljau b i 0.

(* b gives the B. coefficients of a polynomial P on some bounded interval [a, b].
computes the B. coefficients on [b-r, b] si b - a = l + r , as soon as p = deg P *)
Definition dicho p b i := de_casteljau b (p - i) i.

(* the computation of the value at index (k, n) only uses values (i, j)
   for n <=  i <= n + k (a triangle, up and right) *)

Lemma ext_dc :
  forall k b b' n, (forall i, (n <= i)%nat -> (i <= n + k)%nat -> b i = b' i) ->
  de_casteljau b k n = de_casteljau b' k n.
move => k b b'; elim: k => [ n q | k IHk n q] /=.
  by apply: q; rewrite ?addn0 leqnn.
rewrite !IHk //; move => i ni nik; apply: q => //; first exact: ltnW.
  by move: nik; rewrite addnS addSn.
by apply: leq_trans nik _; rewrite addnS leqnSn.
Qed.

(* de_casteljau is linear with respect to coefficients *)
Lemma lin_dc : forall k a a' b b' n,
  de_casteljau (fun j => (a * b j + a' * b' j)%R) k n =
  (a * de_casteljau b k n + a' * de_casteljau b' k n)%R.
Proof.
elim => [ | k IHk] a a' b b' n /= ; first by [].
rewrite 2!IHk !mulrDr !mulrA !(mulrC r) !(mulrC l) !addrA.
by rewrite (addrAC _ _ (a' * l * _)%R).
Qed.

(* in particular it is additive *)
Lemma add_dc k b b' n :
  de_casteljau (fun j => b j + b' j)%R k n =
  (de_casteljau b k n + de_casteljau b' k n)%R.
Proof.
have := lin_dc k 1 1 b b' n.
rewrite (@ext_dc k (fun j => 1 * b j + 1 * b' j) (fun j => b j + b' j))%R.
  by rewrite !mul1r.
by move => x; rewrite /= !mul1r.
Qed.

(* in particular it is homothetic *)
Lemma scal_dc k a b n :
  de_casteljau (fun j => a * b j)%R k n = (a * de_casteljau b k n)%R.
Proof.
have := lin_dc k a 0 b (fun i => 0)%R n.
rewrite (@ext_dc _ (fun j => a * b j + 0 * 0)%R (fun j => a * b j)%R).
  by rewrite mul0r addr0.
by move => x; rewrite /= mul0r addr0.
Qed.

End DeCasteljauAlgo.

Section DeltaSeqs.

Variable R : rcfType.

Definition delta (i j : nat) : R := if (i == j) then 1 else 0.

Lemma dc_delta_head : forall j k l r,
  (j < k)%nat -> dicho' l r (delta k) j = 0.
Proof.
rewrite /dicho' => j k l r hlt.
pose d0 := fun _ : nat => 0 : R.
rewrite (@ext_dc _ _ _ _ _ d0); last first.
  move=> i; rewrite add0n /delta => h1 h2.
  have : (i < k)%nat by apply: leq_ltn_trans hlt.
  by rewrite ltn_neqAle; case/andP; rewrite eq_sym; move/negPf->.
elim:  j {hlt} 0%nat=> [| j ihj n] /=; first by done.
by rewrite !ihj !mulr0 addr0.
Qed.

(*Lemma translation_delta:*)
Lemma dc_deltaS : forall k A B i j,
  de_casteljau A B (delta i.+1) k j.+1 = de_casteljau A B (delta i) k j.
Proof.
elim=> [|k ihk] A B i j /=; last by rewrite !ihk.
case e : (i == j); first by rewrite /delta (eqP e) !eqxx.
by rewrite /delta eqSS e.
Qed.

(* algorithme applique a delta_i (colonne j > i)*)
 (*Lemma coef_algo_delta_col_supi:*)
Lemma dc_delta_lt : forall k A B i j, (j > i)%nat -> de_casteljau A B (delta i) k j = 0.
Proof.
elim=> [|k ihk] A B i j hlt /=.
  by move: hlt; rewrite ltn_neqAle; case/andP; move/negPf; rewrite /delta; move->.
rewrite !ihk // ?mulr0 ?addr0 //; apply: ltn_trans hlt _; exact: ltnSn.
Qed.

(* algorithme applique a delta_i (ligne n ,colonne  i)*)

(*Lemma coef_algo_delta_col_i:*)
Lemma dcn_deltan : forall n i A B,  de_casteljau A B (delta i%nat)  n i = A ^+ n.
Proof.
elim=> [|n ihn] i A B /=; first by rewrite /delta eqxx expr0.
by rewrite !ihn dc_delta_lt ?ltnSn // mulr0 exprS addr0.
Qed.

(* algorithme applique a delta_i (colonne k avec k < i - j, ligne j avec j < i)*)
(*Lemma coef_algo_delta_ligne_infi_k:*)
Lemma dc_delta_gt : forall j i A B, (j < i)%nat ->
  forall k, (k < i - j)%nat ->  de_casteljau A B (delta i) j k = 0.
Proof.
elim=> [| j ihj] i A B hltji k hltkd /=.
  by move: hltkd; rewrite subn0 ltn_neqAle /delta eq_sym; case/andP; move/negPf->.
have ltij : (j < i)%nat by apply: ltn_trans hltji; rewrite ltnSn.
rewrite !ihj // ?mulr0 ?addr0 //; first by rewrite -subnSK.
by apply: ltn_trans hltkd _; rewrite -[(i - j)%nat]subnSK.
Qed.

(* pourquoi on a un add_rec qui nous saute à la figure??? *)

Lemma dc_delta_tail : forall i k A B,
  de_casteljau A B (delta i) (i + k)%nat 0 = A ^+ k * B ^+ i *+'C(k + i, i).
Proof.
elim=> [|i ihi] k A B /=; rewrite -?addnE.
  by rewrite add0n addn0 /= expr0 mulr1  bin0 dcn_deltan mulr1n.
rewrite dc_deltaS ihi.
elim: k => [|k ihk] /=.
  rewrite !add0n !expr0 !addn0 !mul1r dc_delta_gt ?mulr0 ?add0r 1?mulrC ?subSnn //.
  by rewrite !binn !mulr1n exprS mulrC.
rewrite !addnS /= dc_deltaS ihi ihk !addnS !addSn !mulrnAr mulrA -exprS.
rewrite [_ * B^+ i]mulrC mulrA -exprS [B^+_ * _]mulrC -mulrnDr.
by congr (_ *+ _).
Qed.

(* Lemma algo_reverse:*)
Lemma dc_reverse b (A B : R) p : forall i k,
 (i <= p)%N ->
 (k <= p - i)%N ->
  de_casteljau B A (fun t => b (p - t)%N) i k = de_casteljau A B b i (p - (i + k)).
Proof.
elim=> [| i ihi] k hip hk /=; first by rewrite add0n.
rewrite addrC; congr (_  + _).
  by rewrite ihi ?(ltnW hip) ?addnS ?addSn // -[(p - i)%N]subnSK.
rewrite ihi ?(leq_trans hk) // ?leq_sub2l // ?(ltnW hip) //=.
rewrite addSn -subnSK //.
by move:hk; rewrite -ltn_subRL -ltnS subnSK.
Qed.

End DeltaSeqs.

Section weighted_sum.

(* TODO : I don't know what the right type is. *)
Variable R : rcfType.

Lemma size_weighted_sum_leq (A :eqType) (r : seq A) m (f : A -> R)
   (g : A -> {poly R}) :
  (forall i, i \in r -> (size (g i) <= m)%N) ->
  (size (\sum_(i <- r) f i *: g i)%R <= m)%N.
Proof.
elim: r => [_ | n r IH cg]; first by rewrite big_nil polyseq0.
rewrite big_cons (leq_trans (size_add _ _)) // geq_max.
have sn : (size (f n *: g n) <= m)%N.
  case fn : (f n == 0); first by rewrite (eqP fn) scale0r size_poly0.
  rewrite size_scale; last by rewrite fn.
  by apply: (cg n); rewrite in_cons eqxx.
by rewrite sn /=; apply: IH => i ir; apply: cg; rewrite in_cons ir orbT.
Qed.

End weighted_sum.

(* NB(2022/07/04): MathComp PR in progress, use eq_poly *)
Lemma poly_ext (R : ringType) (n : nat) (E1 E2 : nat -> R) :
  (forall i : nat, (i < n)%N -> E1 i = E2 i) ->
  \poly_(i < n) E1 i = \poly_(i < n) E2 i.
Proof.
by move=> E; rewrite !poly_def; apply: eq_bigr => i _; rewrite E.
Qed.

Section bernp.
Variables (R : numDomainType) (a b : R) (deg : nat).

(* elements of the Bernstein basis of degree p *)
Definition bernp (i : nat) : {poly R} :=
  ((b - a)^-deg)%:P * ('X - a%:P)^+i * (b%:P - 'X)^+(deg - i) *+ 'C(deg, i).

Lemma size_bernp (neqab : a != b) (i : nat) :
  (i <= deg)%N -> size (bernp i) = deg.+1.
Proof.
move=> id; rewrite /bernp.
rewrite -!mulrnAl -polyCMn -mulrA.
rewrite size_Cmul.
  rewrite size_monicM.
      rewrite size_exp_XsubC.
      have <- : (-1)%:P * ('X - b%:P) = (b%:P - 'X).
        by rewrite mulrBr polyCN !mulNr -polyCM mul1r opprK addrC mul1r.
      rewrite exprMn_comm; last by apply: mulrC.
      rewrite -polyC_exp size_Cmul; last first.
        rewrite exprnP; apply: expfz_neq0.
        by rewrite oppr_eq0 oner_neq0.
      by rewrite size_exp_XsubC addSn /= addnS subnKC.
    by apply/monic_exp/monicXsubC.
  rewrite exprnP expfz_neq0 // -size_poly_eq0.
  have -> : b%:P - 'X = (-1)%:P * 'X + b%:P.
    by rewrite addrC polyCN mulNr mul1r.
  rewrite size_MXaddC size_polyC.
  by rewrite polyCN oppr_eq0 (negbTE (oner_neq0 _)) andFb.
rewrite mulrn_eq0 negb_or.
rewrite invr_neq0 ?andbT; first by rewrite -lt0n bin_gt0.
by rewrite expf_neq0 // subr_eq0 eq_sym.
Qed.

Lemma bernp_gt0 i x : (i <= deg)%N -> a < x < b ->
   0 < (bernp i).[x].
Proof.
move=> id /andP [ax xb]; rewrite /bernp hornerMn pmulrn_lgt0; last first.
  by rewrite bin_gt0.
rewrite !hornerE.
apply mulr_gt0; first apply mulr_gt0.
    by rewrite invr_gt0 exprn_gt0 // subr_gt0 (lt_trans ax).
  by rewrite horner_exp exprn_gt0 // !hornerE subr_gt0.
by rewrite horner_exp exprn_gt0 // !hornerE subr_gt0.
Qed.

End bernp.

From mathcomp Require Import interval matrix.
From mathcomp Require Import classical_sets set_interval.
Local Open Scope classical_set_scope.


(* NB: already in mathcomp-analysis but with realType, PR in progress *)
Definition factor (R : numDomainType) (a b x : R) := (x - a) / (b - a).

(* TODO: move to set_interval.v *)
Lemma factorE (R : numFieldType) (a b x : R) : a != b ->
  1 - factor a b x = (b - x) / (b - a).
Proof.
move=> ab.
rewrite /factor -(@divrr _ (b - a)) ?unitfE ?subr_eq0 1?eq_sym//.
by rewrite -mulrBl opprB addrA subrK.
Qed.


Reserved Notation "x %:pr" (at level 0, format "x %:pr").

Module Prob.
Section prob.
Variable (R : numDomainType).
Record t := mk { p :> R ; Op1 : 0 <= p <= 1 }.
Definition O1 (p : t) := Op1 p.
Arguments O1 : simpl never.
End prob.
Module Exports.
Section exports.
Variables (R : numDomainType).
Canonical prob_subType := Eval hnf in [subType for @p R].
Local Notation prob := (t R).
Definition prob_eqMixin := [eqMixin of prob by <:].
Canonical prob_eqType := Eval hnf in EqType _ prob_eqMixin.
Definition prob_choiceMixin := [choiceMixin of prob by <:].
Canonical prob_choiceType := ChoiceType prob prob_choiceMixin.
Definition prob_porderMixin := [porderMixin of prob by <:].
Canonical prob_porderType := POrderType ring_display prob prob_porderMixin.
End exports.
End Exports.
End Prob.
Export Prob.Exports.
Notation prob := Prob.t.
Notation "q %:pr" := (@Prob.mk _ q (@Prob.O1 _ _)).
Coercion Prob.p : prob >-> Num.NumDomain.sort.

Lemma prob_ge0 (R : numDomainType) (p : prob R) : 0 <= p :> R.
Proof. by case: p => p /= /andP[]. Qed.
Global Hint Resolve prob_ge0 : core.

Lemma prob_le1 (R : numDomainType) (p : prob R) : p <= 1 :> R.
Proof. by case: p => p /= /andP[]. Qed.
Global Hint Resolve prob_le1 : core.

From mathcomp Require Import functions lebesgue_integral.

(* factors for an affine combination *)
HB.mixin Record isSum1 (R : numDomainType) (n : nat) (f : 'I_n.+1 -> R) := {
  sum_eq1 : \sum_(i < n.+1) f i = 1 }.
#[short(type=affine)]
HB.structure Definition Sum1 (R : numDomainType) (n : nat) :=
  {f of isSum1 R n f}.

From mathcomp Require Import zmodp.
Reserved Notation "v '``_' i" (at level 3, i at level 2,
  left associativity, format "v '``_' i").
Notation "v '``_' i" := (v (GRing.zero (Zp_zmodType O)) i) : ring_scope.

Definition combination (R : numDomainType)  (T : lmodType R) n
    (f : 'I_n.+1 -> R) (v : 'rV[T]_n.+1) : T :=
  \sum_(i < n.+1) f i *: v ``_ i.

(* factors of a convex combination *)
#[short(type=convn)]
HB.structure Definition Convn (R : numDomainType) (n : nat) :=
  {f of isSum1 R n f & NonNegFun 'I_n.+1 f}.

From mathcomp Require Import finmap.

Definition linear_hull_rV
    (R : numDomainType) (T : lmodType R) n (v : 'rV[T]_n.+1) :=
  [set combination a v | a in [set: 'I_n.+1 -> R]].

Definition affine_hull_rV
    (R : numDomainType) (T : lmodType R) n (v : 'rV[T]_n.+1) :=
  [set combination a v | a in [set: affine R n]].

Definition convex_hull_rV
    (R : numDomainType) (T : lmodType R) n (v : 'rV[T]_n.+1) :=
  [set combination a v | a in [set: convn R n]].

Definition vec_in_fset (R : numDomainType) (T : lmodType R)
  n (v : {fset T}) :=
  [set w : 'rV[T]_n.+1 | [forall i, w ``_ i \in v] ].

Definition convex_hull
    (R : numDomainType) (T : lmodType R) (v : {fset T}) :=
  \bigcup_n [set combination a w | a in [set: convn R n] &
                                   w in vec_in_fset v].

Lemma convex_hull_rVE
    (R : numDomainType) (T : lmodType R) n (v : 'rV[T]_n.+1) :
  convex_hull_rV v =
  convex_hull [fset v ``_ k | k in 'I_n.+1]%fset.
Proof.
apply/seteqP; split.
  move=> _ [a _ <-].
  rewrite /convex_hull; exists n => //=; exists a => //=; exists v => //.
  rewrite /vec_in_fset/=; apply/forallP => /= i.
  by apply/imfsetP; exists i.
move=> _ [m _]/= [a _ [w/=] /forallP/= vw <-].
rewrite /convex_hull_rV/=.
Admitted.

Definition cone_rV
    (R : numDomainType) (T : lmodType R) n (v : 'rV[T]_n.+1) :=
  [set combination a v | a in [set: {nnfun 'I_n.+1 >-> R}]].

(* Bernstein polynomials *)
Definition Bern (R : numDomainType) n (i : 'I_n.+1) : {poly R} :=
  bernp 0 1 n i.

Lemma BernE (R : numDomainType) n (i : 'I_n.+1) :
  Bern R i = 'X ^+ i * (1 - 'X) ^+ (n - i) *+ 'C(n, i).
Proof. by rewrite /Bern /bernp !(subr0,expr1n,invr1,mul1r). Qed.

Lemma Bern_bernp (R : numFieldType) n (i : 'I_n.+1) (a b x : R) :
  a != b -> (i <= n)%N ->
  (Bern R i).[factor a b x] = (bernp a b n i).[x].
Proof.
move=> ab ni.
rewrite BernE/= /bernp !(hornerMn,hornerE,horner_exp,hornerE); congr (_ *+ _).
rewrite factorE// !expr_div_n !mulrA mulrC !mulrA; congr (_ * _).
rewrite mulrC mulrA; congr (_ * _).
rewrite exprB// ?unitfE ?subr_eq0 1?eq_sym// mulrC invf_div mulrC mulrA -exprVn.
rewrite -exprMn_comm; last by rewrite /GRing.comm mulrC.
by rewrite mulVf ?subr_eq0 1?eq_sym// expr1n div1r.
Qed.

Lemma Bern_sum1 (R : numDomainType) n x : \sum_(k < n.+1) (Bern R k).[x] = 1.
Proof.
transitivity ((((1 - 'X) + 'X) ^+ n).[x]).
  rewrite exprDn horner_sum;  apply: eq_bigr => /= i _.
  by rewrite BernE; rewrite mulrC.
by rewrite horner_exp !hornerE subrK expr1n.
Qed.

Lemma Bern_ge0 (R : numDomainType) n (x : prob R) :
  forall k :'I_n.+1, 0 <= (Bern R k).[x : R].
Proof.
move=> k; rewrite BernE hornerMn !hornerE mulrn_wge0//.
by rewrite !horner_exp mulr_ge0// !hornerE ?exprn_ge0// ?subr_ge0.
Qed.

Definition eval_Bern (R : numDomainType) n (x : prob R) (i : 'I_n.+1) : R :=
  (Bern R i).[x : R].

HB.instance Definition _ (R : numDomainType) n (x : prob R) :=
  @isSum1.Build R n (@eval_Bern R n x) (Bern_sum1 n (x : R)).

HB.instance Definition _ (R : numDomainType) n (x : prob R) :=
  @IsNonNegFun.Build _ R (@eval_Bern R n x) (@Bern_ge0 R n x).

Definition Bezier_curve
    (R : numDomainType) (T : lmodType R) n (v : 'rV[T]_n.+1) : set T :=
  [set combination (fun i => (Bern R i).[t : R]) v | t in [set: prob R]].

Lemma Bezier_curve_convex_hull
    (R : numDomainType) (T : lmodType R) n (v : 'rV[T]_n.+1) :
  forall p, p \in Bezier_curve v -> p \in convex_hull_rV v.
Proof.
move=> p.
rewrite in_setE /Bezier_curve/= => -[t _ <-].
rewrite in_setE/=.
rewrite convex_hull_rVE.
rewrite /convex_hull.
exists n => //=.
exists [the convn R n of eval_Bern t] => //.
exists v => //.
apply/forallP => /= i.
apply/imfsetP.
by exists i.
Qed.

Section BernsteinPols.
Variables (R : rcfType) (a b : R) (deg : nat).
Hypothesis neqab : a != b.

Definition relocate (q : {poly R}) : {poly R}:=
  let s := size q in
    (* 1st case : degree of q is too large for the current basis choice *)
  if (deg.+1 < s)%N then 0
    else
  (recip deg ((q \shift (- 1)) \scale (b - a))) \shift - a.

Lemma recipE (q : {poly R}) : (size q <= deg.+1)%N ->
  recip deg q = \poly_(i < deg.+1) q`_(deg - i).
Proof.
move=> sq.
have t : forall n m (E : nat -> R), 'X ^+ n * \poly_(i < m) E i =
          \poly_(i < m + n) (E (i - n)%N *+ (n <= i)%N).
  elim=> [ | n IH] m E.
    rewrite expr0 mul1r addn0; rewrite !poly_def; apply: eq_bigr => i _.
    by rewrite subn0 leq0n mulr1n.
  rewrite exprS -mulrA IH !poly_def.
  rewrite addnS big_ord_recl.
  rewrite [X in _ *+ (n < X)]/nat_of_ord /= mulr0n scale0r add0r big_distrr.
  apply: eq_bigr; move=> [i ci] _ /=; rewrite /bump leq0n add1n ltnS subSS.
  by rewrite mulrC -scalerAl exprS mulrC.
rewrite /recip t subnKC // !poly_def; apply: eq_bigr.
move=> [i ci] _ /=; congr (_ *: _).
case h : (deg.+1 - size q <= i)%N.
  rewrite mulr1n; congr (q`_ _); apply/eqP.
  rewrite -(eqn_add2r (i - (deg.+1 - size q)).+1) subnK; last first.
    by rewrite -(ltn_add2r (deg.+1 - size q)) subnK // addnC subnK.
  rewrite -subSn // addnBA; last by apply/(leq_trans h)/leqnSn.
  by rewrite addnS subnK // subKn.
move/negP: h;move/negP; rewrite -ltnNge => h.
rewrite mulr0n nth_default //.
rewrite -(leq_add2r i.+1) -subSS subnK //.
by rewrite addnC -(subnK sq) leq_add2r.
Qed.

Lemma size_recip (q : {poly R}) :
  (size q <= deg.+1 -> size (recip deg q) <= deg.+1)%N.
Proof. by move=> s; rewrite recipE // size_poly. Qed.

Lemma poly_extend (m n : nat) (E : nat -> R) :
  (m <= n)%N -> (forall i : nat, (m <= i < n)%N -> E i = 0) ->
  \poly_(i < m) E i = \poly_(i < n) E i.
Proof.
move=> c e; rewrite !poly_def.
rewrite (big_ord_widen n (fun i => E i *: 'X^i) c) big_mkcond /=.
apply: eq_bigr; move=> [i ci] _ /=; case h: (i < m)%N => //.
rewrite e; first by rewrite scale0r.
by rewrite ci andbT leqNgt h.
Qed.

Lemma recipK (q : {poly R}) : (size q <= deg.+1)%N ->
   recip deg (recip deg q) = q.
Proof.
move=> s; rewrite recipE; last by rewrite size_recip.
rewrite -{2}[q]coefK (poly_extend s).
  apply: poly_ext => i c; rewrite recipE // coef_poly.
  rewrite subKn; last by rewrite -ltnS.
  by rewrite (leq_ltn_trans _ (ltnSn deg)) // leq_subr.
by move=> i c; rewrite nth_default //; case/andP: c.
Qed.

Lemma recipD : forall q1 q2 : {poly R}, (size q1 <= deg.+1)%N ->
   (size q2 <= deg.+1)%N -> recip deg (q1 + q2) = recip deg q1 + recip deg q2.
Proof.
move=> q1 q2 s1 s2; rewrite !recipE // ?poly_def; last first.
  by rewrite (leq_trans (size_add _ _)) // geq_max s1 s2.
have t : forall i : 'I_deg.+1, true -> (q1 + q2)`_(deg.+1 - i.+1) *: 'X^i =
                 q1`_(deg.+1 - i.+1) *: 'X^i + q2`_(deg.+1 - i.+1) *: 'X^i.
  by move=> [i ci] _ /=; rewrite coef_add_poly scalerDl.
by rewrite (eq_bigr _ t) big_split.
Qed.

Lemma recipZ (q : {poly R}) c :
  (size q <= deg.+1)%N -> recip deg (c *: q) = c *: recip deg q.
Proof.
move=> s; rewrite !recipE // ?poly_def; last first.
  case h : (c == 0); first by rewrite (eqP h) scale0r size_poly0.
  by rewrite size_scale ?h.
rewrite -[_ *: (\sum_(_ < _) _)]mul_polyC big_distrr; apply:eq_bigr.
by move=> [i ci] _ /=; rewrite coefZ mul_polyC scalerA.
Qed.

Lemma recipP (q : {poly R}) : size q = deg.+1 ->
  recip deg q = reciprocal_pol q.
Proof. by move=> s; rewrite /recip s subnn expr0 mul1r. Qed.

Lemma recip_scale_swap (q : {poly R}) c : c != 0 -> (size q <= deg.+1)%N ->
  recip deg (q \scale c) = (c ^+ deg)%:P * recip deg q \scale c^-1.
Proof.
move=> c0 sz; rewrite !recipE //; last by rewrite size_scaleX.
rewrite !poly_def big_distrr /=.
rewrite [_ \scale c^-1]/scaleX_poly linear_sum; apply: eq_bigr.
move=> [i ci] _ /=; rewrite scaleX_polyE coef_poly.
case h: (deg - i < size q)%N; last first.
  rewrite scale0r nth_default; last by rewrite leqNgt h.
  by rewrite scale0r mulr0 comp_poly0.
rewrite comp_polyM comp_polyC comp_polyZ poly_comp_exp comp_polyX.
rewrite (mulrC 'X) exprMn scalerAl -!mul_polyC -!polyC_exp mulrA -!polyCM.
rewrite mulrA mulrAC [q`_ _ * _]mulrC; congr (_ %:P * _); congr (_ * _).
case h' : (i < deg)%N; first by rewrite exprVn expfB.
have -> : i = deg by apply/eqP; move: ci; rewrite ltnS leq_eqVlt h' orbF.
by rewrite subnn expr0 exprVn mulfV // expf_neq0.
Qed.

Lemma bern_coeffs_mon : forall i, (i <= deg)%N ->
  relocate 'X^i = ((b - a)^+deg * 'C(deg, i)%:R^-1)%:P * bernp a b deg (deg - i)%N.
Proof.
have nsba0 : ~~ (b - a == 0) by rewrite subr_eq0 eq_sym.
move=> i leqip.
rewrite /bernp polyCM mulrAC -mulr_natr !mulrA -polyCM mulfV; last first.
  by rewrite expf_eq0 (negbTE nsba0) andbF.
rewrite mul1r -!mulrA -polyCMn -polyCM bin_sub // mulfV; last first.
  by rewrite pnatr_eq0 -lt0n bin_gt0.
rewrite subKn // mulr1.
rewrite /relocate /recip size_polyXn ltnNge ltnS leqip /= shift_polyXn.
have -> // : forall c : R, c != 0 ->
  (('X + (-1)%:P)^+ i) \scale c = ('X * c%:P + (-1)%:P)^+ i.
  move=> c hc; rewrite scaleX_polyE size_factor_expr.
  rewrite [(_ * _ + _) ^+ _]exprDn.
  rewrite (reindex_inj rev_ord_inj) /=.
  rewrite power_monom poly_def; apply: eq_bigr => j _.
  rewrite coef_poly subSS; have -> : (j < i.+1)%N by case j.
  rewrite subKn; last by case j.
  rewrite exprMn_comm; last by exact: mulrC.
  rewrite -mulrA (mulrCA 'X^j) (mulrC 'X^j) -!polyC_exp !mul_polyC.
  by rewrite scalerA !scalerMnl -(mulrC (c ^+ j)) mulrnAr bin_sub //; case j.
have -> // : forall c:R, c != 0 ->
  reciprocal_pol (('X * c%:P + (-1)%:P) ^+ i) = (c%:P - 'X)^+i.
  move=> c hc; rewrite reciprocalX reciprocal_monom // addrC.
  by congr ((_ + _) ^+ _); rewrite mulrC mul_polyC scaleNr scale1r.
rewrite size_amul_expr // subSS /shift_poly comp_polyM !poly_comp_exp.
rewrite comp_polyD linearN /= !comp_polyX comp_polyC opprD -!polyCN opprK.
by rewrite polyCB addrAC !addrA addrK.
Qed.

Lemma scaleS (p : {poly R}) (u v : R) :
  (p \scale u) \scale v = p \scale (u * v).
Proof.
rewrite /scaleX_poly -comp_polyA comp_polyM !comp_polyC comp_polyX.
by rewrite -mulrA -polyCM [v * u]mulrC.
Qed.

Lemma scaleZ (p : {poly R}) u v : (u *: p) \scale v = u *: (p \scale v).
Proof.
by rewrite /scaleX_poly linearZ.
Qed.

Lemma scaleD (p q : {poly R}) u : (p + q) \shift u = p \shift u + (q \shift u).
Proof.
by rewrite /scaleX_poly linearD.
Qed.

(* TODO : move to another section and abstract over deg a b, maybe *)
Lemma recip0 : recip deg (0 :{poly R}) = 0.
Proof.
rewrite recipE; last by rewrite size_poly0.
by rewrite poly_def; apply: big1 => i _; rewrite polyseq0 nth_nil scale0r.
Qed.

Lemma Mobius0 : Mobius deg a b (0 : {poly R}) = 0.
Proof.
by rewrite /Mobius /shift_poly linear0 /scaleX_poly !linear0 recip0 linear0.
Qed.

Lemma recip_weighted_sum n (f : nat -> R) (g : nat -> {poly R}) :
  (forall i : 'I_n, (size (g i) <= deg.+1)%N) ->
  recip deg (\sum_(i < n) f i *: g i) = \sum_(i < n) f i *: (recip deg (g i)).
Proof.
elim: n => [ | n IH cg]; first by rewrite !big_ord0 recip0.
rewrite !big_ord_recr /=.
rewrite recipD; first last.
    case fn0 : (f n == 0); first by rewrite (eqP fn0) scale0r size_poly0.
    by rewrite size_scale ?fn0 // (cg ord_max).
  apply: size_weighted_sum_leq.
  by move=> [i ci] _; apply: (cg (Ordinal _)); rewrite ltnS ltnW.
rewrite IH ?recipZ //; first by apply: (cg ord_max).
by move=> [i ci]; apply: (cg (Ordinal _)); rewrite ltnS ltnW.
Qed.

Lemma recip_sum n (g : nat -> {poly R}) :
  (forall i : 'I_n, (size (g i) <= deg.+1)%N) ->
  recip deg (\sum_(i < n) g i) = \sum_(i < n) recip deg (g i).
move=> cg; have bigc : forall i : 'I_n, true -> g i = 1 *: g i.
  by move=> i _; rewrite scale1r.
rewrite (eq_bigr _ bigc).
rewrite (recip_weighted_sum (fun i => 1%R)); last by [].
by apply: eq_bigr=> i _; rewrite scale1r.
Qed.

Lemma MobiusZ x (p : {poly R}) :
(* TODO: remove the size condition, but need to do it also for recipZ *)
   (size p <= deg.+1)%N ->
   Mobius deg a b (x *: p) = x *: Mobius deg a b p.
Proof.
move=> s; rewrite /Mobius /shift_poly /scaleX_poly /=.
rewrite !linearZ recipZ; last first.
  rewrite /= !size_comp_poly2 //; first by rewrite size_XaddC.
  by rewrite size_XmulC // subr_eq0 eq_sym.
by rewrite /= linearZ.
Qed.

Lemma Mobius_weighted_sum n (f : nat -> R) (g : nat -> {poly R}) :
  (forall i : 'I_n, (size (g i) <= deg.+1)%N) ->
  Mobius deg a b (\sum_(i < n) f i *: g i) =
  \sum_(i < n) f i *: Mobius deg a b (g i).
Proof.
rewrite /Mobius /shift_poly /scaleX_poly !linear_sum /= => cg.
have cbig : forall i: 'I_n, true ->
               ((f i *: g i) \Po ('X + a%:P) \Po 'X * (b - a)%:P) =
                       f i *: ((g i \Po ('X + a%:P)) \Po 'X * (b - a)%:P).
  by move=> i _; rewrite !linearZ.
rewrite (eq_bigr _ cbig).
rewrite (@recip_weighted_sum _ _ (fun i => (g i \shift a) \scale _));
  last first.
  move=> i; rewrite !size_comp_poly2; first by apply: cg.
    by apply: size_XaddC.
  by apply: size_XmulC; rewrite subr_eq0 eq_sym.
by rewrite linear_sum; apply: eq_bigr => i _; rewrite linearZ.
Qed.

Lemma relocate_weighted_sum n (f : nat -> R) (g : nat -> {poly R}) :
  (forall i : 'I_n, (size (g i) <= deg.+1)%N) ->
  relocate (\sum_(i < n) f i *: g i) = \sum_(i < n) f i *: relocate (g i).
Proof.
rewrite /relocate /shift_poly /scaleX_poly linear_sum /= => cg.
have s : (size (\sum_(i < n) (f i *: g i))%R <= deg.+1)%N.
  apply: (leq_trans (size_sum _ _ _)).
  by apply/bigmax_leqP => i _; apply/(leq_trans (size_scale_leq _ _))/cg.
rewrite ltnNge s linear_sum /=.
have s' : forall i : 'I_n,
   (size (f i *: g i \Po ('X + (-1)%:P) \Po ('X * (b - a)%:P))%R <= deg.+1)%N.
  move=> i; rewrite !size_comp_poly2.
      by apply/(leq_trans (size_scale_leq _ _))/cg.
    by apply: size_XaddC.
   by apply: size_XmulC; rewrite subr_eq0 eq_sym.
rewrite (@recip_sum _ (fun i => (f i *: g i \shift -1) \scale (b - a)) s').
rewrite linear_sum.
apply: eq_bigr => i _ /=.
rewrite ltnNge cg /=.
rewrite /shift_poly /scaleX_poly !linearZ recipZ ?linearZ //=.
rewrite !size_comp_poly2 //; first by apply: size_XaddC.
by apply: size_XmulC; rewrite subr_eq0 eq_sym.
Qed.

Lemma scalep1 (p : {poly R}) : p \scale 1 = p.
Proof.
by rewrite /scaleX_poly mulr1 comp_polyXr.
Qed.

Lemma MobiusK (q : {poly R}) : (size q <= deg.+1)%N ->
  Mobius deg a b (relocate q) = (b-a) ^+deg *: q.
Proof.
move=> s; rewrite /relocate /Mobius ltnNge s /= /shift_poly.
rewrite -[X in (_ \Po (_ + _)) \Po (_ + X%:P)]opprK [(- - _)%:P]polyCN.
have ba : b - a != 0 by rewrite subr_eq0 eq_sym.
have bav : (b - a)^-1 != 0 by rewrite invr_eq0.
have s1 : (size (q \Po ('X + (-1)%:P)) <= deg.+1)%N.
  by rewrite size_comp_poly2 // size_XaddC.
have rr : GRing.rreg ((b - a) ^+ deg).
  by rewrite /GRing.rreg; apply: mulIf; rewrite expf_eq0 (negbTE ba) andbF.
rewrite comp_polyXaddC_K !recip_scale_swap //; last first.
    by rewrite size_scaleX // mulrC rreg_size ?size_recip.
  by rewrite mulrC rreg_size ?size_recip.
rewrite !mul_polyC recipZ; last first.
  by apply: size_recip; rewrite size_comp_poly2 // size_XaddC.
rewrite !scalerA exprVn mulVf ?scale1r; last first.
  by rewrite expf_eq0 (negbTE ba) andbF.
rewrite invrK recipK; last by rewrite size_comp_poly2 // size_XaddC.
rewrite !scaleZ scaleS mulfV // scalep1 linearZ /=.
rewrite -[X in (_ \Po _) \Po (_ + X%:P)]opprK (polyCN (-1)).
by rewrite comp_polyXaddC_K.
Qed.

Lemma relocateK (q : {poly R}) : (size q <= deg.+1)%N ->
  relocate (Mobius deg a b q) = (b-a) ^+deg *: q.
Proof.
move=> s; rewrite /relocate /Mobius.
rewrite size_comp_poly2; last by rewrite size_XaddC.
set sc := ((q \shift _) \scale _).
set sz := size _.
have dif : b - a != 0 by rewrite subr_eq0 eq_sym.
have t : (size sc <= deg.+1)%N.
  by rewrite size_scaleX // size_comp_poly2 //; apply: size_XaddC.
have t' : (sz <= deg.+1)%N by apply: size_recip.
rewrite ltnNge t' /= -shift_polyD addNr.
rewrite [_ \shift 0]/shift_poly addr0 comp_polyXr.
(* TODO: we miss a scaleX_poly_linear canonical structure.
  and lemma about composing scale operations. *)
rewrite recip_scale_swap // recipK // /sc mul_polyC /scaleX_poly linearZ /=.
rewrite -comp_polyA comp_polyM comp_polyX comp_polyC -mulrA -polyCM.
by rewrite mulVf // mulr1 comp_polyXr linearZ /= shift_polyDK.
Qed.

Lemma relocate0 (p : {poly R}) : (size p <= deg.+1)%N ->
  (relocate p == 0) = (p == 0).
move=> s; apply/idP/idP; last first.
  move/eqP=> ->; rewrite /relocate /shift_poly /scaleX_poly !linear0.
  by rewrite size_poly0 ltn0 recip0 linear0.
have bmax : (b - a) ^+ deg != 0 by rewrite expf_neq0 // subr_eq0 eq_sym.
move/eqP=> r0; rewrite -[p]mul1r -[1]/1%:P -(mulVf bmax) polyCM -mulrA.
rewrite !mul_polyC -MobiusK // r0 /Mobius /shift_poly /scaleX_poly !linear0.
by rewrite recip0 linear0 scaler0.
Qed.

Lemma Mobius_bernp i : (i <= deg)%N ->
  Mobius deg a b (bernp a b deg i) = ('C(deg, i))%:R *: 'X ^+ (deg - i).
Proof.
move=> ci; set u := _%:R; rewrite -(mul1r (bernp a b deg i)) -[1]/(1%:P).
have t : (b - a)^+deg/('C(deg, i))%:R != 0.
  apply: mulf_neq0; first by rewrite expf_neq0 // subr_eq0 eq_sym.
  by rewrite invr_neq0 // pnatr_eq0 -lt0n bin_gt0.
rewrite -(mulVf t) {t} polyCM -mulrA.
rewrite -bin_sub // -[X in bernp a b deg X](subKn ci) -bern_coeffs_mon; last first.
  by rewrite leq_subr.
rewrite mul_polyC MobiusZ.
  rewrite MobiusK; last first.
    by rewrite size_polyXn ltnS leq_subr.
  rewrite invfM scalerA mulrAC mulVf; last first.
    by rewrite expf_neq0 // subr_eq0 eq_sym.
  by rewrite mul1r invrK bin_sub.
(* TODO : make a seprate lemma from this goal. *)
rewrite /relocate.
rewrite ltnNge size_polyXn (leq_ltn_trans _ (ltnSn _)) ?leq_subr //=.
rewrite size_comp_poly2; last by rewrite size_XaddC.
rewrite size_recip // !size_comp_poly2 //.
    by rewrite size_polyXn (leq_ltn_trans _ (ltnSn _)) // leq_subr.
  by rewrite size_XaddC.
by rewrite size_XmulC // subr_eq0 eq_sym.
Qed.

Lemma monomial_free n (l : nat -> R):
  \sum_(i < n) l i *: 'X ^+i == 0 -> forall i, (i < n)%N -> l i = 0.
Proof.
elim:n => [ | n IH] /=; first by move=> _ i; rewrite ltn0.
rewrite big_ord_recr /=.
case r : (l n == 0).
  rewrite (eqP r) scale0r addr0; move/IH=>{IH} II i.
  rewrite ltnS leq_eqVlt =>/orP; case.
    by move/eqP=> ->;apply/eqP.
  by apply: II.
rewrite addr_eq0 => abs.
case/negP: (negbT (ltnn n)).
rewrite [X in (X <= _)%N](_ : _ = size (l n *: 'X^n)); last first.
  by rewrite -mul_polyC size_Cmul ?r // size_polyXn.
rewrite -size_opp -(eqP abs) size_weighted_sum_leq //.
by move=> [i ci]; rewrite /= size_polyXn.
Qed.

Lemma bernp_free : forall (l : nat -> R),
   \sum_(i < deg.+1) l i *: bernp a b deg i = 0 -> forall i : 'I_deg.+1, l i = 0.
Proof.
have bman0 : b - a != 0 by rewrite subr_eq0 eq_sym.
move/(expf_neq0 deg): (bman0) => bmadeg.
move=> l; rewrite -[X in X = 0]scale1r -(mulVf bmadeg) -scalerA.
rewrite -relocateK; last first.
  apply (leq_trans (size_sum _ _ _)); apply/bigmax_leqP.
  move=> i _; apply: (leq_trans (size_scale_leq _ _)).
  by rewrite size_bernp ?leqnn //; case : i => i /=; rewrite ltnS.
move/eqP; rewrite scaler_eq0 invr_eq0 (negbTE bmadeg) orFb.
have t : forall i : 'I_deg.+1, (size (bernp a b deg i) <= deg.+1)%N.
  by move=> [i ci] /=; rewrite size_bernp.
rewrite (Mobius_weighted_sum l t) {t}.
have xdi : forall i, (i < deg.+1)%N -> size (('X : {poly R}) ^+i) = i.+1.
  by move=> i; rewrite -['X]subr0 size_exp_XsubC.
have  t: forall i : nat, (i < deg.+1)%N -> Mobius deg a b (bernp a b deg i) =
                     ('C(deg, i)%:R)%:P * 'X ^+ (deg - i).
  move=> i ci.
  rewrite (_ : bernp a b deg i =
            ('C(deg, i)%:R / (b - a)^+ deg)%:P *
             (((b - a) ^+ deg / 'C(deg, deg - i)%:R)%:P *
                 bernp a b deg (deg - (deg - i)))); last first.
    rewrite mulrA -polyCM !mulrA mulfVK //.
    rewrite bin_sub // mulfV ?mul1r ?subKn // pnatr_eq0.
    by rewrite -lt0n bin_gt0.
  have di : (deg - i <= deg)%N by rewrite leq_subr.
  rewrite -bern_coeffs_mon // !mul_polyC MobiusZ; last first.
    rewrite /relocate /shift_poly /scaleX_poly xdi; last by rewrite ltnS.
    rewrite ltnNge ltnS di /=.
    rewrite size_comp_poly2; last by rewrite size_XaddC.
    rewrite size_recip // !size_comp_poly2 ?xdi ?ltnS //.
      by rewrite size_XaddC.
    by rewrite size_XmulC.
  by rewrite MobiusK ?xdi ?ltnS // -!mul_polyC mulrA -polyCM mulfVK.
rewrite relocate0; last first.
  have T : forall i : 'I_deg.+1,
               (size (Mobius deg a b (bernp a b deg i)) <= deg.+1)%N.
    move=> [i ci]; rewrite t //.
    rewrite size_Cmul; last by rewrite pnatr_eq0 -lt0n bin_gt0.
    by rewrite xdi; rewrite ltnS leq_subr.
    apply: size_weighted_sum_leq => i _; apply: T.
rewrite -(big_mkord (fun _ => true)
             (fun i => l i *: Mobius deg a b (bernp a b deg i))) big_nat_rev /= add0n.
have t' : forall i, (0 <= i < deg.+1)%N ->
               l (deg.+1 - i.+1)%N *: Mobius deg a b (bernp a b deg (deg.+1 - i.+1)) =
               (l (deg - i)%N * ('C(deg, deg - i))%:R) *: 'X^i.
  move=> i;case/andP=> _ ci.
  rewrite subSS t; last by rewrite ltnS leq_subr.
  by rewrite -!mul_polyC mulrA polyCM subKn.
rewrite (eq_big_nat _ _ t') big_mkord => t2.
have t3 := (@monomial_free _
                 (fun i => l (deg - i)%N * ('C(deg, deg - i))%:R) t2).
move=> [i ci] /=.
have t4 : ('C(deg, i))%:R != 0 :> R.
  by rewrite pnatr_eq0 -lt0n bin_gt0.
apply: (mulIf t4); rewrite mul0r.
have t5: (i <= deg)%N by rewrite -ltnS.
rewrite -(subKn t5); apply: t3.
by rewrite ltnS leq_subr.
Qed.

End BernsteinPols.

Section dicho_proofs.

Variable R : rcfType.

Lemma dicho'_delta_bern (a b m : R) k p (alpha := (b - m) * (b - a)^-1)
  (beta := ((m - a) * (b - a)^-1)) :
  a != b -> m != a -> (k <= p)%N ->
  bernp a b p k =
  \sum_(j < p.+1)((dicho' alpha beta  (delta R k) j)%:P * bernp a m p j).
Proof.
move=> dab dma hlt1.
rewrite -(big_mkord
(fun _ => true)
(fun j => (dicho' alpha beta (delta R k) j)%:P * bernp a m p j)).
rewrite (big_cat_nat _ _ _ (leq0n k)) //=; last by apply: leq_trans hlt1 _; exact: leqnSn.
rewrite (_ : \sum_( _ <= i0 < _ ) _ = 0) /= ?add0r; last first.
  rewrite big1_seq //= => j; rewrite mem_iota add0n subn0; case/andP=> _ h.
  by rewrite dc_delta_head // polyC0 mul0r.
rewrite -{2}(add0n k) big_addn.
have h : forall i0, (0 <= i0 < p - k)%nat ->
  (dicho' (m - a) (b - m) (delta R k) (i0 + k))%:P * bernp a m p (i0 + k) =
   (( (m - a) ^+ i0) * (b - m) ^+ k)%:P * bernp a m p (i0 + k) *+ 'C(i0 + k, k).
  by move=> j h; rewrite /dicho' addnC dc_delta_tail polyCMn -mulrnAl addnC.
have -> : bernp a b p k =
          (('X - a%:P)^+k * ((b - a)^-k)%:P) *
          ((b%:P  - 'X )^+(p - k) * ((b - a)^-(p - k))%:P) *+'C(p, k).
  rewrite /bernp -!mulrA. congr (_ *+ _).
  rewrite [_ * (_)%:P]mulrC [((b - a)^-k)%:P * _]mulrA -polyCM.
  by rewrite -invfM -exprD subnKC // !mulrA [_ %:P * _]mulrC.
have -> : (('X - a%:P) ^+ k * ((b - a) ^- k)%:P) =
           (beta^+k)%:P * (('X - a%:P) ^+ k * ((m - a) ^- k)%:P).
  rewrite /beta expr_div_n polyCM !mulrA -[_ * (_ ^+k)]mulrC !mulrA mulrAC.
  rewrite -!mulrA -polyCM mulfV ?polyC1 ?mulr1 ?expf_eq0 ?subr_eq0 //.
  by move/negPf: dma => ->; rewrite andbF.
rewrite -(exprVn (b - a)) [(_ ^-1 ^+ _)%:P]polyC_exp.
rewrite -exprMn_comm; last by exact: mulrC.
have -> : (b%:P - 'X) * ((b - a)^-1)%:P =
   ((m%:P - 'X) * (m - a)^-1%:P) + (alpha%:P * ('X - a%:P) * (m - a)^-1%:P).
 (* a ring tactic would be nice here *)
  rewrite [(m%:P - _) * _]mulrDl mulrDr [(alpha%:P * _ + _) * _]mulrDl.
  rewrite (mulrC _ 'X) -(mulrA 'X) [_ + (- 'X * _)]addrC mulNr -mulrN.
  rewrite addrAC addrA -mulrDr -mulN1r -mulrDl.
  rewrite -(polyCN 1) -polyCD /alpha.
  have -> : -1 = (a-b)/(b-a).
    by rewrite -opprB mulNr mulfV // subr_eq0 eq_sym.
  rewrite -mulrDl addrA addrNK -(opprB m a).
  rewrite -polyCM !mulNr mulrAC mulfV ?mul1r; last by rewrite subr_eq0.
  rewrite polyCN -addrA -mulrDl [_ * - a%:P]mulrC -[-a%:P]polyCN.
  rewrite -polyCM -polyCD !mulrA.
  have {2}-> : m = m * (b - a) / (b - a) by rewrite mulfK // subr_eq0 eq_sym.
  rewrite -[_ + _ /(b-a)]mulrDl !mulrDr addrA addrAC [-a * -m]mulrN.
  rewrite [-a * m]mulrC addrNK [_ + m * b]addrC -mulrDl -polyCM.
  rewrite [_ * b]mulrC mulrAC mulfK; last by rewrite subr_eq0.
  by rewrite mulrN -mulNr polyCM -mulrDl addrC.
rewrite [_^+ (p - k)]exprDn /= subSn //.
rewrite -(big_mkord (fun _ => true) (fun i => ((m%:P - 'X) * ((m - a)^-1)%:P) ^+ (p - k - i) *
       (alpha%:P * ('X - a%:P) * ((m - a)^-1)%:P) ^+ i *+ 'C(
       p - k, i))).
rewrite  big_distrr /= (big_morph  _ (mulrnDl ('C(p, k))) (mul0rn _ _)).
apply: congr_big_nat=> // i /= hi.
rewrite /dicho' [(i + k)%nat]addnC dc_delta_tail /bernp.
rewrite !mulrnAr polyCMn mulrnAl -!mulrnA; congr (_ *+ _); last first.
   rewrite addnC -util_C ?leq_addr //.
     by rewrite mulnC; congr (_ * _)%N;  rewrite addnC addnK.
   by move:hi; rewrite ltnS -(leq_add2l k) subnKC.
set Xa := ('X - a%:P); set Xb := (_ - 'X).
rewrite [alpha^+_ * _]mulrC [(beta^+_ * _)%:P]polyCM -!mulrA; congr (_ * _).
rewrite [(alpha%:P * _)]mulrC.
rewrite [(_ * alpha%:P)^+i]exprMn_comm; last by exact: mulrC.
set lhs := (alpha ^+ i)%:P * _; rewrite !mulrA.
rewrite [_ * alpha%:P ^+ i]mulrC /lhs polyC_exp; congr (_ * _)=> {lhs alpha}.
set lhs := _ * (_ * Xb ^+ (p - _)).
rewrite !exprMn_comm; try exact: mulrC.
rewrite [Xa^+i * _]mulrC !mulrA [_ * Xa^+ _]mulrC !mulrA.
rewrite -exprD /lhs [_ * (Xa^+ _ * _)]mulrA [_ * Xa^+ _]mulrC -!mulrA.
rewrite addnC; congr (_ * _)=> {lhs}.
rewrite !mulrA [_ * Xb^+ (p - k - i)]mulrC -!mulrA [Xb^+ _ * _]mulrC.
rewrite subnDA; congr (_ * _); rewrite -!polyC_exp -!polyCM; congr (_ %:P).
rewrite -!exprVn -!exprD; congr ((m -a)^-1 ^+ _).
rewrite subnK; last by [].
by rewrite addnC subnK; last by [].
Qed.

Lemma dicho'_correct : forall (a b m : R)(alpha := (b - m) * (b - a)^-1)
  (beta := ((m - a) * (b - a)^-1))(p : nat)(q : {poly R})(c : nat -> R),
  a != b ->
  m != a ->
  q = \sum_(i < p.+1) c i *: bernp a b p i ->
  q = \sum_(j < p.+1) dicho' alpha beta c j *: bernp a m p j.
Proof.
move=> a b m alpha beta p q c neqab neqma qdef.
have {neqma qdef} -> : q =
  \sum_(j < p.+1) \sum_(i < p.+1)
  (c i)%:P * (dicho' alpha beta (delta R i) j)%:P * bernp a m p j.
  rewrite exchange_big /= qdef; apply: congr_big; [by [] | by [] |].
  case=> k hk _ /=.
  have hk': (k <= p)%N by exact: hk.
  rewrite (dicho'_delta_bern neqab neqma hk').
  rewrite -mul_polyC big_distrr /=;  apply: congr_big; [by [] | by [] |].
  by case=> i hi _; rewrite !mulrA.
apply: congr_big; [by [] | by [] |].
case=> i hi _ /=;  rewrite -big_distrl /= -mul_polyC; congr (_ * _).
have -> : dicho' alpha beta c i =
  dicho' alpha beta (fun k => \sum_(j < p.+1)(c j) * (delta R j k)) i.
  apply: ext_dc=> k _; rewrite add0n => h.
  have pk : (k < p.+1)%N by apply: leq_ltn_trans hi.
  rewrite (bigD1 (Ordinal pk)) //= /delta eqxx mulr1 big1 ?addr0 //.
  case=> j hj /=; move/negPf; case e : (j == k); last by rewrite mulr0.
  suff : Ordinal hj = Ordinal pk by move/eqP->.
  by apply: val_inj=> /=; apply/eqP.
elim: p i {hi} c alpha beta=> [| p ihp] i c alpha beta /=; set f := dicho' alpha beta.
  rewrite big_ord_recl /= big_ord0 /dicho' /= addr0.
  rewrite /f /dicho'.
  have : forall k,
    (0 <= k)%N -> (k <= 0 + i)%N ->
    \sum_(j < 1) c j * delta R j k = (c 0%N) * (delta R 0) k.
    by move=> k _ _; rewrite  big_ord_recl /= big_ord0 addr0.
  by move/ext_dc->; rewrite scal_dc polyCM.
  rewrite (_ : f _ _ =
  f
  (fun k : nat =>
    (\sum_(j < p.+1) c j * delta R j k) + (c p.+1 * delta R p.+1 k)) i);
  last first.
  by apply: ext_dc=> k _; rewrite add0n=> hki; rewrite big_ord_recr.
rewrite /f /dicho' add_dc polyCD -ihp // big_ord_recr /=; congr (_ + _).
by rewrite scal_dc polyCM.
Qed.

Lemma bern_swap p i (l r : R) : (i <= p)%N -> bernp r l p i = bernp l r p (p - i).
Proof.
move=> lip; rewrite /bernp subKn // bin_sub //; congr (_ *+ _).
rewrite -[l - r]opprB -[l%:P - 'X]opprB -['X - r%:P]opprB.
rewrite -mulN1r -[-(r%:P - 'X)]mulN1r  -[- ('X - l%:P)]mulN1r.
rewrite !exprMn_comm; try exact: mulrC.
rewrite invfM polyCM [_ * ((r - l)^-p)%:P]mulrC.
rewrite -!mulrA; congr (_ * _).
rewrite  -exprVn polyC_exp [(- 1)^-1]invrN invr1 polyCN.
rewrite [(r%:P - 'X)^+i * _]mulrC !mulrA polyC1 -!exprD.
by rewrite -addnA subnKC // -signr_odd oddD addbb /= expr0 mul1r.
Qed.

Lemma bern_rev_coef : forall (p : nat)(a b : R)(c : nat -> R),
  \sum_(i < p.+1) c i *: (bernp a b p i) =
  \sum_(i < p.+1) c (p - i)%N *: (bernp b a p i).
Proof.
move=> p a b c.
pose t := \sum_(i < p.+1) c (p - i)%N *: bernp a b p (p - i)%N.
transitivity t.
  by rewrite (reindex_inj rev_ord_inj) /=; apply: eq_bigl.
apply:eq_bigr => [[i hi]] _ /=.
by rewrite bern_swap ?subKn // leq_subr.
Qed.

Lemma dicho_correct : forall (a b m : R)(alpha := (b - m) * (b - a)^-1)
  (beta := ((m - a) * (b - a)^-1))(p : nat)(q : {poly R})(c : nat -> R),
  a != b ->
  m != b ->
  q = \sum_(i < p.+1) c i *: bernp a b p i ->
  q = \sum_(j < p.+1) dicho alpha beta p c j *: bernp m b p j.
Proof.
move=> a b m alpha beta p q c neqab neqmb qdef.
rewrite bern_rev_coef in qdef.
have neqba : b != a by rewrite eq_sym.
rewrite (@dicho'_correct _ _ _ _ _ (fun i => c (p - i)%N) neqba neqmb qdef).
rewrite -(big_mkord
(fun _ => true) (fun j => dicho' ((a - m) / (a - b)) ((m - b) / (a - b))
         (fun i : nat => c (p - i)%N) j *: bernp b m p j)).
rewrite big_nat_rev /= big_mkord; apply: congr_big; [by [] | by [] |].
move=> [i hi] _ {qdef}; rewrite add0n subSS.
rewrite -bern_swap //; congr (_ *: _); rewrite /dicho' /dicho.
rewrite dc_reverse //= ?leq_subr // addn0 subKn //.
rewrite -opprB -[a - b]opprB -[a - m]opprB -mulN1r -[-(b - a)]mulN1r.
rewrite -[-(m - a)]mulN1r invfM [(- 1)^-1]invrN invr1 -mulrA.
rewrite [(b - m) * _]mulrC !mulrA mulNr mul1r opprK [-1 * _ ]mulrC 2!mulrN1.
by rewrite opprK -/beta mulrC mul1r.
Qed.

End dicho_proofs.

Section isolation_tree.

Variable A : Type.

Inductive root_info : Type :=
  | Exact (x : A)
  | One_in (x y : A)
  | Zero_in (x y : A)
  | Unknown (x y : A).

End isolation_tree.

Section isolation_algorithm.

Variable R0 : archiFieldType.

Let R := {realclosure R0}.

Definition head_root (f : R -> R) (l : seq (root_info R)) : Prop :=
  match l with
    [::] => True
  | Exact x::tl => True
  | One_in x y::tl => f x != 0
  | Zero_in x y::tl => f x != 0
  | Unknown x y::tl => f x != 0
  end.

Definition unique_root_for (f : R -> R) (x y : R) : Prop :=
  exists z, x < z < y /\ f z = 0 /\ (forall u, x < u < y -> f u = 0 -> u = z).

Definition no_root_for (f : R -> R) (x y : R) : Prop :=
  forall z, x < z < y -> f z != 0.

Fixpoint read (f : R -> R) (l : seq (root_info R)) : Prop :=
  match l with
    [::] => True
  | Exact x::tl => f x = 0 /\ read f tl
  | One_in x y::tl => unique_root_for f x y /\ head_root f tl /\ read f tl
  | Zero_in x y::tl => no_root_for f x y /\ head_root f tl /\ read f tl
  | Unknown x y::tl => read f tl
  end.

Fixpoint isol_rec n d a b (l : seq R) acc : seq (root_info R) :=
  match n with
    O => Unknown a b::acc
  | S p =>
    match changes (seqn0 l) with
    | 0%nat => Zero_in a b::acc
    | 1%nat => One_in a b::acc
    | _ =>
    let c := (a + b)/2%:R in
    let l2 := mkseq (dicho (2%:R^-1) (2%:R^-1) d (fun i => l`_i)) d.+1 in
    isol_rec p d a c (mkseq (dicho' (2%:R^-1) (2%:R^-1) (fun i => l`_i)) d.+1)
        (if l2`_0 == 0 then
           Exact c::isol_rec p d c b l2 acc
        else isol_rec p d c b l2 acc)
    end
  end.

Lemma cons_polyK : forall p : {poly R},
  cons_poly p.[0] (\poly_(i < (size p).-1) p`_i.+1) = p.
move=> p; rewrite cons_poly_def addrC -[X in _ = X]coefK.
case sz : (size p) => [ | s].
  move/eqP: sz; rewrite size_poly_eq0 => /eqP => sz.
  by rewrite sz horner0 polyC0 add0r /= polyseq0 !polyd0 mul0r.
rewrite [s.+1.-1]/= !poly_def big_ord_recl; congr (_ + _).
  by rewrite expr0 alg_polyC horner_coef0.
rewrite big_distrl; apply: eq_bigr; move=> [i ci] _ /=.
by rewrite -scalerAl /bump leq0n add1n exprS mulrC.
Qed.

Lemma poly_border (p : {poly R}) a b:
  a < b -> (forall x, a < x < b -> 0 < p.[x]) -> 0 <= p.[a].
Proof.
move=> ab cp; case p0: (p.[a] < 0); last by rewrite leNgt p0.
have := (cons_polyK (p \Po ('X + a%:P))); rewrite cons_poly_def.
have -> : (p \Po ('X + a%:P)).[0] = p.[a].
  by rewrite horner_comp hornerD hornerC hornerX add0r.
move=> qdec.
have : p = p \Po ('X + a%:P) \Po ('X - a%:P) by rewrite comp_polyXaddC_K.
rewrite -qdec comp_polyD comp_polyC comp_polyM comp_polyX.
set q := \poly_(_ < _) _; move=> pq.
have [ub pu] := (poly_itv_bound (q \Po ('X - a%:P)) a b).
have ub0 : 0 <= ub by rewrite (le_trans _ (pu a _)) // lexx andTb ltW.
set ub' := ub + 1.
have ub'0 : 0 < ub' by rewrite ltr_paddl.
have ublt : ub < ub' by rewrite ltr_spaddr // ltr01.
pose x := minr (a - p.[a]/ub') (half (a + b)).
have xitv2 : a < x < b.
  by case/andP: (mid_between ab)=> A B; rewrite lt_minr ltr_spaddr ?A //=
    ?lt_minl ?B ?orbT // -mulNr mulr_gt0 // ?invr_gt0 // oppr_gt0.
have xitv : a <= x <= b by case/andP: xitv2 => *; rewrite !ltW //.
have := cp _ xitv2.
rewrite [X in X.[x]]pq hornerD hornerC hornerM hornerXsubC.
rewrite -[X in 0 <  _ + X]opprK subr_gt0 => abs.
have : x - a <= -p.[a] / ub' by rewrite ler_subl_addl le_minl mulNr lexx.
rewrite -(ler_pmul2r ub'0) mulfVK; last first.
  by move:ub'0; rewrite lt0r=>/andP=>[[]].
have xma :0 < x - a by rewrite subr_gt0; case/andP: xitv2.
move: (pu _ xitv); rewrite lter_norml; case/andP => _ {pu}.
rewrite -[_ <= ub](ler_pmul2r xma) => pu2.
rewrite mulrC; have := (lt_le_trans abs pu2) => {pu2} {}abs ab'.
have := (le_lt_trans ab' abs); rewrite ltr_pmul2r // ltNge;case/negP.
by rewrite ltW.
Qed.

Lemma one_root1_unique :
  forall q a b, one_root1 q a b -> unique_root_for (horner q) a b.
Proof.
move=> q a b [c [d [k [itv]]]].
rewrite /pos_in_interval /neg_in_interval1 /slope_bounded2.
move=> itv1 itv2 sl.
case/andP: itv=> ac; case/andP=> cd; case/andP=> db k0.
have qd0 : q.[d] <= 0.
  have : (0 <= (-q).[d]).
    by apply: (poly_border db) => x xitv; rewrite hornerN lter_oppE itv2.
  by rewrite hornerN lter_oppE.
have qc0 : 0 <= q.[c] by apply/ltW/itv1; rewrite ac lexx.
have qcd0 : (-q).[c] <= 0 <= (-q).[d] by rewrite !hornerN !lter_oppE qd0 qc0.
have [x xin] := (poly_ivt (ltW cd) qcd0).
rewrite /root hornerN oppr_eq0 =>/eqP => xr.
exists x.
split.
  by case/andP: xin=> cx xd; rewrite (lt_le_trans ac cx) (le_lt_trans xd db).
split; first by [].
move=> u; case/andP=> au ub qu0.
case cu : (u <= c).
  have : a < u <= c by rewrite cu au.
  by move/itv1; rewrite qu0 ltxx.
case ud : (d < u).
  have : d < u < b by rewrite ud ub.
  by move/itv2; rewrite qu0 ltxx.
have cu' : c <= u.
  by apply: ltW; rewrite ltNge cu.
have ud' : u <= d.
  by rewrite leNgt ud.
case/andP: xin=> cx xd.
case ux : (u <= x).
  have := (sl _ _ cu' ux xd).
  rewrite qu0 xr subrr -(mulr0 k) ler_pmul2l // subr_le0 => xu.
  by apply/eqP; rewrite eq_le ux.
have xu : x <= u.
  by apply: ltW; rewrite ltNge ux.
  have := (sl _ _ cx xu ud').
  rewrite qu0 xr subrr -(mulr0 k) ler_pmul2l // subr_le0 => ux'.
by apply/eqP; rewrite eq_le ux'.
Qed.

Lemma alternate_1_neq0 (p : {poly R}) :
   alternate_1 p -> p != 0.
case/alternate_1P=> l1 [v [l2 [h1]]] _ _ _.
by rewrite -nil_poly h1 {h1}; case: l1 => //.
Qed.

Lemma all_ge0_cat {R'' : realDomainType} :
   {morph (@all_ge0 R'') : x y / x ++ y >-> x && y}.
Proof. by elim=> [ | a x IH y] //=; rewrite IH andbA. Qed.

Lemma alternate_r d (p : {poly R}) a :
  ( 0 < a) -> alternate p -> (size p <= d)%N -> alternate (p + a *: 'X ^+ d).
Proof.
move=> a0 /alternate_P [l1 [x [l2 [y [l3 [P1 P2 P3 P4]]]]]] ps.
apply/alternate_P; exists l1, x, l2, y.
exists (l3 ++ (mkseq (fun i => 0) (d - size p)) ++ [:: a]).
split => //; first last.
  case: P4 => P4 P5 P6; split=> //.
  rewrite !all_ge0_cat P6 andTb; apply/andP; split; last by rewrite /= ltW.
  by apply/(all_nthP 0); move => i; rewrite size_mkseq => W; rewrite nth_mkseq.
(* With "apply/all_nthP"
  The previous line introduces an existential that is uncaptured. *)
set m := mkseq _ _; set l := _ ++ _.
have reorg : l = p ++ m ++ [:: a] by rewrite P1 /m -!(catA, cat_cons).
have saxd : size (a *: 'X^d) = d.+1.
  by rewrite -mul_polyC size_Cmul ?size_polyXn; last rewrite neq_lt a0 orbT.
have spax : size (p + a *: 'X^d) = d.+1.
  by rewrite addrC size_addl // saxd ltnS.
have sreo : size (p ++ m) = d by rewrite size_cat /m size_mkseq addnC subnK.
apply: (@eq_from_nth _ 0).
  by rewrite spax reorg catA size_cat sreo /= addn1.
move=> i; rewrite spax ltnS leq_eqVlt=> ib; rewrite coef_add_poly coefZ.
case/orP: ib => [/eqP -> | iltd].
  rewrite [p`_d]nth_default // add0r coefXn eqxx mulr1 reorg catA.
  by rewrite nth_cat sreo ltnn subnn.
move: (iltd); rewrite coefXn ltn_neqAle=> /andP [df _]; rewrite (negbTE df).
rewrite mulr0 addr0 reorg catA nth_cat sreo iltd nth_cat.
case tst: (i < size p)%N => //.
rewrite /m nth_mkseq.
  by rewrite nth_default // leqNgt tst.
by rewrite ltn_subRL addnC subnK // leqNgt tst.
Qed.

Lemma all_eq0_seqn0  (l : seq R) : (head 0 (seqn0 l) == 0) = (all_eq0 l).
Proof.
elim: l=> [ | a l IH]; first by rewrite eqxx.
by rewrite /=; case a0: (a == 0) => //=.
Qed.

Lemma seqn0_last (l : seq R) : head 0 (seqn0 l) != 0 ->
  exists l1 x l2, [&& l == l1 ++ x :: l2, x != 0 & all_eq0 l2].
Proof.
elim: l => [ | a l IH] /=; first by rewrite eqxx.
case a0: (a == 0) => /=.
  move/IH=> [l1 [x [l2 /andP [p1 p2]]]]; exists (a::l1), x, l2.
  by rewrite (eqP p1) cat_cons eqxx p2.
move=> an0.
case h: (all_eq0 l).
  by exists nil, a, l; rewrite /= an0 h eqxx.
move/negbT: h.
rewrite -all_eq0_seqn0; move/IH=>[l1 [x [l2 /andP [p1 p2]]]].
by exists (a::l1), x, l2; rewrite (eqP p1) p2 cat_cons eqxx.
Qed.

Lemma first_neg_no_change_all_le0 (l : seq R) :
  head 0 (seqn0 l) < 0 -> changes (seqn0 l) = 0%N -> all_le0 l.
Proof.
elim: l=> [ | a l IH] //=; case a0: (a==0)=> /= hsn0.
  by rewrite le_eqVlt a0 /=; apply: IH => //; apply/eqP.
case h0: (head 0 (seqn0 l) == 0); move: (h0).
  rewrite all_eq0_seqn0 (ltW hsn0) /= => al0 _.
  by move: al0; apply: sub_all => x x0; rewrite (eqP x0) lexx.
move=> _ /eqP; rewrite (ltW hsn0) addn_eq0 /= => /andP [p1]/eqP.
apply: IH.
rewrite lt_neqAle h0 /= -(ler_nmul2l hsn0) mulr0.
by move: p1; rewrite eqb0 ltNge negbK.
Qed.

Lemma first_pos_no_change_all_ge0 (l : seq R) :
  0 <= head 0 (seqn0 l) -> changes (seqn0 l) = 0%N -> all_ge0 l.
Proof.
elim: l=> [ | a l IH] //=; case a0: (a==0)=> /= hsn0.
  by rewrite le_eqVlt eq_sym a0 /=; apply: IH => //; apply/eqP.
case h0: (head 0 (seqn0 l) == 0); move: (h0).
  rewrite all_eq0_seqn0 hsn0 /= => al0 _.
  by move: al0; apply: sub_all => x x0; rewrite (eqP x0) lexx.
move=> _ /eqP; rewrite hsn0 addn_eq0 /= => /andP [p1]/eqP.
apply: IH.
have hsn0' : 0 < a by rewrite lt_neqAle eq_sym a0.
rewrite  -(ler_pmul2l hsn0') mulr0.
by move: p1; rewrite eqb0 ltNge negbK.
Qed.

Lemma changes1_alternate d (l : seq R) f : (size l <= d.+1)%N ->
         (forall i, (i < d.+1)%N -> (0 < f i)) ->
         changes (seqn0 l) = 1%N -> 0 <= (seqn0 l)`_0 = true ->
         alternate (\sum_(i < d.+1) (l`_i * f i *: 'X^(d - i))).
Proof.
elim: d l f => [| d IH] /=.
  case => /= [ | a [ | *]] // f cf _.
  case: (a != 0) => //=; by rewrite mulr0 ltxx addn0.
case => [| a l] //= f; rewrite ltnS.
case h: (a!=0) => //=; last first.
  rewrite -[X in 0 <= X]/((seqn0 l)`_0) => h1 h2 h3 h4.
  rewrite big_ord_recl /=.
  have := negbFE h => /eqP => ->; rewrite mul0r scale0r add0r.
  have t : forall i : 'I_d.+1, true ->
               l`_i * f (bump 0 i) *: 'X^(d.+1 - bump 0 i) =
                 l`_i * f (i.+1) *: 'X^(d - i).
    by move=> i /=; rewrite /bump leq0n add1n subSS.
  rewrite (eq_bigr _ t) {t}.
  have h2' : forall i : nat, (i < d.+1)%N -> (0 < f i.+1).
    by move=> i ci; apply: h2; rewrite ltnS.
  by apply: IH h2' _ _.
case alt: (a * head 0 (seqn0 l) < 0)%R; last first.
  rewrite add0n => h1 h2 h3 h4.
  have h2' : forall i : nat, (i < d.+1)%N -> (0 < f i.+1).
    by move=> i ci; apply: h2; rewrite ltnS.
  have alt' : alternate (\sum_(i < d.+1) (l`_i * f i.+1) *: 'X^(d - i)).
    apply: (IH l (fun i => f i.+1)) => //.
    have agt0 : 0 < a by rewrite lt_neqAle eq_sym (negbTE h).
    rewrite -(ler_pmul2l agt0) mulr0 leNgt; apply: negbT; exact alt.
  rewrite big_ord_recl subn0 nth0 /= addrC; apply: alternate_r => //.
    rewrite pmulr_lgt0; first by rewrite lt_neqAle eq_sym h h4.
    by apply: h2.
  have asl : forall i : 'I_d.+1,
                (size (('X^(d.+1 - bump 0 i):{poly R})) <= d.+1)%N.
    by move=> i; rewrite /bump leq0n add1n subSS size_polyXn ltnS leq_subr.
  apply: size_weighted_sum_leq=> i _; apply: asl.
rewrite add1n; move=> sl cf [c0] ap.
have negl : head 0 (seqn0 l) < 0.
  have ap' : 0 < a by rewrite lt_neqAle eq_sym h ap.
  by rewrite -(ltr_pmul2l ap') mulr0 alt.
have int: head 0 (seqn0 l) != 0 by rewrite neq_lt negl.
move/seqn0_last: (int) => [l1 [x [l2 /andP [/eqP p1 /andP[p2 p3]]]]].
apply/alternate_P; rewrite /= -/R.
have cfp : forall j, (j < d.+2)%N ->
      (\sum_(i < d.+2) ((a :: l)`_i * f i) *: 'X^(d.+1 - i))`_j =
      ((a :: l)`_(d.+1 - j) * f (d.+1 - j)%N).
  move=> j cj.
  have cut1 : (0 <= d.+1 - j)%N by rewrite leq0n.
  have cut2 : (d.+1 - j <= d.+2)%N.
    by rewrite (leq_trans _ (ltnW (ltnSn d.+1))) // leq_subr.
  rewrite -(big_mkord (fun i => true)
                (fun i => ((a :: l)`_i * f i) *: 'X^(d.+1 - i))).
  rewrite (big_cat_nat _ xpredT  _ cut1 cut2) /= coef_add_poly.
  have cut3 : (d.+1 - j <= (d.+1 - j).+1)%N by rewrite leqnSn.
  have cut4 : ((d.+1 - j) < d.+2)%N by rewrite ltnS leq_subr.
  rewrite (big_cat_nat _ xpredT _ cut3 cut4) /= coef_add_poly.
  rewrite big_nat1 coefZ subKn; last by rewrite -ltnS.
  rewrite coefXn eqxx mulr1 [X in X + (_ + _)](_ : _ = 0).
    rewrite add0r [X in _ + X](_ : _ = 0); first by rewrite addr0.
    rewrite nth_default //.
    apply: size_weighted_sum_leq=> i; rewrite mem_index_iota => /andP [ci c'].
    rewrite size_polyXn.
    move: ci; rewrite -(ltn_add2r j) subnK; last by rewrite -ltnS.
    move=> ci; rewrite -(ltn_add2r i) subnK; first by rewrite addnC.
    by rewrite -ltnS.
  have t : forall i, (0 <= i < d.+1 - j)%N ->
             ((a :: l)`_i * f i) *: 'X^(d.+1 - i) =
             ((a :: l)`_i * f i) *: 'X^(d - j - i) * 'X^j.+1.
    move=> i /andP [_ ci]; rewrite -scalerAl -exprD addnS subnAC subnK.
      by rewrite subSn // -ltnS (leq_trans ci).
    rewrite -(leq_add2r i) subnK; last first.
      by rewrite -ltnS (leq_trans ci).
    move: ci; rewrite -(ltn_add2r j) subnK.
      by rewrite ltnS addnC.
    by rewrite -ltnS.
  by rewrite (@eq_big_nat _ _ _ _ _ _ _ t) -big_distrl coefMXn leqnn.
exists (mkseq (fun i => 0) (d.+1 - size l)++(rev l2)), (x * f (size l1).+1),
  (mkseq (fun i => (rev l1)`_i * f ((size l1) - i)%N) (size l1)),
  (a * f 0%N), [::].
have am : all_eq0 (mkseq (fun  _ => (0:R)) (d.+1 - size l)).
  rewrite /all_eq0; apply/(all_nthP 0); rewrite size_mkseq=> i ci.
  by rewrite nth_mkseq.
have apos : 0 < a * f 0%N.
  by apply: mulr_gt0; first rewrite lt_neqAle ap eq_sym h //; apply: cf.
rewrite /all_eq0 /all_le0 all_cat -!all_rev -/(all_eq0 l2) p3 /=.
have al : all_le0 l by apply: first_neg_no_change_all_le0.
rewrite [all _ (mkseq _ _)]am apos /=.
have sl' : (size l1 + size l2 <= d)%N.
  by move: sl; rewrite p1 size_cat /= addnS ltnS.
have sl1d : (size l1 <= d)%N.
  by apply: leq_trans sl'; apply leq_addr.
have -> : x * f (size l1).+1 < 0.
  rewrite pmulr_llt0; last by apply: cf; rewrite !ltnS.
  rewrite lt_neqAle; rewrite p2 /=.
  by move/allP: al=> al; apply al; rewrite p1 mem_cat in_cons eqxx orbT.
split => //; last split=>//.
  have st : size (a * f 0%N *: 'X^d.+1) = d.+2.
  rewrite -mul_polyC size_Cmul ?size_polyXn // mulf_neq0 //.
    by rewrite neq_lt cf ?orbT.
  set sg := \sum_(_ < _) _; have st' : size sg = d.+2.
    rewrite /sg big_ord_recl /= subn0 size_addl; first by [].
    rewrite st ltnS size_weighted_sum_leq ?st //.
    by move=> [i C] _; rewrite /bump add1n subSS size_polyXn ltnS leq_subr.
  apply: (@eq_from_nth _ 0).
    move:sl; rewrite p1 !size_cat /= !size_cat /= !size_rev !addnS addn0=> T.
    by rewrite !size_mkseq subSS -addnA [(size l2 + _)%N]addnC subnK.
  move=> i; rewrite st' => ci; rewrite cfp // {st' sg st al apos am cfp}.
  rewrite nth_cat size_cat size_mkseq size_rev.
  case b1 : (i < d.+1 - size l + size l2)%N.
    rewrite nth_cat size_mkseq.
    case b2 : (i < d.+1 - size l)%N.
      rewrite nth_mkseq // nth_default ?mul0r //=.
      move: b2; rewrite -(ltn_add2r (size l)) subnK // => b2.
      by rewrite -(ltn_add2r i) subnK // addnC.
    have b2' : (d.+1 - size l <= i)%N by rewrite leqNgt b2.
    rewrite nth_rev; last first.
      by rewrite  -(ltn_add2r (d.+1 - size l)) subnK // addnC.
    case l2c : (l2) => [ | b l3] /=; first by move: b1; rewrite l2c addn0 b2.
    move: p3 {b2}; rewrite /all_eq0=>/all_nthP=> l20.
    rewrite -l2c (eqP (l20 0 _ _)); last first.
      by rewrite subSS l2c /= ltnS leq_subr.
    have b1' : (i < d - size l1)%N.
      move: b1; rewrite p1 size_cat /= addnS subSS subnDA subnK //.
      by rewrite -(leq_add2r (size l1)) subnK // addnC.
    have di1 : (i <= d)%N by rewrite (leq_trans (ltnW b1')) // leq_subr.
    rewrite subSn //= p1 nth_cat.
    have dil1 : (d - i < size l1)%N = false.
      apply: negbTE; rewrite -leqNgt -(leq_add2r i) subnK//.
      move: b1; rewrite -(ltn_add2l (size l1)) => b1.
      rewrite -ltnS (leq_trans b1) // p1 size_cat /= addnS subSS.
      by rewrite !(addnC (size l1)) -addnA subnK // addnC.
    rewrite dil1; move/negbT: dil1; rewrite -leqNgt=>dil1.
    rewrite -subnDA addnC subnDA -subnSK //= (eqP (l20 _ _ _)) ?mul0r //.
    rewrite -(ltn_add2r i.+1) subnK // addnS ltnS -leq_subLR.
    by rewrite (leq_trans _ b2') // p1 size_cat /= addnS subSS subnDA.
  move=>{p3 p2}.
  move/negbT: b1; rewrite -leqNgt leq_eqVlt; case/orP=>[/eqP b1 {ci} | b1].
    rewrite b1 subnn p1 /= -b1 p1 size_cat /= addnS subSS [(d - _)%N]subnDA.
    rewrite subnK; last first.
      by rewrite -(leq_add2r (size l1)) subnK // addnC.
    by rewrite subSn ?leq_subr // subKn //= nth_cat ltnn subnn /=.
  have sl2dml1: (size l2 <= d - size l1)%N.
    by rewrite -(leq_add2r (size l1)) subnK // addnC.
  have dml1i : (d - size l1 < i)%N.
    by apply: leq_trans b1; rewrite p1 size_cat /= addnS subSS subnDA subnK.
  rewrite -[(i - _)%N]subnSK //= nth_cat size_mkseq -subnDA.
  rewrite subnSK //.
  case b2 : (i - (d.+1 - size l + size l2) <= size l1)%N.
    rewrite nth_mkseq; last by rewrite subnSK.
  move: (b2); rewrite -(leq_add2r (d.+1 - size l + size l2)).
    rewrite subnK; last by rewrite ltnW.
    rewrite addnC p1 size_cat /= addnS subSS subnDA subnK // subnK // => b2'.
    rewrite nth_rev; last first.
      by rewrite -(ltn_add2r (d - size l1).+1) subnK // addnS addnC subnK.
    rewrite subnSK // subSn //= subnBA; last by rewrite ltnW.
    rewrite addnC subnK // subnBA // addnS addnC subnK // nth_cat.
    have dmil1 : (d - i < size l1)%N.
      rewrite -(ltn_add2r i) subnK //; move: dml1i.
      by rewrite -(ltn_add2r (size l1)) subnK // addnC.
    by rewrite dmil1 subSn.
  move/negbT: b2; rewrite -ltnNge=> b2.
  have difinal : i = d.+1.
    apply: anti_leq; apply/andP; split; first by rewrite -ltnS.
    move: b2; rewrite -(ltn_add2r (d.+1 - size l + size l2)).
    rewrite subnK; last by rewrite ltnW.
    by rewrite p1 size_cat /= addnS subSS subnDA subnK // addnC subnK.
  rewrite difinal subnn addSn subSS p1 size_cat /= addnS subnDA subSS.
  rewrite [(d - (size l1 + size l2))%N]subnDA subnK // subnBA //.
  by rewrite addKn subnn.
apply/(all_nthP 0); rewrite size_mkseq => i C; rewrite nth_mkseq // pmulr_lle0.
move: al; rewrite /all_le0 p1 all_cat => /andP [al1 _]; rewrite nth_rev //.
  by move/(all_nthP 0): al1 => -> //; rewrite subnSK // leq_subr.
apply: cf; rewrite ltnS (leq_trans _ (ltnW (ltnSn _))) ?(leq_trans _ sl1d) //.
by rewrite leq_subr.
Qed.

Lemma seqn0_oppr (l : seq R) :
  seqn0 (map (fun i => -i) l) = map (fun i => -i) (seqn0 l).
Proof.
elim: l => [// | a l IH] /=.
by rewrite oppr_eq0; case: (a != 0); rewrite /= IH //.
Qed.

Lemma changes_oppr (l : seq R) :
  changes [seq - x | x <- l] = changes l.
elim: l => [// | x [ | y l] IH] /=; first by rewrite !mulr0.
rewrite mulrNN; congr (_ + _)%N; exact: IH.
Qed.

Lemma ch1_correct l d a b (q : {poly R}):
  (size l <= d.+1)%N ->
  a < b -> q = \sum_(i < d.+1) l`_i *: bernp a b d i ->
    changes (seqn0 l) = 1%N -> unique_root_for (horner q) a b.
Proof.
wlog : l q / (0 <= (seqn0 l)`_0).
  move=> main s ab qq c1.
  case sg : (0 <= (seqn0 l)`_0).
  apply: (main l q sg) => //.
  have ur : unique_root_for (horner (-q)) a b.
    apply: (main (map (fun x => -x) l) (-q)) => //.
          rewrite seqn0_oppr (nth_map 0).
            by rewrite ler_oppr oppr0 ltW // ltNge sg.
          rewrite lt0n; apply/negP; move/eqP=>abs; move: sg.
          by rewrite nth_default ?abs ?lexx.
        by rewrite size_map.
      rewrite -(mul1r q) -mulNr qq big_distrr; apply/eq_bigr.
      move=> i _ /=; case ci : (i < size l)%N.
        by rewrite (nth_map 0) // mulNr mul1r scaleNr.
      move/negbT: ci; rewrite -leqNgt => ci.
      rewrite !nth_default //; last by rewrite size_map.
      by rewrite !scale0r mulr0.
    by rewrite seqn0_oppr changes_oppr.
  case: ur => [x [inx [xr xu]]].
  exists x; split; first by [].
  split; first by apply/eqP; rewrite -oppr_eq0 -hornerN; apply/eqP.
  by move=> u inu /eqP; rewrite -oppr_eq0 -hornerN => /eqP; apply:xu.
move=> sg s ab qq c1.
suff : one_root1 q a b by apply: one_root1_unique.
apply: (@Bernstein_isolate _ d) => //.
    rewrite lt0n size_poly_eq0; apply/negP => /eqP => abs.
    move/eqP: qq; rewrite abs eq_sym=> /eqP.
    move: (ab); rewrite lt_def eq_sym; case/andP => ab' _ sb.
    have := bernp_free ab' sb => bf {ab' sb abs sg}.
    have abs : (seqn0 l) = [::].
      move: l s bf {a b q ab c1}.
      elim: d => [ | d IH].
        move=> [ | a l]; first by [].
        case: l => /=; last by [].
        by move=> _ l0; have := (l0 ord0) => /= => ->; rewrite eqxx /=.
      move=> [ | a l] /=; first by [].
      rewrite ltnS=> s l0; have := (l0 ord0) => /= => ->; rewrite eqxx /=.
      apply: IH => //; move=> [i] /=; rewrite -ltnS => ci.
      by have := (l0 (Ordinal ci)).
    by move: c1; rewrite abs.
  rewrite qq; apply: size_weighted_sum_leq.
  move=> [i ci]; rewrite size_bernp ?leqnn //.
  by move: ab; rewrite lt_def eq_sym; case/andP.
have anb : a != b.
  by move: ab; rewrite lt_def eq_sym; case/andP.
rewrite qq Mobius_weighted_sum //; last by move=> [i ci]; rewrite size_bernp.
have t : forall i : 'I_d.+1, true -> l`_i *: Mobius d a b (bernp a b d i) =
                      (l`_i * ('C(d, i))%:R) *: 'X ^+ (d - i).
  by move=> [i ci]; rewrite Mobius_bernp //= scalerA.
rewrite (eq_bigr _ t) {t}.
have binp : forall i, (i < d.+1)%N -> (0:R) < ('C(d, i))%:R.
  by move => i ci; rewrite ltr0n bin_gt0 -ltnS.
apply: (changes1_alternate s binp) => //.
Qed.

Lemma ch0_correct l d a b q : a < b -> q != 0 ->
       q = \sum_(i < d.+1) l`_i *: bernp a b d i ->
       changes (seqn0 l) = 0%N -> no_root_for (horner q) a b.
move=> ab.
wlog : l q / 0 <= head 0 (seqn0 l).
move=> wlh qn0 qq ch.
  case pos : (0 <= head 0 (seqn0 l)); first by apply: (wlh l) => //.
  have ssn0 : (0 < size (seqn0 l))%N.
    rewrite lt0n; apply/negP=> s0.
    case/negP: qn0; rewrite qq big1 //.
    move=> i _; case sli: (size l <= i)%N.
      by rewrite nth_default ?scale0r.
    have : all_eq0 l by rewrite -all_eq0_seqn0 -nth0 nth_default // (eqP s0).
    move/negbT: sli; rewrite -ltnNge=> sli /allP l0.
    by have := mem_nth 0 sli => /l0/eqP=> li0; rewrite li0 scale0r.
  move: ch; rewrite -changes_oppr -seqn0_oppr => ch.
  move/negbT: pos; rewrite -ltNge -oppr_gt0 -nth0 -(nth_map 0 0) // nth0.
  rewrite -seqn0_oppr=>pos.
  have ssn0' : (0 < size (seqn0 [seq -x | x <- l]))%N.
    by rewrite seqn0_oppr size_map.
  move: qn0; rewrite -oppr_eq0 => qn0.
  have := refl_equal (-q); rewrite [X in _ = - X]qq -[X in _ = -X]mul1r {qq}.
  rewrite -mulNr big_distrr /=.
  have t : forall i : 'I_d.+1, true ->
     -1 * (l`_i *: bernp a b d i) =
     [seq -x | x <- l]`_i *: bernp a b d i.
    move=> i _; case ci : (i < size l)%N.
      rewrite (nth_map 0) // -[-1]/(-(1%:P)) -polyCN mul_polyC scalerA.
      by rewrite mulNr mul1r.
    move/negbT: ci; rewrite -leqNgt=> ci.
    rewrite !nth_default //; first by rewrite !scale0r mulr0.
    by rewrite size_map.
  rewrite (eq_bigr _ t) => qq {t ssn0}.
  have {wlh qq ch qn0 pos ssn0'} := wlh _ _ (ltW pos) qn0 qq ch.
  by move=> nx x inx; rewrite -[q.[x]]opprK -hornerN oppr_eq0 nx.
move=> h qn0 qq ch x inx; apply /negP; rewrite qq.
rewrite horner_sum psumr_eq0 /=.
move=> al0; case/negP: qn0; rewrite qq.
  rewrite big1 //; move => i _; rewrite [l`_i](_ : _ = 0) ?scale0r //.
  have : l`_i * (bernp a b d i).[x] == 0.
    by have := (allP al0 i (mem_index_enum _)); rewrite hornerZ.
  rewrite mulf_eq0.
  case: i => i /=; rewrite ltnS => ci.
  have := bernp_gt0 ci inx; set bf := (_.[_]) => b0.
  have bn0 : (bf != 0) by rewrite neq_lt b0 orbT.
  by rewrite (negbTE bn0) orbF => /eqP.
move=> i _; rewrite hornerZ.
apply: mulr_ge0; last first.
  by apply/ltW/bernp_gt0=> //; case i.
case sli: (i < size l)%N; last first.
  by move/negbT: sli; rewrite -leqNgt=> sli; rewrite nth_default //.
by move/allP: (first_pos_no_change_all_ge0 h ch)=> t; apply/t/mem_nth.
Qed.

Lemma bern0_a : forall (a b : R) deg i, a != b -> (0 < deg)%N ->
   (i <= deg)%N -> (bernp a b deg i).[a] == 0 = (i != 0)%N.
Proof.
move=> a b deg i anb dn0 id.
rewrite /bernp hornerMn !hornerE !horner_exp !hornerE subrr.
rewrite mulrn_eq0 !mulf_eq0 !expf_eq0 eqxx andbT invr_eq0 expf_eq0 dn0 andTb.
rewrite subr_eq0 [b == a]eq_sym (negbTE anb) orFb lt0n andbF orbF.
by rewrite eqn0Ngt bin_gt0 id.
Qed.

Lemma bernp_first_coeff0 l d (a b : R) q :
  a != b -> (0 < d)%N  ->
  q = \sum_(i < d.+1) l`_i *: bernp a b d i ->
  (l`_0 == 0) = (q.[a] == 0).
Proof.
move=> anb dn0 qq.
rewrite qq horner_sum big_ord_recl !hornerE.
rewrite (_ : \sum_(i < d) _ = 0).
  by rewrite addr0 mulf_eq0 bern0_a // eqxx orbF.
apply: big1; move=> [i ci] _ /=; apply/eqP.
by rewrite hornerE mulf_eq0 bern0_a // [bump _ _ == _]eq_sym neq_bump orbT.
Qed.

Lemma isol_rec_head_root : forall c l d a b q acc,
  q.[a] != 0 -> head_root (horner q) (isol_rec c d a b l acc).
Proof.
elim=> [// | c IH l d a b q acc qa0 /=].
by case tst : (changes (seqn0 l)) => [ | [ | cl]] //=; apply: IH.
Qed.

Lemma isol_rec_correct : forall c l d a b q acc,
  a < b -> (0 < d)%N -> q != 0 -> (size l <= d.+1)%N ->
  q = \sum_(i < d.+1) l`_i *: bernp a b d i ->
  read (horner q) acc -> head_root (horner q) acc ->
  read (horner q) (isol_rec c d a b l acc).
Proof.
elim=> [// | c IH].
move=> l d a b q acc altb dn0 qn0 sld qq ht hh /=.
have anb : a != b by rewrite neq_lt altb.
case tst : (changes (seqn0 l)) => [/= | [/= | nc]].
    by split=> //; apply (ch0_correct altb qn0 qq).
  by split=> //; apply (ch1_correct sld altb qq).
have help : 2%:R^-1 = ((a + b) / 2%:R - a)/(b - a).
  rewrite -[X in _ / _ - X]double_half -/(half (a + b)) half_lin half_lin1.
  rewrite opprD addrCA !addrA addNr add0r /half mulrAC mulfV ?mul1r //.
  by rewrite subr_eq0 eq_sym.
have help2 : 2%:R^-1 = (b - (a + b)/2%:R)/(b - a).
  rewrite -[X in X - _ / _]double_half -/(half(a + b)) half_lin half_lin1.
  rewrite opprD addrCA addrK [- _ + _]addrC /half mulrAC mulfV ?mul1r //.
  by rewrite subr_eq0 eq_sym.
have qh' :
  q = \sum_(i < d.+1)
         (mkseq (dicho' 2%:R^-1 2%:R^-1 [eta nth 0 l]) d.+1)`_i *:
         bernp a ((a + b) / 2%:R) d i.
  have qt : forall i : 'I_d.+1, true ->
                  (mkseq (dicho' 2%:R^-1 2%:R^-1 [eta nth 0 l]) d.+1)`_i *:
                       bernp a ((a + b) / 2%:R) d i =
                  dicho' ((b - half (a + b))/(b - a))
                         ((half (a + b) - a)/(b - a)) [eta nth 0 l] i *:
                  bernp a ((a + b) / 2%:R) d i.
    by move => [i ci] _; rewrite -help -help2 /= nth_mkseq.
  rewrite (eq_bigr _ qt); apply: dicho'_correct => //.
  rewrite -[X in _ == X]double_half half_lin; apply/negP.
  by move/eqP/half_inj/addrI/eqP; rewrite eq_sym; apply/negP.
have qh :
  q = \sum_(i < d.+1)
         (mkseq (dicho 2%:R^-1 2%:R^-1 d [eta nth 0 l]) d.+1)`_i *:
         bernp ((a + b) / 2%:R) b d i.
  have qt : forall i : 'I_d.+1, true ->
                (mkseq (dicho 2%:R^-1 2%:R^-1 d [eta nth 0 l]) d.+1)`_i *:
                     bernp ((a + b) / 2%:R) b d i =
                dicho ((b - half (a + b))/(b - a))
                      ((half (a + b) - a)/(b - a)) d [eta nth 0 l] i *:
                  bernp ((a + b) / 2%:R) b d i.
    by move => [i ci] _; rewrite -help -help2 /= nth_mkseq.
  rewrite (eq_bigr _ qt); apply: dicho_correct => //.
  rewrite -[X in _ == X]double_half half_lin; apply/negP.
  by move/eqP/half_inj/addIr/eqP; apply/negP.
apply: (IH) => //.
      by case/andP : (mid_between altb) => it _; exact it.
    by rewrite size_mkseq.
  case ts0: (dicho 2%:R^-1 2%:R^-1 d [eta nth 0 l] 0 == 0).
    rewrite /=; split.
      apply/eqP; rewrite -(bernp_first_coeff0 _ dn0 qh).
        by rewrite nth_mkseq.
      rewrite -[X in _ == X]double_half half_lin; apply/negP.
      by move/eqP/half_inj/addIr/eqP; apply/negP.
    apply: IH => //.
      by case/andP : (mid_between altb) => _ it; exact it.
    by rewrite size_mkseq.
  apply: IH => //.
    by case/andP : (mid_between altb) => _ it; exact it.
  by rewrite size_mkseq.
case ts0: (dicho 2%:R^-1 2%:R^-1 d [eta nth 0 l] 0 == 0); first by [].
apply: isol_rec_head_root.
rewrite -(bernp_first_coeff0 _ dn0 qh); last first.
  rewrite -[X in _ == X]double_half half_lin; apply/negP.
  by move/eqP/half_inj/addIr/eqP; apply/negP.
by rewrite nth_mkseq; move/negbT: ts0.
Qed.

End isolation_algorithm.
