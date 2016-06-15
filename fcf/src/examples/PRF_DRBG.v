
     fcf_spec_ret.
  
   Qed.


   (* The previous recursive function is equivalent to mapping the computation that produces random values over a list of the appropriate length.  The form thet uses compMap can be unified with some existing theory to compute the probability of the event. *)
   Definition PRF_DRBG_G3_bad_3 :=
     ls <-$ compMap _ (fun _ => {0, 1}^eta) (forNats (pred l));
     ret (hasDups _ (v_init :: (map injD ls))).

   Theorem PRF_DRBG_f_bad_2_compMap_equiv :
     forall n, 
     comp_spec eq
     (PRF_DRBG_f_bad_2 n)
     (compMap (Bvector_EqDec eta) (fun _ : nat => { 0 , 1 }^eta)
        (forNats n)).

     induction n; intuition; simpl in *.
     fcf_reflexivity.
     fcf_skip.
     fcf_skip.
     apply IHn.
     subst.
     fcf_reflexivity.

   Qed.

   Theorem PRF_DRBG_G3_bad_2_3_equiv : 
     Pr[PRF_DRBG_G3_bad_2] == Pr[PRF_DRBG_G3_bad_3].

     unfold PRF_DRBG_G3_bad_2, PRF_DRBG_G3_bad_3.
     fcf_to_prhl_eq.
     pose proof PRF_DRBG_f_bad_2_compMap_equiv.
     fcf_skip.

   Qed.
   
   (* Don't apply the injection to the random values and initial input. *)
   Definition PRF_DRBG_G3_bad_4 :=
     ls <-$ compMap _ (fun _ => {0, 1}^eta) (forNats (pred l));
     ret (hasDups _ (r_init :: ls)).

    Theorem PRF_DRBG_G3_bad_3_4_equiv : 
     Pr[PRF_DRBG_G3_bad_3] == Pr[PRF_DRBG_G3_bad_4].

     unfold PRF_DRBG_G3_bad_3, PRF_DRBG_G3_bad_4.
     fcf_to_prhl_eq.
     fcf_skip.
     fcf_spec_ret.
     unfold v_init.

     symmetry.
     erewrite (hasDups_inj_equiv _ _ (r_init :: b)).
     simpl. eauto.
     trivial.
   Qed.

   (* HasDups.v has a theorem that computes the probability of duplicates in a list of random values.  We need a form of the dupProb theorem that allows the first item in the list to be fixed.  *)
   Theorem dupProb_const : 
    forall (X : Set)(ls : list X)(v : Bvector eta),
      Pr[x <-$ compMap _ (fun _ => {0, 1}^eta) ls; ret (hasDups _ (v :: x))] <= 
      ((S (length ls)) ^ 2 / 2 ^ eta).

     intuition.
     (* Either the list of random values has duplicates, or v is in this list.  The probability value that we want is (at most) the sum of the probabilities of these two events.  The evalDist_orb_le theorem allows us to reason about them separately.  Put the game in a form that unifies with this theorem. *)

     fcf_rewrite_l (Pr[x <-$ compMap (Bvector_EqDec eta) (fun _ : X => { 0 , 1 }^eta) ls;
                      ret ((if (in_dec (EqDec_dec _) v x) then true else false) || (hasDups (Bvector_EqDec eta) x)) ] 
                 ).
     fcf_skip.
     simpl.
     destruct ( in_dec (EqDec_dec (Bvector_EqDec eta)) v x).
     simpl.
     intuition.
     rewrite orb_false_l.
     intuition.

     rewrite evalDist_orb_le.

     (* Use a theorem from the library to determine the probability that v is present in the random list. *)
     rewrite FixedInRndList_prob.
     (* Now determine the probability that there are duplicates in the random list. *)
     rewrite dupProb.
     
     (* The rest is just arithmetic. *)
     simpl.
     rewrite mult_1_r.
     cutrewrite ( S (length ls + length ls * S (length ls)) =  (S (length ls) + length ls * S (length ls)))%nat.
     rewrite ratAdd_num.
     eapply ratAdd_leRat_compat.
     eapply leRat_terms;
     omega.
     eapply leRat_terms.
     eapply mult_le_compat; omega.
     trivial.
     omega.
   Qed.

   Theorem PRF_DRBG_G3_bad_4_small :
      Pr[PRF_DRBG_G3_bad_4] <= (l ^ 2 / 2 ^ eta).

     unfold PRF_DRBG_G3_bad_4.
     rewrite dupProb_const.
     destruct l.
     omega.
     
     simpl.
     rewrite forNats_length.
     rewrite mult_1_r.
     reflexivity.
 
   Qed.

   (* Combine all of the results related to the G3 games to show that G3 and G4 are close. *)
   Theorem PRF_DRBG_G3_G4_close : 
     | Pr[ PRF_DRBG_G3 ] - Pr[  PRF_DRBG_G4 ] | <= (l^2 / 2^eta).

     rewrite PRF_DRBG_G3_1_eq.
     rewrite PRF_DRBG_G3_1_2_eq.
     rewrite <- PRF_DRBG_G3_3_G4_eq.
     rewrite  PRF_DRBG_G3_2_3_close.
     rewrite PRF_DRBG_G3_bad_equiv.
     rewrite PRF_DRBG_G3_bad_1_2_equiv.
     rewrite PRF_DRBG_G3_bad_2_3_equiv.
     rewrite PRF_DRBG_G3_bad_3_4_equiv.
     apply PRF_DRBG_G3_bad_4_small.

   Qed.

   (* Finally, show that G4 is equivalent to the second game in the DRBG security definition. *)
   Theorem PRF_DRBG_f_G2_compMap_spec :
     forall n v, 
     comp_spec (fun x1 x2 => fst x1 = x2)
     ((PRF_DRBG_f_G2 v n) unit unit_EqDec
        (fun (_ : unit) (_ : D) => x <-$ { 0 , 1 }^eta; ret (x, tt)) tt)
     (compMap (Bvector_EqDec eta) (fun _ : nat => { 0 , 1 }^eta) (forNats n)).

     induction n; intuition; simpl in *.
     fcf_simp.
     fcf_spec_ret.
     
     fcf_inline_first.
     fcf_skip.
     fcf_skip.
     fcf_spec_ret.
   Qed.
       
  Theorem PRF_DRBG_G4_DRBG_equiv : 
    Pr[PRF_DRBG_G4] == Pr[DRBG_G1 RndOut A].

    unfold PRF_DRBG_G4, DRBG_G1, RndOut, PRF_A.
    simpl.
    fcf_inline_first.
    fcf_to_prhl_eq.
    fcf_with PRF_DRBG_f_G2_compMap_spec fcf_skip.
   
    simpl.
    fcf_inline_first.
    fcf_ident_expand_r.
    fcf_skip.

  Qed.


  (* The final security result showing that the advantage of the adversary against the DRBG is at most the advantage of the constructed adversary against the PRF, and some negligible value. *)

  Theorem PRF_DRBG_Adv_small : 
    DRBG_Advantage RndKey RndOut PRF_DRBG A <=  
    PRF_Advantage RndKey ({ 0 , 1 }^eta) f D_EqDec (Bvector_EqDec eta) PRF_A
    + l ^ 2 / 2 ^ eta.

    intuition.
    unfold DRBG_Advantage.
    rewrite PRF_DRBG_G1_equiv.
    rewrite PRF_DRBG_G1_G2_equiv.
    rewrite <- PRF_DRBG_G4_DRBG_equiv.
    eapply ratDistance_le_trans.
    apply PRF_DRBG_G2_G3_close.
    apply PRF_DRBG_G3_G4_close.

  Qed.

  Print Assumptions PRF_DRBG_Adv_small.

End PRF_DRBG.
