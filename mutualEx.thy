theory mutualEx imports cacheBeta
begin
section{*Main defintions*}
(***************definitions for the enumvalues types****************************************)
definition true::"nat"  where [simp]: "true\<equiv>  8"   
definition false::"nat"  where [simp]: "false\<equiv>  9"   
definition Bool::"nat set" where [simp]: "Bool \<equiv> {true,false}"
definition I::"nat"  where [simp]: "I\<equiv>  4"   
definition T::"nat"  where [simp]: "T\<equiv>  5"   
definition C::"nat"  where [simp]: "C\<equiv>  6"   
definition E::"nat"  where [simp]: "E\<equiv>  7"   
definition nStateType::"nat set" where [simp]: "nStateType \<equiv> {I,T,C,E}"
(*definition Int::"nat set" where [simp]: "Int \<equiv> {,,}"*)
(***************definitions for the axioms ****************************************)
axiomatization where axiomOn_n  [simp]:"   s (IVar (Para ''n'' i )) \<in> nStateType "
axiomatization where axiomOn_x  [simp]:"   s (IVar (Global ''x'' )) \<in> Bool "
definition rule_crit::" nat \<Rightarrow> rule" where [simp]:
" rule_crit  iInv1 \<equiv>   
let g=( andForm ( eqn ( IVar ( Para ''n'' iInv1) )  ( Const T ))    ( eqn ( IVar ( Global ''x'') )  ( Const true ))  )  in 
let S=(
(let S_1=  (( Para ''n'' iInv1),  ( Const C ) ) in
let S_2=(assign   (( Global ''x''),  ( Const false ) ) ) in
( parallel S_1 S_2) )) in 
guard g S"
definition rule_exit::" nat \<Rightarrow> rule" where [simp]:
" rule_exit  iInv1 \<equiv>   
let g=( eqn ( IVar ( Para ''n'' iInv1) )  ( Const C ))  in 
let S=(
 assign   (( Para ''n'' iInv1),  ( Const E ) )) in 
guard g S"
definition rule_idle::" nat \<Rightarrow> rule" where [simp]:
" rule_idle  iInv1 \<equiv>   
let g=( eqn ( IVar ( Para ''n'' iInv1) )  ( Const E ))  in 
let S=(
(let S_1=  (( Global ''x''),  ( Const true ) ) in
let S_2=(assign   (( Para ''n'' iInv1),  ( Const I ) ) ) in
( parallel S_1 S_2) )) in 
guard g S"
definition rule_try::" nat \<Rightarrow> rule" where [simp]:
" rule_try  iInv1 \<equiv>   
let g=( eqn ( IVar ( Para ''n'' iInv1) )  ( Const I ))  in 
let S=(
 assign   (( Para ''n'' iInv1),  ( Const T ) )) in 
guard g S"
definition rules::"nat \<Rightarrow> rule set"  where [simp] :
"rules N\<equiv> {r. exLessP N (%i.  r=rule_crit i)  \<or>
exLessP N (%i.  r=rule_exit i)  \<or>
exLessP N (%i.  r=rule_idle i)  \<or>
exLessP N (%i.  r=rule_try i)  }"
definition inv1::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:
       "inv1 iInv1 iInv2 \<equiv> 
   
       let ant= ( eqn ( IVar ( Para ''n'' iInv1) )  ( Const E ))   in
   
       let cons=  (neg ( eqn ( IVar ( Para ''n'' iInv2) )  ( Const E )) )   in 
   
       (implyForm ant cons)  "
 definition inv2::"nat \<Rightarrow> formula "  where [simp]:
       "inv2 iInv1 \<equiv> 
   
       let ant= ( eqn ( IVar ( Global ''x'') )  ( Const true ))   in
   
       let cons=  (neg ( eqn ( IVar ( Para ''n'' iInv1) )  ( Const E )) )   in 
   
       (implyForm ant cons)  " 
definition inv3::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:
       "inv3 iInv1 iInv2 \<equiv> 
   
       let ant= ( eqn ( IVar ( Para ''n'' iInv1) )  ( Const E ))   in
   
       let cons=  (neg ( eqn ( IVar ( Para ''n'' iInv2) )  ( Const C )) )   in 
   
       (implyForm ant cons)  "
 definition inv4::"nat \<Rightarrow> formula "  where [simp]:
       "inv4 iInv1 \<equiv> 
   
       let ant= ( eqn ( IVar ( Global ''x'') )  ( Const true ))   in
   
       let cons=  (neg ( eqn ( IVar ( Para ''n'' iInv1) )  ( Const C )) )   in 
   
       (implyForm ant cons)  " 
definition inv5::"nat \<Rightarrow> nat \<Rightarrow>formula "  where [simp]:
       "inv5 iInv1 iInv2 \<equiv> 
   
       let ant= ( eqn ( IVar ( Para ''n'' iInv1) )  ( Const C ))   in
   
       let cons=  (neg ( eqn ( IVar ( Para ''n'' iInv2) )  ( Const C )) )   in 
   
       (implyForm ant cons)  "
 definition invariants::"nat \<Rightarrow> formula set"  where [simp] :
"invariants N\<equiv> {f. exTwoLessP N (% i j.  f = inv1 i j)  \<or>
exLessP N (% i.  f= inv2 i)  \<or>
exTwoLessP N (% i j.  f = inv3 i j)  \<or>
exLessP N (% i.  f= inv4 i)  \<or>
exTwoLessP N (% i j.  f = inv5 i j)   }"
 definition iniStateSpecOfn::" nat \<Rightarrow> formula" where [simp] :
  " iniStateSpecOfn  i\<equiv>  eqn (IVar (Para ''n'' i)) ( Const I )"
 definition iniStateSpecOfx::"  formula" where [simp] :
  " iniStateSpecOfx \<equiv>  eqn (IVar (Global ''x'')) ( Const true )"
definition mutualIni ::"nat\<Rightarrow>formula" where [simp]:
   "mutualIni  N \<equiv>( andForm(iniStateSpecOfx ) 
 ( forallForm (down N) (%x. iniStateSpecOfn x))
)"
lemma lemmaOnIni_iniStateSpecOfn:
  assumes   a2:" ini \<in> { mutualIni  N}"
  and a3:"formEval ini s" and a4:"i \<le> N"
  shows " formEval (iniStateSpecOfn i) s"
  apply(rule_tac i="i" and N="N" in forallLemma)
  apply(cut_tac a4,simp)
  apply(cut_tac a2 a3,simp)
  done
lemma lemmaOnIni_iniStateSpecOfx:
  assumes   a2:" ini \<in> { mutualIni  N}"
  and a3:"formEval ini s"  
  shows " formEval (iniStateSpecOfx ) s"
 
  apply(unfold iniStateSpecOfx_def)
  apply(cut_tac a2 a3,simp)
  done
  
  
locale iniImplyOneInvInExLessPByDisableAnt=
  fixes paraInv ::"nat \<Rightarrow> formula"  and iniStateSpecOfAVar::" nat \<Rightarrow> formula"
  assumes  a:"\<forall> i s. formEval (antOf (paraInv i)) s \<longrightarrow> \<not>  formEval (iniStateSpecOfAVar  i) s "  and
  b:"\<forall> N ini i s. i\<le>N \<longrightarrow>ini \<in> { mutualIni  N}\<longrightarrow>formEval ini s \<longrightarrow>  formEval (iniStateSpecOfAVar  i) s" and
  c:"\<exists>  ant0 cons0. (paraInv i)= implyForm ant0 cons0"
begin
theorem iniImplyInv:
  assumes a1: " exLessP N (%i.  invariant = paraInv i)" 
 
  and a2:" ini \<in> { mutualIni  N}"
  and a3:"formEval ini s"
  shows "formEval invariant s"
proof -
  from a1 obtain i where b1:"i \<le> N \<and> invariant =paraInv  i" 
    apply -
    apply(simp add:exLessP_def)
    apply auto
    done
  have b2:"formEval (iniStateSpecOfAVar  i) s"
    
    apply(cut_tac b b1 a2 a3)
    by blast
  have b3:"\<exists>  ant0 cons0. (paraInv i)= implyForm ant0 cons0"
    by(cut_tac c,auto)
  then obtain ant0 cons0  where b4:"paraInv  i=implyForm ant0 cons0"
    by blast
     
  show  "formEval invariant s"   
    apply(cut_tac a)
    apply(cut_tac b1 b2 b4,simp)
    apply auto
    done
qed
end
locale iniImplyOneInvInExTwoLessPByDisableAnt=
  fixes paraInv ::" nat \<Rightarrow>nat \<Rightarrow> formula"  and iniStateSpecOfAVar::" nat \<Rightarrow> formula"
  assumes  a:"\<forall> i j s. formEval (antOf (paraInv i j)) s \<longrightarrow> \<not>  formEval (iniStateSpecOfAVar  i) s "  and
  b:"\<forall> N ini i s. i\<le>N \<longrightarrow>ini \<in> { mutualIni  N}\<longrightarrow>formEval ini s \<longrightarrow>  formEval (iniStateSpecOfAVar  i) s" and
  c:"\<exists>  ant0 cons0. (paraInv i j)= implyForm ant0 cons0"
begin
theorem iniImplyInv:
  assumes a1: " exTwoLessP N (%i j.  invariant = paraInv i j)"  
  and a2:" ini \<in> { mutualIni  N}"
  and a3:"formEval ini s"
  shows "formEval invariant s "
proof -
  from a1 obtain i j where b1:"i \<le> N \<and> j\<le>N \<and> invariant =paraInv  i j"
 
    apply -
    apply(simp add:exTwoLessP_def)
    apply auto
    done
  have b2:"formEval (iniStateSpecOfAVar  i) s"    
    apply(cut_tac b b1 a2 a3)
    by blast
  have b3:"\<exists>  ant0 cons0. (paraInv i j)= implyForm ant0 cons0"
    by(cut_tac c,auto)
  then obtain ant0 cons0  where b4:"paraInv  i j=implyForm ant0 cons0"
    by blast
     
  show  "formEval invariant s "   
    
    apply(cut_tac a)
    apply(cut_tac b1 b2 b4,simp)
    by (metis (lifting) antOf.simps)
qed
end   
locale iniImplyOneInvInExLessPByEnableCons=
  fixes paraInv ::"nat \<Rightarrow> formula"  and iniStateSpecOfAVar::" nat \<Rightarrow> formula"
  assumes  a:"\<forall> i s. formEval (iniStateSpecOfAVar  i) s 
    \<longrightarrow>formEval (consOf (paraInv i)) s "  and
  b:"\<forall> N ini i s. i\<le>N \<longrightarrow>ini \<in> { mutualIni  N}\<longrightarrow>formEval ini s 
  \<longrightarrow>  formEval (iniStateSpecOfAVar  i) s" and
  c:"\<exists>  ant0 cons0. (paraInv i)= implyForm ant0 cons0"
begin
theorem iniImplyInv:
  assumes a1: " exLessP N (%i.  invariant = paraInv i)"  
  and a2:" ini \<in> { mutualIni  N}"
  and a3:"formEval ini s"
  shows "formEval invariant s "
proof -
  from a1 obtain i where b1:"i \<le> N \<and> invariant =paraInv  i" 
    apply -
    apply(simp add:exLessP_def)
    apply auto
    done
  have b2:"formEval (iniStateSpecOfAVar  i) s"    
    apply(cut_tac b b1 a2 a3)
    by blast
  have b3:"\<exists>  ant0 cons0. (paraInv i)= implyForm ant0 cons0"
    by(cut_tac c,auto)
  then obtain ant0 cons0  where b4:"paraInv  i=implyForm ant0 cons0"
    by blast
     
  then have b5:"formEval cons0  s"
    apply -   
    apply(cut_tac a b2)     
    apply(drule_tac x="i" in spec)
    apply(drule_tac x="s" in spec)
    by auto
  show  "formEval invariant s "   
    apply(cut_tac a)
    apply(cut_tac b1 b2 b4 b5,simp)
    done
qed
end
locale iniImplyOneInvInExTwoLessPByEnableCons= 
  fixes paraInv ::" nat \<Rightarrow>nat \<Rightarrow> formula"  and iniStateSpecOfAVar::" nat \<Rightarrow> formula" 
  assumes  a:" \<forall> i j s.   formEval (iniStateSpecOfAVar  j) s  \<longrightarrow> 
  formEval (consOf (paraInv i j)) s "  and 
  b:"\<forall> N ini i s. i\<le>N \<longrightarrow>ini \<in> { mutualIni  N}\<longrightarrow>formEval ini s \<longrightarrow>  formEval (iniStateSpecOfAVar  i) s" and 
  c:"\<exists>  ant0 cons0. (paraInv i j)= implyForm ant0 cons0" 
begin 
theorem iniImplyInv: 
  assumes a1: " exTwoLessP N (%i j.  invariant = paraInv i j)"   
  and a2:" ini \<in> { mutualIni  N}" 
  and a3:"formEval ini s" 
  shows "formEval invariant s " 
proof - 
  from a1 obtain i j where b1:"i \<le> N \<and> j\<le>N \<and> invariant =paraInv  i j"  
    apply - 
    apply(simp add:exTwoLessP_def) 
    apply auto 
    done 
 
  have b2:"formEval (iniStateSpecOfAVar  j) s"     
    apply(cut_tac b b1 a2 a3) 
    by blast 
 
  have b3:"\<exists>  ant0 cons0. (paraInv i j)= implyForm ant0 cons0" 
    by(cut_tac c,auto) 
 
  then obtain ant0 cons0  where b4:"paraInv  i j=implyForm ant0 cons0" 
    by blast 
 
  then have b5:"formEval cons0  s" 
 
    apply -    
    apply(cut_tac a b2)      
    apply(drule_tac x="i" in spec) 
    apply(drule_tac x="j" in spec) 
    apply(drule_tac x="s" in spec) 
    by auto 
     
  show  "formEval invariant s "    
    
    apply(cut_tac a) 
    apply(cut_tac b1 b2 b4 b5,simp) 
    done 
qed 
end 
  interpretation iniImply_Inv1:iniImplyOneInvInExTwoLessPByEnableCons "inv1::nat\<Rightarrow>nat\<Rightarrow>formula"  "iniStateSpecOfn::nat \<Rightarrow> formula"
   proof(unfold iniImplyOneInvInExTwoLessPByEnableCons_def inv1_def,
      rule conjI, force,rule conjI, 
     blast intro:lemmaOnIni_iniStateSpecOfn,
      force)
    qed
  interpretation iniImply_Inv2:iniImplyOneInvInExLessPByEnableCons "inv2::nat\<Rightarrow>formula"  "iniStateSpecOfn::nat \<Rightarrow> formula"
   proof(unfold iniImplyOneInvInExLessPByEnableCons_def inv2_def,
      rule conjI, force,rule conjI, 
     blast intro:lemmaOnIni_iniStateSpecOfn,
      force)
    qed
  interpretation iniImply_Inv3:iniImplyOneInvInExTwoLessPByEnableCons "inv3::nat\<Rightarrow>nat\<Rightarrow>formula"  "iniStateSpecOfn::nat \<Rightarrow> formula"
   proof(unfold iniImplyOneInvInExTwoLessPByEnableCons_def inv3_def,
      rule conjI, force,rule conjI, 
     blast intro:lemmaOnIni_iniStateSpecOfn,
      force)
    qed
  interpretation iniImply_Inv4:iniImplyOneInvInExLessPByEnableCons "inv4::nat\<Rightarrow>formula"  "iniStateSpecOfn::nat \<Rightarrow> formula"
   proof(unfold iniImplyOneInvInExLessPByEnableCons_def inv4_def,
      rule conjI, force,rule conjI, 
     blast intro:lemmaOnIni_iniStateSpecOfn,
      force)
    qed
  interpretation iniImply_Inv5:iniImplyOneInvInExTwoLessPByEnableCons "inv5::nat\<Rightarrow>nat\<Rightarrow>formula"  "iniStateSpecOfn::nat \<Rightarrow> formula"
   proof(unfold iniImplyOneInvInExTwoLessPByEnableCons_def inv5_def,
      rule conjI, force,rule conjI, 
     blast intro:lemmaOnIni_iniStateSpecOfn,
      force)
    qed
locale paraRuleInstValidateExLessInvInst=
  fixes paraRule ::"nat \<Rightarrow> rule"  and paraInv::"nat \<Rightarrow> formula "  
  and iRule::"nat" and iInv1::"nat"  and N::"nat"
  assumes a:" \<exists>  ant0 cons0. paraInv iInv1= implyForm ant0 cons0" and 
  b:"iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow> iRule = iInv1 \<longrightarrow> 
  (invHoldForRule (paraInv iInv1) (paraRule iRule)  (invariants N) )"  and 
  c:"iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>  iRule \<noteq> iInv1 \<longrightarrow> 
  (invHoldForRule (paraInv iInv1) (paraRule iRule)  (invariants N)  )" 
begin
theorem paraRuleInstValidateExLessInvInst:
  assumes a1:"iRule \<le> N"  and a2:" iInv1 \<le> N "
  shows "(invHoldForRule (paraInv iInv1) (paraRule iRule)  (invariants N)  )"
    (is "?P paraInv iInv1 paraRule iRule  (invariants N)")
  proof -
   have e2:"iRule=iInv1  \<or> iRule \<noteq> iInv1 "  by auto
     
     
   moreover
   {assume e3:" iRule=iInv1 "
            
     have "?P paraInv iInv1 paraRule iRule  (invariants N)"
       by (metis a1 a2 b e3)
   }     
   moreover
   {assume e3:"iRule\<noteq>iInv1 "
     have "?P paraInv iInv1 paraRule iRule  (invariants N) "
       by (metis a1 a2 c e3)
   }
   ultimately show "?P paraInv iInv1 paraRule iRule  (invariants N) "
     by blast
 qed
end
  
locale paraRuleInstValidateExTwoLessInvInst=
  fixes paraRule ::"nat \<Rightarrow> rule"  and paraInv::"nat \<Rightarrow> nat\<Rightarrow>formula "  
  and iRule::"nat" and iInv1::"nat" and iInv2::"nat" and N::"nat"
  assumes a:" \<exists>  ant0 cons0. paraInv iInv1 iInv2= implyForm ant0 cons0" and 
  b:"iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>iInv2 \<le> N\<longrightarrow>iRule = iInv1 \<longrightarrow> 
  invHoldForRule (paraInv iInv1 iInv2) (paraRule iRule)  (invariants N) "  and 
  c:"iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>iInv2 \<le> N\<longrightarrow>iRule = iInv2 \<longrightarrow> 
  invHoldForRule (paraInv iInv1 iInv2) (paraRule iRule) (invariants N)"  and
  d:"iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>iInv2 \<le> N\<longrightarrow>iRule \<noteq> iInv1 \<longrightarrow>iRule \<noteq> iInv2 \<longrightarrow> 
  invHoldForRule (paraInv iInv1 iInv2) (paraRule iRule)  (invariants N)"
begin
theorem paraRuleInstValidateExTwoLessInvInst:
  assumes a1:"iRule \<le> N"  and a2:" iInv1 \<le> N " and a3:"iInv2 \<le> N "
  and a4:"iInv1 \<noteq> iInv2"
  shows "invHoldForRule (paraInv iInv1 iInv2) (paraRule iRule)   (invariants N) "  (is "?P paraInv iInv paraRule iRule  invs")
  proof -
   have d2:"iRule=iInv1 \<or> iRule=iInv2 \<or> ((iRule \<noteq> iInv1) \<and> (iRule\<noteq>iInv2))"  by auto
   moreover
   {assume e1:"iRule=iInv1"
     have "?P paraInv iInv paraRule iRule  invs "
       by (metis  a2 a3 a4 b e1)
              
           
   }     
   moreover
   {assume e1:"iRule = iInv2"            
     have "?P paraInv iInv paraRule iRule  invs"
       by (metis  a2 a3 a4 c e1)
   }
   
       
   moreover
   {assume e1:"iRule\<noteq>iInv1 \<and> iRule\<noteq>iInv2"
     have "?P paraInv iInv paraRule iRule  invs"
       by (metis  a1 a2 a3 a4 d e1)
            
   }
   ultimately show "?P paraInv iInv paraRule iRule  invs"
     by blast
 qed
end
interpretation paraRuleInstValidateExTwoLessInvInst_rule_idle_inv1:paraRuleInstValidateExTwoLessInvInst
      
 "rule_idle::nat \<Rightarrow> rule "  "inv1::nat \<Rightarrow> nat\<Rightarrow>formula"  "iRule::nat" "iInv1::nat" "iInv2::nat" 
  
proof(unfold paraRuleInstValidateExTwoLessInvInst_def)
  show "((\<exists>ant0 cons0. inv1 iInv1 iInv2 = implyForm ant0 cons0) \<and>
    
     (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
      iInv1 \<le> N \<longrightarrow>
      iInv2 \<le> N \<longrightarrow>
      iRule = iInv1 \<longrightarrow> invHoldForRule (inv1 iInv1 iInv2) (rule_idle iRule) (invariants N))) \<and>
    
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow> iRule = iInv2 \<longrightarrow> invHoldForRule (inv1  iInv1 iInv2) (rule_idle iRule) (invariants N)) \<and>
   
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow>
     iRule \<noteq> iInv1 \<longrightarrow>
     iRule \<noteq> iInv2 \<longrightarrow> invHoldForRule (inv1  iInv1 iInv2) (rule_idle iRule) (invariants N))"
  
    (is "(?P1 \<and> ?P2) \<and> ?P3 \<and> ?P4")
  proof -
    have b1:"?P1"
      by auto
  
    have b2:"?P2"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
      
    have b3:"?P3"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
      
    have b4:"?P4"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4 \<longrightarrow> ?ANT5\<longrightarrow>  ?ANT6 \<longrightarrow>?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5" and c6:"?ANT6"
      from c1 c2 c3 c4 c5 c6
    have "?P22"
  apply -
 
  apply(auto intro!:forallVars1 simp  add :invHoldForRule2_def varsOfVar_def)
       
  done
  then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
  qed
 
      
    
  with b1 b2 b3 b4 show  "(?P1 \<and> ?P2) \<and>  ?P3 \<and>  ?P4"
      by blast
   qed
 qed
interpretation paraRuleInstValidateExLessInvInst_rule_idle_inv2:paraRuleInstValidateExLessInvInst
 "rule_idle::nat \<Rightarrow> rule "  "inv2::nat \<Rightarrow> formula"  "iRule::nat" "iInv1::nat"
proof(unfold paraRuleInstValidateExLessInvInst_def)
  show "(\<exists>ant0 cons0. inv2 iInv1 = implyForm ant0 cons0) \<and>
    (iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>iRule = iInv1 \<longrightarrow> invHoldForRule (inv2 iInv1) (rule_idle iRule) (invariants N)) \<and>
    (iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>iRule \<noteq> iInv1 \<longrightarrow> invHoldForRule (inv2 iInv1) (rule_idle iRule) (invariants N))"
    (is "?P1 \<and> ?P2 \<and>?P3") 
  proof -
    have b1:"?P1"
      by auto
  
    have b2:"?P2"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3"
      from c1 c2 c3 
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
 
    have b3:"?P3"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3"
      from c1 c2 c3
    
      have "?P23"
        
        apply -
        apply(cut_tac c3, simp)
        apply(rule_tac x="(implyForm ( eqn ( IVar ( Para ''n'' iRule) )  ( Const E ))    (neg ( eqn ( IVar ( Para ''n'' iInv1) )  ( Const E )) ) ) " in exI)
        apply(rule conjI)
        apply(cut_tac c1 c2,unfold  exTwoLessP_def, simp)
        apply(rule_tac x=" ( eqn ( IVar ( Para ''n'' iRule) )  ( Const E ))      " in exI)
        apply(unfold logicImply_def, auto)
        done
      then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
        qed
    
    with b1 b2 show "?P1 \<and> ?P2 \<and>?P3"
      by blast
  qed
qed
interpretation paraRuleInstValidateExTwoLessInvInst_rule_idle_inv3:paraRuleInstValidateExTwoLessInvInst
      
 "rule_idle::nat \<Rightarrow> rule "  "inv3::nat \<Rightarrow> nat\<Rightarrow>formula"  "iRule::nat" "iInv1::nat" "iInv2::nat" 
  
proof(unfold paraRuleInstValidateExTwoLessInvInst_def)
  show "((\<exists>ant0 cons0. inv3 iInv1 iInv2 = implyForm ant0 cons0) \<and>
    
     (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
      iInv1 \<le> N \<longrightarrow>
      iInv2 \<le> N \<longrightarrow>
      iRule = iInv1 \<longrightarrow> invHoldForRule (inv3 iInv1 iInv2) (rule_idle iRule) (invariants N))) \<and>
    
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow> iRule = iInv2 \<longrightarrow> invHoldForRule (inv3  iInv1 iInv2) (rule_idle iRule) (invariants N)) \<and>
   
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow>
     iRule \<noteq> iInv1 \<longrightarrow>
     iRule \<noteq> iInv2 \<longrightarrow> invHoldForRule (inv3  iInv1 iInv2) (rule_idle iRule) (invariants N))"
  
    (is "(?P1 \<and> ?P2) \<and> ?P3 \<and> ?P4")
  proof -
    have b1:"?P1"
      by auto
  
    have b2:"?P2"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
      
    have b3:"?P3"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
      
    have b4:"?P4"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4 \<longrightarrow> ?ANT5\<longrightarrow>  ?ANT6 \<longrightarrow>?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5" and c6:"?ANT6"
      from c1 c2 c3 c4 c5 c6
    have "?P22"
  apply -
 
  apply(auto intro!:forallVars1 simp  add :invHoldForRule2_def varsOfVar_def)
       
  done
  then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
  qed
 
      
    
  with b1 b2 b3 b4 show  "(?P1 \<and> ?P2) \<and>  ?P3 \<and>  ?P4"
      by blast
   qed
 qed
interpretation paraRuleInstValidateExLessInvInst_rule_idle_inv4:paraRuleInstValidateExLessInvInst
 "rule_idle::nat \<Rightarrow> rule "  "inv4::nat \<Rightarrow> formula"  "iRule::nat" "iInv1::nat"
proof(unfold paraRuleInstValidateExLessInvInst_def)
  show "(\<exists>ant0 cons0. inv4 iInv1 = implyForm ant0 cons0) \<and>
    (iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>iRule = iInv1 \<longrightarrow> invHoldForRule (inv4 iInv1) (rule_idle iRule) (invariants N)) \<and>
    (iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>iRule \<noteq> iInv1 \<longrightarrow> invHoldForRule (inv4 iInv1) (rule_idle iRule) (invariants N))"
    (is "?P1 \<and> ?P2 \<and>?P3") 
  proof -
    have b1:"?P1"
      by auto
  
    have b2:"?P2"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3"
      from c1 c2 c3 
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
 
    have b3:"?P3"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3"
      from c1 c2 c3
    
      have "?P23"
        
        apply -
        apply(cut_tac c3, simp)
        apply(rule_tac x="(implyForm ( eqn ( IVar ( Para ''n'' iRule) )  ( Const E ))    (neg ( eqn ( IVar ( Para ''n'' iInv1) )  ( Const C )) ) ) " in exI)
        apply(rule conjI)
        apply(cut_tac c1 c2,unfold  exTwoLessP_def, simp)
        apply(rule_tac x=" ( eqn ( IVar ( Para ''n'' iRule) )  ( Const E ))      " in exI)
        apply(unfold logicImply_def, auto)
        done
      then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
        qed
    
    with b1 b2 show "?P1 \<and> ?P2 \<and>?P3"
      by blast
  qed
qed
interpretation paraRuleInstValidateExTwoLessInvInst_rule_idle_inv5:paraRuleInstValidateExTwoLessInvInst
      
 "rule_idle::nat \<Rightarrow> rule "  "inv5::nat \<Rightarrow> nat\<Rightarrow>formula"  "iRule::nat" "iInv1::nat" "iInv2::nat" 
  
proof(unfold paraRuleInstValidateExTwoLessInvInst_def)
  show "((\<exists>ant0 cons0. inv5 iInv1 iInv2 = implyForm ant0 cons0) \<and>
    
     (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
      iInv1 \<le> N \<longrightarrow>
      iInv2 \<le> N \<longrightarrow>
      iRule = iInv1 \<longrightarrow> invHoldForRule (inv5 iInv1 iInv2) (rule_idle iRule) (invariants N))) \<and>
    
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow> iRule = iInv2 \<longrightarrow> invHoldForRule (inv5  iInv1 iInv2) (rule_idle iRule) (invariants N)) \<and>
   
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow>
     iRule \<noteq> iInv1 \<longrightarrow>
     iRule \<noteq> iInv2 \<longrightarrow> invHoldForRule (inv5  iInv1 iInv2) (rule_idle iRule) (invariants N))"
  
    (is "(?P1 \<and> ?P2) \<and> ?P3 \<and> ?P4")
  proof -
    have b1:"?P1"
      by auto
  
    have b2:"?P2"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
      
    have b3:"?P3"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
      
    have b4:"?P4"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4 \<longrightarrow> ?ANT5\<longrightarrow>  ?ANT6 \<longrightarrow>?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5" and c6:"?ANT6"
      from c1 c2 c3 c4 c5 c6
    have "?P22"
  apply -
 
  apply(auto intro!:forallVars1 simp  add :invHoldForRule2_def varsOfVar_def)
       
  done
  then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
  qed
 
      
    
  with b1 b2 b3 b4 show  "(?P1 \<and> ?P2) \<and>  ?P3 \<and>  ?P4"
      by blast
   qed
 qed
interpretation paraRuleInstValidateExTwoLessInvInst_rule_try_inv1:paraRuleInstValidateExTwoLessInvInst
      
 "rule_try::nat \<Rightarrow> rule "  "inv1::nat \<Rightarrow> nat\<Rightarrow>formula"  "iRule::nat" "iInv1::nat" "iInv2::nat" 
  
proof(unfold paraRuleInstValidateExTwoLessInvInst_def)
  show "((\<exists>ant0 cons0. inv1 iInv1 iInv2 = implyForm ant0 cons0) \<and>
    
     (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
      iInv1 \<le> N \<longrightarrow>
      iInv2 \<le> N \<longrightarrow>
      iRule = iInv1 \<longrightarrow> invHoldForRule (inv1 iInv1 iInv2) (rule_try iRule) (invariants N))) \<and>
    
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow> iRule = iInv2 \<longrightarrow> invHoldForRule (inv1  iInv1 iInv2) (rule_try iRule) (invariants N)) \<and>
   
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow>
     iRule \<noteq> iInv1 \<longrightarrow>
     iRule \<noteq> iInv2 \<longrightarrow> invHoldForRule (inv1  iInv1 iInv2) (rule_try iRule) (invariants N))"
  
    (is "(?P1 \<and> ?P2) \<and> ?P3 \<and> ?P4")
  proof -
    have b1:"?P1"
      by auto
  
    have b2:"?P2"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
      
    have b3:"?P3"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
      
    have b4:"?P4"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4 \<longrightarrow> ?ANT5\<longrightarrow>  ?ANT6 \<longrightarrow>?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5" and c6:"?ANT6"
      from c1 c2 c3 c4 c5 c6
    have "?P22"
  apply -
 
  apply(auto intro!:forallVars1 simp  add :invHoldForRule2_def varsOfVar_def)
       
  done
  then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
  qed
 
      
    
  with b1 b2 b3 b4 show  "(?P1 \<and> ?P2) \<and>  ?P3 \<and>  ?P4"
      by blast
   qed
 qed
interpretation paraRuleInstValidateExLessInvInst_rule_try_inv2:paraRuleInstValidateExLessInvInst
 "rule_try::nat \<Rightarrow> rule "  "inv2::nat \<Rightarrow> formula"  "iRule::nat" "iInv1::nat"
proof(unfold paraRuleInstValidateExLessInvInst_def)
  show "(\<exists>ant0 cons0. inv2 iInv1 = implyForm ant0 cons0) \<and>
    (iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>iRule = iInv1 \<longrightarrow> invHoldForRule (inv2 iInv1) (rule_try iRule) (invariants N)) \<and>
    (iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>iRule \<noteq> iInv1 \<longrightarrow> invHoldForRule (inv2 iInv1) (rule_try iRule) (invariants N))"
    (is "?P1 \<and> ?P2 \<and>?P3") 
  proof -
    have b1:"?P1"
      by auto
  
    have b2:"?P2"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3"
      from c1 c2 c3 
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
 
    have b3:"?P3"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3"
      from c1 c2 c3
    have "?P22"
  apply -
 
  apply(auto intro!:forallVars1 simp  add :invHoldForRule2_def varsOfVar_def)
       
  done
  then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
  qed
 
    
    with b1 b2 show "?P1 \<and> ?P2 \<and>?P3"
      by blast
  qed
qed
interpretation paraRuleInstValidateExTwoLessInvInst_rule_try_inv3:paraRuleInstValidateExTwoLessInvInst
      
 "rule_try::nat \<Rightarrow> rule "  "inv3::nat \<Rightarrow> nat\<Rightarrow>formula"  "iRule::nat" "iInv1::nat" "iInv2::nat" 
  
proof(unfold paraRuleInstValidateExTwoLessInvInst_def)
  show "((\<exists>ant0 cons0. inv3 iInv1 iInv2 = implyForm ant0 cons0) \<and>
    
     (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
      iInv1 \<le> N \<longrightarrow>
      iInv2 \<le> N \<longrightarrow>
      iRule = iInv1 \<longrightarrow> invHoldForRule (inv3 iInv1 iInv2) (rule_try iRule) (invariants N))) \<and>
    
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow> iRule = iInv2 \<longrightarrow> invHoldForRule (inv3  iInv1 iInv2) (rule_try iRule) (invariants N)) \<and>
   
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow>
     iRule \<noteq> iInv1 \<longrightarrow>
     iRule \<noteq> iInv2 \<longrightarrow> invHoldForRule (inv3  iInv1 iInv2) (rule_try iRule) (invariants N))"
  
    (is "(?P1 \<and> ?P2) \<and> ?P3 \<and> ?P4")
  proof -
    have b1:"?P1"
      by auto
  
    have b2:"?P2"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
      
    have b3:"?P3"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
      
    have b4:"?P4"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4 \<longrightarrow> ?ANT5\<longrightarrow>  ?ANT6 \<longrightarrow>?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5" and c6:"?ANT6"
      from c1 c2 c3 c4 c5 c6
    have "?P22"
  apply -
 
  apply(auto intro!:forallVars1 simp  add :invHoldForRule2_def varsOfVar_def)
       
  done
  then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
  qed
 
      
    
  with b1 b2 b3 b4 show  "(?P1 \<and> ?P2) \<and>  ?P3 \<and>  ?P4"
      by blast
   qed
 qed
interpretation paraRuleInstValidateExLessInvInst_rule_try_inv4:paraRuleInstValidateExLessInvInst
 "rule_try::nat \<Rightarrow> rule "  "inv4::nat \<Rightarrow> formula"  "iRule::nat" "iInv1::nat"
proof(unfold paraRuleInstValidateExLessInvInst_def)
  show "(\<exists>ant0 cons0. inv4 iInv1 = implyForm ant0 cons0) \<and>
    (iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>iRule = iInv1 \<longrightarrow> invHoldForRule (inv4 iInv1) (rule_try iRule) (invariants N)) \<and>
    (iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>iRule \<noteq> iInv1 \<longrightarrow> invHoldForRule (inv4 iInv1) (rule_try iRule) (invariants N))"
    (is "?P1 \<and> ?P2 \<and>?P3") 
  proof -
    have b1:"?P1"
      by auto
  
    have b2:"?P2"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3"
      from c1 c2 c3 
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
 
    have b3:"?P3"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3"
      from c1 c2 c3
    have "?P22"
  apply -
 
  apply(auto intro!:forallVars1 simp  add :invHoldForRule2_def varsOfVar_def)
       
  done
  then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
  qed
 
    
    with b1 b2 show "?P1 \<and> ?P2 \<and>?P3"
      by blast
  qed
qed
interpretation paraRuleInstValidateExTwoLessInvInst_rule_try_inv5:paraRuleInstValidateExTwoLessInvInst
      
 "rule_try::nat \<Rightarrow> rule "  "inv5::nat \<Rightarrow> nat\<Rightarrow>formula"  "iRule::nat" "iInv1::nat" "iInv2::nat" 
  
proof(unfold paraRuleInstValidateExTwoLessInvInst_def)
  show "((\<exists>ant0 cons0. inv5 iInv1 iInv2 = implyForm ant0 cons0) \<and>
    
     (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
      iInv1 \<le> N \<longrightarrow>
      iInv2 \<le> N \<longrightarrow>
      iRule = iInv1 \<longrightarrow> invHoldForRule (inv5 iInv1 iInv2) (rule_try iRule) (invariants N))) \<and>
    
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow> iRule = iInv2 \<longrightarrow> invHoldForRule (inv5  iInv1 iInv2) (rule_try iRule) (invariants N)) \<and>
   
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow>
     iRule \<noteq> iInv1 \<longrightarrow>
     iRule \<noteq> iInv2 \<longrightarrow> invHoldForRule (inv5  iInv1 iInv2) (rule_try iRule) (invariants N))"
  
    (is "(?P1 \<and> ?P2) \<and> ?P3 \<and> ?P4")
  proof -
    have b1:"?P1"
      by auto
  
    have b2:"?P2"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
      
    have b3:"?P3"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
      
    have b4:"?P4"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4 \<longrightarrow> ?ANT5\<longrightarrow>  ?ANT6 \<longrightarrow>?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5" and c6:"?ANT6"
      from c1 c2 c3 c4 c5 c6
    have "?P22"
  apply -
 
  apply(auto intro!:forallVars1 simp  add :invHoldForRule2_def varsOfVar_def)
       
  done
  then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
  qed
 
      
    
  with b1 b2 b3 b4 show  "(?P1 \<and> ?P2) \<and>  ?P3 \<and>  ?P4"
      by blast
   qed
 qed
interpretation paraRuleInstValidateExTwoLessInvInst_rule_exit_inv1:paraRuleInstValidateExTwoLessInvInst
      
 "rule_exit::nat \<Rightarrow> rule "  "inv1::nat \<Rightarrow> nat\<Rightarrow>formula"  "iRule::nat" "iInv1::nat" "iInv2::nat" 
  
proof(unfold paraRuleInstValidateExTwoLessInvInst_def)
  show "((\<exists>ant0 cons0. inv1 iInv1 iInv2 = implyForm ant0 cons0) \<and>
    
     (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
      iInv1 \<le> N \<longrightarrow>
      iInv2 \<le> N \<longrightarrow>
      iRule = iInv1 \<longrightarrow> invHoldForRule (inv1 iInv1 iInv2) (rule_exit iRule) (invariants N))) \<and>
    
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow> iRule = iInv2 \<longrightarrow> invHoldForRule (inv1  iInv1 iInv2) (rule_exit iRule) (invariants N)) \<and>
   
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow>
     iRule \<noteq> iInv1 \<longrightarrow>
     iRule \<noteq> iInv2 \<longrightarrow> invHoldForRule (inv1  iInv1 iInv2) (rule_exit iRule) (invariants N))"
  
    (is "(?P1 \<and> ?P2) \<and> ?P3 \<and> ?P4")
  proof -
    have b1:"?P1"
      by auto
  
    have b2:"?P2"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P23"
        
        apply -
        apply(cut_tac c3, simp)
        apply(rule_tac x="(implyForm ( eqn ( IVar ( Para ''n'' iInv2) )  ( Const E ))    (neg ( eqn ( IVar ( Para ''n'' iInv1) )  ( Const C )) ) ) " in exI)
        apply(rule conjI)
        apply(cut_tac c1 c2,unfold  exTwoLessP_def, simp)
        apply(rule_tac x=" ( eqn ( IVar ( Para ''n'' iInv1) )  ( Const C ))      " in exI)
        apply(unfold logicImply_def, auto)
        done
      then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
        qed
      
    have b3:"?P3"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P24"
        
        apply -
        (*apply(cut_tac c3,simp,rule conjI, force intro!: forallVars1 simp add :varsOfVar_def)*)
        apply(cut_tac c3,simp)
        apply(rule_tac x="(implyForm ( eqn ( IVar ( Para ''n'' iInv1) )  ( Const E ))    (neg ( eqn ( IVar ( Para ''n'' iInv2) )  ( Const C )) ) ) " in exI)
        apply(rule conjI)
        apply(cut_tac c1 c2,unfold  exTwoLessP_def, simp)
        apply(rule_tac x=" ( eqn ( IVar ( Para ''n'' iInv2) )  ( Const C ))     " in exI)
        apply(rule_tac x=" ( eqn ( IVar ( Para ''n'' iInv1) )  ( Const E ))     " in exI)
        apply(unfold logicImply_def, auto)
        done
      then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
        qed
      
    have b4:"?P4"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4 \<longrightarrow> ?ANT5\<longrightarrow>  ?ANT6 \<longrightarrow>?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5" and c6:"?ANT6"
      from c1 c2 c3 c4 c5 c6
    have "?P22"
  apply -
 
  apply(auto intro!:forallVars1 simp  add :invHoldForRule2_def varsOfVar_def)
       
  done
  then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
  qed
 
      
    
  with b1 b2 b3 b4 show  "(?P1 \<and> ?P2) \<and>  ?P3 \<and>  ?P4"
      by blast
   qed
 qed
interpretation paraRuleInstValidateExLessInvInst_rule_exit_inv2:paraRuleInstValidateExLessInvInst
 "rule_exit::nat \<Rightarrow> rule "  "inv2::nat \<Rightarrow> formula"  "iRule::nat" "iInv1::nat"
proof(unfold paraRuleInstValidateExLessInvInst_def)
  show "(\<exists>ant0 cons0. inv2 iInv1 = implyForm ant0 cons0) \<and>
    (iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>iRule = iInv1 \<longrightarrow> invHoldForRule (inv2 iInv1) (rule_exit iRule) (invariants N)) \<and>
    (iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>iRule \<noteq> iInv1 \<longrightarrow> invHoldForRule (inv2 iInv1) (rule_exit iRule) (invariants N))"
    (is "?P1 \<and> ?P2 \<and>?P3") 
  proof -
    have b1:"?P1"
      by auto
  
    have b2:"?P2"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3"
      from c1 c2 c3 
    
      have "?P24"
        
        apply -
        (*apply(cut_tac c3,simp,rule conjI, force intro!: forallVars1 simp add :varsOfVar_def)*)
        apply(cut_tac c3,simp)
        apply(rule_tac x="(implyForm ( eqn ( IVar ( Global ''x'') )  ( Const true ))    (neg ( eqn ( IVar ( Para ''n'' iInv1) )  ( Const C )) ) ) " in exI)
        apply(rule conjI)
        apply(cut_tac c1 c2,unfold  exLessP_def, simp)
        apply(rule_tac x=" ( eqn ( IVar ( Para ''n'' iInv1) )  ( Const C ))     " in exI)
        apply(rule_tac x=" ( eqn ( IVar ( Global ''x'') )  ( Const true ))     " in exI)
        apply(unfold logicImply_def, auto)
        done
      then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
        qed
 
    have b3:"?P3"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3"
      from c1 c2 c3
    have "?P22"
  apply -
 
  apply(auto intro!:forallVars1 simp  add :invHoldForRule2_def varsOfVar_def)
       
  done
  then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
  qed
 
    
    with b1 b2 show "?P1 \<and> ?P2 \<and>?P3"
      by blast
  qed
qed
interpretation paraRuleInstValidateExTwoLessInvInst_rule_exit_inv3:paraRuleInstValidateExTwoLessInvInst
      
 "rule_exit::nat \<Rightarrow> rule "  "inv3::nat \<Rightarrow> nat\<Rightarrow>formula"  "iRule::nat" "iInv1::nat" "iInv2::nat" 
  
proof(unfold paraRuleInstValidateExTwoLessInvInst_def)
  show "((\<exists>ant0 cons0. inv3 iInv1 iInv2 = implyForm ant0 cons0) \<and>
    
     (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
      iInv1 \<le> N \<longrightarrow>
      iInv2 \<le> N \<longrightarrow>
      iRule = iInv1 \<longrightarrow> invHoldForRule (inv3 iInv1 iInv2) (rule_exit iRule) (invariants N))) \<and>
    
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow> iRule = iInv2 \<longrightarrow> invHoldForRule (inv3  iInv1 iInv2) (rule_exit iRule) (invariants N)) \<and>
   
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow>
     iRule \<noteq> iInv1 \<longrightarrow>
     iRule \<noteq> iInv2 \<longrightarrow> invHoldForRule (inv3  iInv1 iInv2) (rule_exit iRule) (invariants N))"
  
    (is "(?P1 \<and> ?P2) \<and> ?P3 \<and> ?P4")
  proof -
    have b1:"?P1"
      by auto
  
    have b2:"?P2"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P23"
        
        apply -
        apply(cut_tac c3, simp)
        apply(rule_tac x="(implyForm ( eqn ( IVar ( Para ''n'' iInv1) )  ( Const C ))    (neg ( eqn ( IVar ( Para ''n'' iInv2) )  ( Const C )) ) ) " in exI)
        apply(rule conjI)
        apply(cut_tac c1 c2,unfold  exTwoLessP_def, simp)
        apply(rule_tac x=" ( eqn ( IVar ( Para ''n'' iInv1) )  ( Const C ))      " in exI)
        apply(unfold logicImply_def, auto)
        done
      then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
        qed
      
    have b3:"?P3"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
      
    have b4:"?P4"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4 \<longrightarrow> ?ANT5\<longrightarrow>  ?ANT6 \<longrightarrow>?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5" and c6:"?ANT6"
      from c1 c2 c3 c4 c5 c6
    have "?P22"
  apply -
 
  apply(auto intro!:forallVars1 simp  add :invHoldForRule2_def varsOfVar_def)
       
  done
  then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
  qed
 
      
    
  with b1 b2 b3 b4 show  "(?P1 \<and> ?P2) \<and>  ?P3 \<and>  ?P4"
      by blast
   qed
 qed
interpretation paraRuleInstValidateExLessInvInst_rule_exit_inv4:paraRuleInstValidateExLessInvInst
 "rule_exit::nat \<Rightarrow> rule "  "inv4::nat \<Rightarrow> formula"  "iRule::nat" "iInv1::nat"
proof(unfold paraRuleInstValidateExLessInvInst_def)
  show "(\<exists>ant0 cons0. inv4 iInv1 = implyForm ant0 cons0) \<and>
    (iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>iRule = iInv1 \<longrightarrow> invHoldForRule (inv4 iInv1) (rule_exit iRule) (invariants N)) \<and>
    (iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>iRule \<noteq> iInv1 \<longrightarrow> invHoldForRule (inv4 iInv1) (rule_exit iRule) (invariants N))"
    (is "?P1 \<and> ?P2 \<and>?P3") 
  proof -
    have b1:"?P1"
      by auto
  
    have b2:"?P2"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3"
      from c1 c2 c3 
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
 
    have b3:"?P3"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3"
      from c1 c2 c3
    have "?P22"
  apply -
 
  apply(auto intro!:forallVars1 simp  add :invHoldForRule2_def varsOfVar_def)
       
  done
  then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
  qed
 
    
    with b1 b2 show "?P1 \<and> ?P2 \<and>?P3"
      by blast
  qed
qed
interpretation paraRuleInstValidateExTwoLessInvInst_rule_exit_inv5:paraRuleInstValidateExTwoLessInvInst
      
 "rule_exit::nat \<Rightarrow> rule "  "inv5::nat \<Rightarrow> nat\<Rightarrow>formula"  "iRule::nat" "iInv1::nat" "iInv2::nat" 
  
proof(unfold paraRuleInstValidateExTwoLessInvInst_def)
  show "((\<exists>ant0 cons0. inv5 iInv1 iInv2 = implyForm ant0 cons0) \<and>
    
     (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
      iInv1 \<le> N \<longrightarrow>
      iInv2 \<le> N \<longrightarrow>
      iRule = iInv1 \<longrightarrow> invHoldForRule (inv5 iInv1 iInv2) (rule_exit iRule) (invariants N))) \<and>
    
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow> iRule = iInv2 \<longrightarrow> invHoldForRule (inv5  iInv1 iInv2) (rule_exit iRule) (invariants N)) \<and>
   
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow>
     iRule \<noteq> iInv1 \<longrightarrow>
     iRule \<noteq> iInv2 \<longrightarrow> invHoldForRule (inv5  iInv1 iInv2) (rule_exit iRule) (invariants N))"
  
    (is "(?P1 \<and> ?P2) \<and> ?P3 \<and> ?P4")
  proof -
    have b1:"?P1"
      by auto
  
    have b2:"?P2"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
      
    have b3:"?P3"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
      
    have b4:"?P4"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4 \<longrightarrow> ?ANT5\<longrightarrow>  ?ANT6 \<longrightarrow>?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5" and c6:"?ANT6"
      from c1 c2 c3 c4 c5 c6
    have "?P22"
  apply -
 
  apply(auto intro!:forallVars1 simp  add :invHoldForRule2_def varsOfVar_def)
       
  done
  then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
  qed
 
      
    
  with b1 b2 b3 b4 show  "(?P1 \<and> ?P2) \<and>  ?P3 \<and>  ?P4"
      by blast
   qed
 qed
interpretation paraRuleInstValidateExTwoLessInvInst_rule_crit_inv1:paraRuleInstValidateExTwoLessInvInst
      
 "rule_crit::nat \<Rightarrow> rule "  "inv1::nat \<Rightarrow> nat\<Rightarrow>formula"  "iRule::nat" "iInv1::nat" "iInv2::nat" 
  
proof(unfold paraRuleInstValidateExTwoLessInvInst_def)
  show "((\<exists>ant0 cons0. inv1 iInv1 iInv2 = implyForm ant0 cons0) \<and>
    
     (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
      iInv1 \<le> N \<longrightarrow>
      iInv2 \<le> N \<longrightarrow>
      iRule = iInv1 \<longrightarrow> invHoldForRule (inv1 iInv1 iInv2) (rule_crit iRule) (invariants N))) \<and>
    
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow> iRule = iInv2 \<longrightarrow> invHoldForRule (inv1  iInv1 iInv2) (rule_crit iRule) (invariants N)) \<and>
   
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow>
     iRule \<noteq> iInv1 \<longrightarrow>
     iRule \<noteq> iInv2 \<longrightarrow> invHoldForRule (inv1  iInv1 iInv2) (rule_crit iRule) (invariants N))"
  
    (is "(?P1 \<and> ?P2) \<and> ?P3 \<and> ?P4")
  proof -
    have b1:"?P1"
      by auto
  
    have b2:"?P2"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
      
    have b3:"?P3"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
      
    have b4:"?P4"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4 \<longrightarrow> ?ANT5\<longrightarrow>  ?ANT6 \<longrightarrow>?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5" and c6:"?ANT6"
      from c1 c2 c3 c4 c5 c6
    have "?P22"
  apply -
 
  apply(auto intro!:forallVars1 simp  add :invHoldForRule2_def varsOfVar_def)
       
  done
  then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
  qed
 
      
    
  with b1 b2 b3 b4 show  "(?P1 \<and> ?P2) \<and>  ?P3 \<and>  ?P4"
      by blast
   qed
 qed
interpretation paraRuleInstValidateExLessInvInst_rule_crit_inv2:paraRuleInstValidateExLessInvInst
 "rule_crit::nat \<Rightarrow> rule "  "inv2::nat \<Rightarrow> formula"  "iRule::nat" "iInv1::nat"
proof(unfold paraRuleInstValidateExLessInvInst_def)
  show "(\<exists>ant0 cons0. inv2 iInv1 = implyForm ant0 cons0) \<and>
    (iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>iRule = iInv1 \<longrightarrow> invHoldForRule (inv2 iInv1) (rule_crit iRule) (invariants N)) \<and>
    (iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>iRule \<noteq> iInv1 \<longrightarrow> invHoldForRule (inv2 iInv1) (rule_crit iRule) (invariants N))"
    (is "?P1 \<and> ?P2 \<and>?P3") 
  proof -
    have b1:"?P1"
      by auto
  
    have b2:"?P2"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3"
      from c1 c2 c3 
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
 
    have b3:"?P3"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3"
      from c1 c2 c3
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
    
    with b1 b2 show "?P1 \<and> ?P2 \<and>?P3"
      by blast
  qed
qed
interpretation paraRuleInstValidateExTwoLessInvInst_rule_crit_inv3:paraRuleInstValidateExTwoLessInvInst
      
 "rule_crit::nat \<Rightarrow> rule "  "inv3::nat \<Rightarrow> nat\<Rightarrow>formula"  "iRule::nat" "iInv1::nat" "iInv2::nat" 
  
proof(unfold paraRuleInstValidateExTwoLessInvInst_def)
  show "((\<exists>ant0 cons0. inv3 iInv1 iInv2 = implyForm ant0 cons0) \<and>
    
     (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
      iInv1 \<le> N \<longrightarrow>
      iInv2 \<le> N \<longrightarrow>
      iRule = iInv1 \<longrightarrow> invHoldForRule (inv3 iInv1 iInv2) (rule_crit iRule) (invariants N))) \<and>
    
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow> iRule = iInv2 \<longrightarrow> invHoldForRule (inv3  iInv1 iInv2) (rule_crit iRule) (invariants N)) \<and>
   
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow>
     iRule \<noteq> iInv1 \<longrightarrow>
     iRule \<noteq> iInv2 \<longrightarrow> invHoldForRule (inv3  iInv1 iInv2) (rule_crit iRule) (invariants N))"
  
    (is "(?P1 \<and> ?P2) \<and> ?P3 \<and> ?P4")
  proof -
    have b1:"?P1"
      by auto
  
    have b2:"?P2"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
      
    have b3:"?P3"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P24"
        
        apply -
        (*apply(cut_tac c3,simp,rule conjI, force intro!: forallVars1 simp add :varsOfVar_def)*)
        apply(cut_tac c3,simp)
        apply(rule_tac x="(implyForm ( eqn ( IVar ( Global ''x'') )  ( Const true ))    (neg ( eqn ( IVar ( Para ''n'' iInv1) )  ( Const E )) ) ) " in exI)
        apply(rule conjI)
        apply(cut_tac c1 c2,unfold  exLessP_def, simp)
        apply(rule_tac x=" ( eqn ( IVar ( Global ''x'') )  ( Const true ))     " in exI)
        apply(rule_tac x=" ( eqn ( IVar ( Para ''n'' iInv1) )  ( Const E ))     " in exI)
        apply(unfold logicImply_def, auto)
        done
      then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
        qed
      
    have b4:"?P4"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4 \<longrightarrow> ?ANT5\<longrightarrow>  ?ANT6 \<longrightarrow>?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5" and c6:"?ANT6"
      from c1 c2 c3 c4 c5 c6
    have "?P22"
  apply -
 
  apply(auto intro!:forallVars1 simp  add :invHoldForRule2_def varsOfVar_def)
       
  done
  then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
  qed
 
      
    
  with b1 b2 b3 b4 show  "(?P1 \<and> ?P2) \<and>  ?P3 \<and>  ?P4"
      by blast
   qed
 qed
interpretation paraRuleInstValidateExLessInvInst_rule_crit_inv4:paraRuleInstValidateExLessInvInst
 "rule_crit::nat \<Rightarrow> rule "  "inv4::nat \<Rightarrow> formula"  "iRule::nat" "iInv1::nat"
proof(unfold paraRuleInstValidateExLessInvInst_def)
  show "(\<exists>ant0 cons0. inv4 iInv1 = implyForm ant0 cons0) \<and>
    (iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>iRule = iInv1 \<longrightarrow> invHoldForRule (inv4 iInv1) (rule_crit iRule) (invariants N)) \<and>
    (iRule \<le> N \<longrightarrow>iInv1 \<le> N\<longrightarrow>iRule \<noteq> iInv1 \<longrightarrow> invHoldForRule (inv4 iInv1) (rule_crit iRule) (invariants N))"
    (is "?P1 \<and> ?P2 \<and>?P3") 
  proof -
    have b1:"?P1"
      by auto
  
    have b2:"?P2"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3"
      from c1 c2 c3 
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
 
    have b3:"?P3"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3"
      from c1 c2 c3
    
      have "?P21"
        apply -
        apply(auto)
        (*apply(rule disjI1)
        apply( auto simp add:statementEnableForm_def)*)
        done
     then  show "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
       by blast
    qed
    
    with b1 b2 show "?P1 \<and> ?P2 \<and>?P3"
      by blast
  qed
qed
interpretation paraRuleInstValidateExTwoLessInvInst_rule_crit_inv5:paraRuleInstValidateExTwoLessInvInst
      
 "rule_crit::nat \<Rightarrow> rule "  "inv5::nat \<Rightarrow> nat\<Rightarrow>formula"  "iRule::nat" "iInv1::nat" "iInv2::nat" 
  
proof(unfold paraRuleInstValidateExTwoLessInvInst_def)
  show "((\<exists>ant0 cons0. inv5 iInv1 iInv2 = implyForm ant0 cons0) \<and>
    
     (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
      iInv1 \<le> N \<longrightarrow>
      iInv2 \<le> N \<longrightarrow>
      iRule = iInv1 \<longrightarrow> invHoldForRule (inv5 iInv1 iInv2) (rule_crit iRule) (invariants N))) \<and>
    
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow> iRule = iInv2 \<longrightarrow> invHoldForRule (inv5  iInv1 iInv2) (rule_crit iRule) (invariants N)) \<and>
   
    (iInv1 \<noteq> iInv2\<longrightarrow>iRule \<le> N \<longrightarrow>
     iInv1 \<le> N \<longrightarrow>
     iInv2 \<le> N \<longrightarrow>
     iRule \<noteq> iInv1 \<longrightarrow>
     iRule \<noteq> iInv2 \<longrightarrow> invHoldForRule (inv5  iInv1 iInv2) (rule_crit iRule) (invariants N))"
  
    (is "(?P1 \<and> ?P2) \<and> ?P3 \<and> ?P4")
  proof -
    have b1:"?P1"
      by auto
  
    have b2:"?P2"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P23"
        
        apply -
        apply(cut_tac c3, simp)
        apply(rule_tac x="(implyForm ( eqn ( IVar ( Global ''x'') )  ( Const true ))    (neg ( eqn ( IVar ( Para ''n'' iInv2) )  ( Const C )) ) ) " in exI)
        apply(rule conjI)
        apply(cut_tac c1 c2,unfold  exLessP_def, simp)
        apply(rule_tac x=" ( eqn ( IVar ( Global ''x'') )  ( Const true ))      " in exI)
        apply(unfold logicImply_def, auto)
        done
      then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
        qed
      
    have b3:"?P3"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4\<longrightarrow> ?ANT5 \<longrightarrow> ?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5"
      from c1 c2 c3 c4 c5
    
      have "?P24"
        
        apply -
        (*apply(cut_tac c3,simp,rule conjI, force intro!: forallVars1 simp add :varsOfVar_def)*)
        apply(cut_tac c3,simp)
        apply(rule_tac x="(implyForm ( eqn ( IVar ( Global ''x'') )  ( Const true ))    (neg ( eqn ( IVar ( Para ''n'' iInv1) )  ( Const C )) ) ) " in exI)
        apply(rule conjI)
        apply(cut_tac c1 c2,unfold  exLessP_def, simp)
        apply(rule_tac x=" ( eqn ( IVar ( Global ''x'') )  ( Const true ))     " in exI)
        apply(rule_tac x=" ( eqn ( IVar ( Para ''n'' iInv1) )  ( Const C ))     " in exI)
        apply(unfold logicImply_def, auto)
        done
      then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
        qed
      
    have b4:"?P4"  (is "?ANT1 \<longrightarrow> ?ANT2 \<longrightarrow> ?ANT3 \<longrightarrow>  ?ANT4 \<longrightarrow> ?ANT5\<longrightarrow>  ?ANT6 \<longrightarrow>?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24\<or> ?P25")
    proof(rule impI)+
      assume c1:"?ANT1" and c2:"?ANT2" and c3:"?ANT3" and c4:"?ANT4" and c5:"?ANT5" and c6:"?ANT6"
      from c1 c2 c3 c4 c5 c6
    have "?P22"
  apply -
 
  apply(auto intro!:forallVars1 simp  add :invHoldForRule2_def varsOfVar_def)
       
  done
  then show  "?P21 \<or> ?P22 \<or> ?P23 \<or> ?P24 \<or> ?P25"
        by blast
  qed
 
      
    
  with b1 b2 b3 b4 show  "(?P1 \<and> ?P2) \<and>  ?P3 \<and>  ?P4"
      by blast
   qed
 qed
lemma main:
  assumes   a1:"s \<in> reachableSet { mutualIni  N} (rules N)"  and a2:"0<N"
  shows "\<forall>inv. inv \<in>(invariants N)\<longrightarrow>formEval inv s"
proof(rule consistentLemma)
  show "consistent (invariants N) {mutualIni  N} (rules N)"
  proof(cut_tac a1, unfold consistent_def,rule conjI)
    show " \<forall>inv ini s. inv \<in>(invariants N)\<longrightarrow> ini \<in>{ mutualIni  N}\<longrightarrow> formEval ini s\<longrightarrow> formEval inv s"
    proof((rule allI)+,(rule impI)+)
      fix inv ini s 
      assume b1:"inv \<in>(invariants N) " and b2:"ini \<in> { mutualIni  N} " and b3:"formEval ini s"
      show "formEval inv s"
      proof -     
        
        have c1:" exTwoLessP N (% i j .  inv= inv1  i j )  \<or> exLessP N (% i .  inv= inv2  i )  \<or> exTwoLessP N (% i j .  inv= inv3  i j )  \<or> exLessP N (% i .  inv= inv4  i )  \<or> exTwoLessP N (% i j .  inv= inv5  i j )   "
          by (cut_tac b1, simp )       moreover
        {assume d1: " exTwoLessP N (% i j .  inv= inv1  i j )  "
          have "formEval inv s"
            by (metis b2 b3 d1 iniImply_Inv1.iniImplyInv)}
       moreover
        {assume d1: " exLessP N (% i .  inv= inv2  i )  "
          have "formEval inv s"
            by (metis b2 b3 d1 iniImply_Inv2.iniImplyInv)}
       moreover
        {assume d1: " exTwoLessP N (% i j .  inv= inv3  i j )  "
          have "formEval inv s"
            by (metis b2 b3 d1 iniImply_Inv3.iniImplyInv)}
       moreover
        {assume d1: " exLessP N (% i .  inv= inv4  i )  "
          have "formEval inv s"
            by (metis b2 b3 d1 iniImply_Inv4.iniImplyInv)}
       moreover
        {assume d1: " exTwoLessP N (% i j .  inv= inv5  i j )  "
          have "formEval inv s"
            by (metis b2 b3 d1 iniImply_Inv5.iniImplyInv)}
      ultimately show "formEval inv s"
      by blast
      qed
    qed
next
   show  "\<forall>inv r. inv \<in> invariants N\<longrightarrow> r \<in>rules N\<longrightarrow> invHoldForRule inv r (invariants N) "
   
   proof((rule allI)+,(rule impI)+)
      fix inv r
      assume b1:"inv \<in> invariants N" and b2:"r \<in> rules N"
      have c1:"exLessP N (%i.  r=rule_idle i )\<or>exLessP N (%i.  r=rule_try i )\<or>exLessP N (%i.  r=rule_exit i )\<or>exLessP N (%i.  r=rule_crit i )" 
        apply(cut_tac  b2)
        apply auto
        done      moreover
        {assume c1: "exLessP N (%i.  r= rule_idle i)
"
         
         from c1 obtain iRule where c2:"iRule \<le> N \<and> r= rule_idle iRule" 
         by (auto simp add: exLessP_def)
         
         have c3:"  exTwoLessP N (% i j .  inv= inv1  i j )  \<or> exLessP N (% i .  inv= inv2  i )  \<or> exTwoLessP N (% i j .  inv= inv3  i j )  \<or> exLessP N (% i .  inv= inv4  i )  \<or> exTwoLessP N (% i j .  inv= inv5  i j )     "
          by (cut_tac b1, simp )
          
         moreover
        {assume d1:" exTwoLessP N (%i j.  inv= inv1 i j)"
            from d1 obtain iInv1 and iInv2 
            where d2:"iInv1 \<le> N \<and> iInv2 \<le>N \<and> iInv1 \<noteq>iInv2\<and> inv= inv1 iInv1 iInv2" 
            by (-,unfold exTwoLessP_def,auto)
          have "invHoldForRule (inv1 iInv1 iInv2) (rule_idle iRule) (invariants N) "
            apply(cut_tac  c2 d2)
            by (metis paraRuleInstValidateExTwoLessInvInst_rule_idle_inv1.paraRuleInstValidateExTwoLessInvInst)
          then have "invHoldForRule inv r (invariants N) "
            by(cut_tac c2 d2, simp) 
        }moreover
        {assume d1:" exLessP N (%i .  inv= inv2 i )"
            from d1 obtain iInv1  
            where d2:"iInv1 \<le> N  \<and> inv= inv2 iInv1  " 
            by (-,unfold exLessP_def,auto)
          have "invHoldForRule (inv2 iInv1  ) (rule_idle iRule) (invariants N) "
            apply(cut_tac  c2 d2)
            by (metis paraRuleInstValidateExLessInvInst_rule_idle_inv2.paraRuleInstValidateExLessInvInst)
          then have "invHoldForRule inv r (invariants N) "
            by(cut_tac c2 d2, simp) 
        }moreover
        {assume d1:" exTwoLessP N (%i j.  inv= inv3 i j)"
            from d1 obtain iInv1 and iInv2 
            where d2:"iInv1 \<le> N \<and> iInv2 \<le>N \<and> iInv1 \<noteq>iInv2\<and> inv= inv3 iInv1 iInv2" 
            by (-,unfold exTwoLessP_def,auto)
          have "invHoldForRule (inv3 iInv1 iInv2) (rule_idle iRule) (invariants N) "
            apply(cut_tac  c2 d2)
            by (metis paraRuleInstValidateExTwoLessInvInst_rule_idle_inv3.paraRuleInstValidateExTwoLessInvInst)
          then have "invHoldForRule inv r (invariants N) "
            by(cut_tac c2 d2, simp) 
        }moreover
        {assume d1:" exLessP N (%i .  inv= inv4 i )"
            from d1 obtain iInv1  
            where d2:"iInv1 \<le> N  \<and> inv= inv4 iInv1  " 
            by (-,unfold exLessP_def,auto)
          have "invHoldForRule (inv4 iInv1  ) (rule_idle iRule) (invariants N) "
            apply(cut_tac  c2 d2)
            by (metis paraRuleInstValidateExLessInvInst_rule_idle_inv4.paraRuleInstValidateExLessInvInst)
          then have "invHoldForRule inv r (invariants N) "
            by(cut_tac c2 d2, simp) 
        }moreover
        {assume d1:" exTwoLessP N (%i j.  inv= inv5 i j)"
            from d1 obtain iInv1 and iInv2 
            where d2:"iInv1 \<le> N \<and> iInv2 \<le>N \<and> iInv1 \<noteq>iInv2\<and> inv= inv5 iInv1 iInv2" 
            by (-,unfold exTwoLessP_def,auto)
          have "invHoldForRule (inv5 iInv1 iInv2) (rule_idle iRule) (invariants N) "
            apply(cut_tac  c2 d2)
            by (metis paraRuleInstValidateExTwoLessInvInst_rule_idle_inv5.paraRuleInstValidateExTwoLessInvInst)
          then have "invHoldForRule inv r (invariants N) "
            by(cut_tac c2 d2, simp) 
        }
					
					ultimately have "invHoldForRule inv r (invariants N) "
          by blast
      }
	      moreover
        {assume c1: "exLessP N (%i.  r= rule_try i)
"
         
         from c1 obtain iRule where c2:"iRule \<le> N \<and> r= rule_try iRule" 
         by (auto simp add: exLessP_def)
         
         have c3:"  exTwoLessP N (% i j .  inv= inv1  i j )  \<or> exLessP N (% i .  inv= inv2  i )  \<or> exTwoLessP N (% i j .  inv= inv3  i j )  \<or> exLessP N (% i .  inv= inv4  i )  \<or> exTwoLessP N (% i j .  inv= inv5  i j )     "
          by (cut_tac b1, simp )
          
         moreover
        {assume d1:" exTwoLessP N (%i j.  inv= inv1 i j)"
            from d1 obtain iInv1 and iInv2 
            where d2:"iInv1 \<le> N \<and> iInv2 \<le>N \<and> iInv1 \<noteq>iInv2\<and> inv= inv1 iInv1 iInv2" 
            by (-,unfold exTwoLessP_def,auto)
          have "invHoldForRule (inv1 iInv1 iInv2) (rule_try iRule) (invariants N) "
            apply(cut_tac  c2 d2)
            by (metis paraRuleInstValidateExTwoLessInvInst_rule_try_inv1.paraRuleInstValidateExTwoLessInvInst)
          then have "invHoldForRule inv r (invariants N) "
            by(cut_tac c2 d2, simp) 
        }moreover
        {assume d1:" exLessP N (%i .  inv= inv2 i )"
            from d1 obtain iInv1  
            where d2:"iInv1 \<le> N  \<and> inv= inv2 iInv1  " 
            by (-,unfold exLessP_def,auto)
          have "invHoldForRule (inv2 iInv1  ) (rule_try iRule) (invariants N) "
            apply(cut_tac  c2 d2)
            by (metis paraRuleInstValidateExLessInvInst_rule_try_inv2.paraRuleInstValidateExLessInvInst)
          then have "invHoldForRule inv r (invariants N) "
            by(cut_tac c2 d2, simp) 
        }moreover
        {assume d1:" exTwoLessP N (%i j.  inv= inv3 i j)"
            from d1 obtain iInv1 and iInv2 
            where d2:"iInv1 \<le> N \<and> iInv2 \<le>N \<and> iInv1 \<noteq>iInv2\<and> inv= inv3 iInv1 iInv2" 
            by (-,unfold exTwoLessP_def,auto)
          have "invHoldForRule (inv3 iInv1 iInv2) (rule_try iRule) (invariants N) "
            apply(cut_tac  c2 d2)
            by (metis paraRuleInstValidateExTwoLessInvInst_rule_try_inv3.paraRuleInstValidateExTwoLessInvInst)
          then have "invHoldForRule inv r (invariants N) "
            by(cut_tac c2 d2, simp) 
        }moreover
        {assume d1:" exLessP N (%i .  inv= inv4 i )"
            from d1 obtain iInv1  
            where d2:"iInv1 \<le> N  \<and> inv= inv4 iInv1  " 
            by (-,unfold exLessP_def,auto)
          have "invHoldForRule (inv4 iInv1  ) (rule_try iRule) (invariants N) "
            apply(cut_tac  c2 d2)
            by (metis paraRuleInstValidateExLessInvInst_rule_try_inv4.paraRuleInstValidateExLessInvInst)
          then have "invHoldForRule inv r (invariants N) "
            by(cut_tac c2 d2, simp) 
        }moreover
        {assume d1:" exTwoLessP N (%i j.  inv= inv5 i j)"
            from d1 obtain iInv1 and iInv2 
            where d2:"iInv1 \<le> N \<and> iInv2 \<le>N \<and> iInv1 \<noteq>iInv2\<and> inv= inv5 iInv1 iInv2" 
            by (-,unfold exTwoLessP_def,auto)
          have "invHoldForRule (inv5 iInv1 iInv2) (rule_try iRule) (invariants N) "
            apply(cut_tac  c2 d2)
            by (metis paraRuleInstValidateExTwoLessInvInst_rule_try_inv5.paraRuleInstValidateExTwoLessInvInst)
          then have "invHoldForRule inv r (invariants N) "
            by(cut_tac c2 d2, simp) 
        }
					
					ultimately have "invHoldForRule inv r (invariants N) "
          by blast
      }
	      moreover
        {assume c1: "exLessP N (%i.  r= rule_exit i)
"
         
         from c1 obtain iRule where c2:"iRule \<le> N \<and> r= rule_exit iRule" 
         by (auto simp add: exLessP_def)
         
         have c3:"  exTwoLessP N (% i j .  inv= inv1  i j )  \<or> exLessP N (% i .  inv= inv2  i )  \<or> exTwoLessP N (% i j .  inv= inv3  i j )  \<or> exLessP N (% i .  inv= inv4  i )  \<or> exTwoLessP N (% i j .  inv= inv5  i j )     "
          by (cut_tac b1, simp )
          
         moreover
        {assume d1:" exTwoLessP N (%i j.  inv= inv1 i j)"
            from d1 obtain iInv1 and iInv2 
            where d2:"iInv1 \<le> N \<and> iInv2 \<le>N \<and> iInv1 \<noteq>iInv2\<and> inv= inv1 iInv1 iInv2" 
            by (-,unfold exTwoLessP_def,auto)
          have "invHoldForRule (inv1 iInv1 iInv2) (rule_exit iRule) (invariants N) "
            apply(cut_tac  c2 d2)
            by (metis paraRuleInstValidateExTwoLessInvInst_rule_exit_inv1.paraRuleInstValidateExTwoLessInvInst)
          then have "invHoldForRule inv r (invariants N) "
            by(cut_tac c2 d2, simp) 
        }moreover
        {assume d1:" exLessP N (%i .  inv= inv2 i )"
            from d1 obtain iInv1  
            where d2:"iInv1 \<le> N  \<and> inv= inv2 iInv1  " 
            by (-,unfold exLessP_def,auto)
          have "invHoldForRule (inv2 iInv1  ) (rule_exit iRule) (invariants N) "
            apply(cut_tac  c2 d2)
            by (metis paraRuleInstValidateExLessInvInst_rule_exit_inv2.paraRuleInstValidateExLessInvInst)
          then have "invHoldForRule inv r (invariants N) "
            by(cut_tac c2 d2, simp) 
        }moreover
        {assume d1:" exTwoLessP N (%i j.  inv= inv3 i j)"
            from d1 obtain iInv1 and iInv2 
            where d2:"iInv1 \<le> N \<and> iInv2 \<le>N \<and> iInv1 \<noteq>iInv2\<and> inv= inv3 iInv1 iInv2" 
            by (-,unfold exTwoLessP_def,auto)
          have "invHoldForRule (inv3 iInv1 iInv2) (rule_exit iRule) (invariants N) "
            apply(cut_tac  c2 d2)
            by (metis paraRuleInstValidateExTwoLessInvInst_rule_exit_inv3.paraRuleInstValidateExTwoLessInvInst)
          then have "invHoldForRule inv r (invariants N) "
            by(cut_tac c2 d2, simp) 
        }moreover
        {assume d1:" exLessP N (%i .  inv= inv4 i )"
            from d1 obtain iInv1  
            where d2:"iInv1 \<le> N  \<and> inv= inv4 iInv1  " 
            by (-,unfold exLessP_def,auto)
          have "invHoldForRule (inv4 iInv1  ) (rule_exit iRule) (invariants N) "
            apply(cut_tac  c2 d2)
            by (metis paraRuleInstValidateExLessInvInst_rule_exit_inv4.paraRuleInstValidateExLessInvInst)
          then have "invHoldForRule inv r (invariants N) "
            by(cut_tac c2 d2, simp) 
        }moreover
        {assume d1:" exTwoLessP N (%i j.  inv= inv5 i j)"
            from d1 obtain iInv1 and iInv2 
            where d2:"iInv1 \<le> N \<and> iInv2 \<le>N \<and> iInv1 \<noteq>iInv2\<and> inv= inv5 iInv1 iInv2" 
            by (-,unfold exTwoLessP_def,auto)
          have "invHoldForRule (inv5 iInv1 iInv2) (rule_exit iRule) (invariants N) "
            apply(cut_tac  c2 d2)
            by (metis paraRuleInstValidateExTwoLessInvInst_rule_exit_inv5.paraRuleInstValidateExTwoLessInvInst)
          then have "invHoldForRule inv r (invariants N) "
            by(cut_tac c2 d2, simp) 
        }
					
					ultimately have "invHoldForRule inv r (invariants N) "
          by blast
      }
	      moreover
        {assume c1: "exLessP N (%i.  r= rule_crit i)
"
         
         from c1 obtain iRule where c2:"iRule \<le> N \<and> r= rule_crit iRule" 
         by (auto simp add: exLessP_def)
         
         have c3:"  exTwoLessP N (% i j .  inv= inv1  i j )  \<or> exLessP N (% i .  inv= inv2  i )  \<or> exTwoLessP N (% i j .  inv= inv3  i j )  \<or> exLessP N (% i .  inv= inv4  i )  \<or> exTwoLessP N (% i j .  inv= inv5  i j )     "
          by (cut_tac b1, simp )
          
         moreover
        {assume d1:" exTwoLessP N (%i j.  inv= inv1 i j)"
            from d1 obtain iInv1 and iInv2 
            where d2:"iInv1 \<le> N \<and> iInv2 \<le>N \<and> iInv1 \<noteq>iInv2\<and> inv= inv1 iInv1 iInv2" 
            by (-,unfold exTwoLessP_def,auto)
          have "invHoldForRule (inv1 iInv1 iInv2) (rule_crit iRule) (invariants N) "
            apply(cut_tac  c2 d2)
            by (metis paraRuleInstValidateExTwoLessInvInst_rule_crit_inv1.paraRuleInstValidateExTwoLessInvInst)
          then have "invHoldForRule inv r (invariants N) "
            by(cut_tac c2 d2, simp) 
        }moreover
        {assume d1:" exLessP N (%i .  inv= inv2 i )"
            from d1 obtain iInv1  
            where d2:"iInv1 \<le> N  \<and> inv= inv2 iInv1  " 
            by (-,unfold exLessP_def,auto)
          have "invHoldForRule (inv2 iInv1  ) (rule_crit iRule) (invariants N) "
            apply(cut_tac  c2 d2)
            by (metis paraRuleInstValidateExLessInvInst_rule_crit_inv2.paraRuleInstValidateExLessInvInst)
          then have "invHoldForRule inv r (invariants N) "
            by(cut_tac c2 d2, simp) 
        }moreover
        {assume d1:" exTwoLessP N (%i j.  inv= inv3 i j)"
            from d1 obtain iInv1 and iInv2 
            where d2:"iInv1 \<le> N \<and> iInv2 \<le>N \<and> iInv1 \<noteq>iInv2\<and> inv= inv3 iInv1 iInv2" 
            by (-,unfold exTwoLessP_def,auto)
          have "invHoldForRule (inv3 iInv1 iInv2) (rule_crit iRule) (invariants N) "
            apply(cut_tac  c2 d2)
            by (metis paraRuleInstValidateExTwoLessInvInst_rule_crit_inv3.paraRuleInstValidateExTwoLessInvInst)
          then have "invHoldForRule inv r (invariants N) "
            by(cut_tac c2 d2, simp) 
        }moreover
        {assume d1:" exLessP N (%i .  inv= inv4 i )"
            from d1 obtain iInv1  
            where d2:"iInv1 \<le> N  \<and> inv= inv4 iInv1  " 
            by (-,unfold exLessP_def,auto)
          have "invHoldForRule (inv4 iInv1  ) (rule_crit iRule) (invariants N) "
            apply(cut_tac  c2 d2)
            by (metis paraRuleInstValidateExLessInvInst_rule_crit_inv4.paraRuleInstValidateExLessInvInst)
          then have "invHoldForRule inv r (invariants N) "
            by(cut_tac c2 d2, simp) 
        }moreover
        {assume d1:" exTwoLessP N (%i j.  inv= inv5 i j)"
            from d1 obtain iInv1 and iInv2 
            where d2:"iInv1 \<le> N \<and> iInv2 \<le>N \<and> iInv1 \<noteq>iInv2\<and> inv= inv5 iInv1 iInv2" 
            by (-,unfold exTwoLessP_def,auto)
          have "invHoldForRule (inv5 iInv1 iInv2) (rule_crit iRule) (invariants N) "
            apply(cut_tac  c2 d2)
            by (metis paraRuleInstValidateExTwoLessInvInst_rule_crit_inv5.paraRuleInstValidateExTwoLessInvInst)
          then have "invHoldForRule inv r (invariants N) "
            by(cut_tac c2 d2, simp) 
        }
					
					ultimately have "invHoldForRule inv r (invariants N) "
          by blast
      }
	ultimately show "invHoldForRule inv r (invariants N) "
          by blast 
     qed
qed
next
  show "s \<in> reachableSet {mutualIni N} (rules N)"
by (metis a1)
 
next  
  show " \<forall>inv. inv \<in>invariants N\<longrightarrow> ofImplyForm inv"
  apply(rule allI,rule impI)
  apply(simp,unfold exLessP_def exTwoLessP_def ofImplyForm_def, auto)
  done
qed
end  