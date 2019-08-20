theory v3_isar
  imports Main "../QML_S5"
begin

text \<open>
@{text "Compossibility\<^sub>3'"}: If a table @{term x} is originally made from matter @{term y} and it
is possible for a table to be the only table  originally made from matter @{term z} according to plan @{term p}, 
then it is also possible for table @{term x} to be originally made from matter @{term y} and in 
addition some table or other @{term x'} to be the only table  originally made from matter @{term z} 
according to plan @{term p}.


@{text "Origin Uniqueness\<^sub>1'"}: It is impossible that a single table @{term x} is originally made from 
matter @{term y} and in addition is originally made from matter @{term z}.


@{text "Sufficiency\<^sub>3'"}: If it is possible that a table @{term x'} is the only table originally made from matter @{term z}
according to plan @{term p}, then necessarily any table that is the only table originally made from matter @{term z} 
according to plan @{term p} is the very table @{term x'} and no other.
\<close>


text \<open>
@{text "Origin Essentialism\<^sub>3'"}: If a given table is originally made from certain matter, then it is necessary 
that the given table is not the only table  originally made from any non-overlapping matter according to any plan.
\<close>


consts planTable :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" ("P")

(* (P x y p) \<equiv> x made from y according to p *)
lemma 
assumes compossibilty3: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. ((P x y p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p \<^bold>\<and> (\<^bold>\<forall>t'.(\<^bold>\<not>(t \<^bold>=\<^sup>L t') \<^bold>\<rightarrow> \<^bold>\<not>(P t' z p))))) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. P x' z p \<^bold>\<and> (\<^bold>\<forall>x''.(\<^bold>\<not>(x' \<^bold>=\<^sup>L x'') \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p))))))\<rfloor>" 
assumes sufficiency3: "\<lfloor>(\<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<forall>p. \<^bold>\<diamond>(P x' y p \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x' \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t y p)))) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x. (P x y p \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t y p)))) \<^bold>\<rightarrow> (x\<^bold>=\<^sup>Lx')))\<rfloor>"  
assumes origin_uniqueness3: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<not>\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> \<^bold>\<not>(y\<^bold>=\<^sup>L z)))\<rfloor>" 
shows origin_essentialism3: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<diamond>(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p' \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p'))))))\<rfloor>"

proof (rule allI)
  fix w 
  show "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<diamond>(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p' \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p')))))) w"
  proof (rule allI)
    fix x
    show "(\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<diamond>(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p' \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p')))))) w"
    proof (rule allI)
      fix y 
      show "(\<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<diamond>(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p' \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p')))))) w"
      proof  (rule allI)
        fix z 
        show "(\<^bold>\<forall>p. \<^bold>\<diamond>(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p' \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p')))))) w"
        proof (rule allI)
          fix p 
          show "(\<^bold>\<diamond>(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p' \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p')))))) w"
          proof  (rule impI)
            assume antecedent: "(\<^bold>\<diamond>(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p))) w"
            show  "(\<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p' \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p')))))) w"
            proof  (rule notI)
              assume n_consequent: "(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p' \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p'))))) w"

              from antecedent obtain w where w:  "((\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p))) w" by (rule exE)
              then have non_overlapping: "(\<^bold>\<not>(y \<^bold>=\<^sup>L z)) w" by simp
              have table_x_from_y: "(P x y p) w" using `((\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p))) w` by simp

              from n_consequent have "(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p' \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p'))))) w" by simp
              then obtain v where v: "((\<^bold>\<forall>p'. P x z p' \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p'))))) v" by (rule exE)
              then have "((P x z p \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p))))) v" by (rule allE)
              then have possibility: "(\<^bold>\<diamond>(P x z p \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p))))) w" by (rule exI)

              have compossibilty3_ante: "((P x y p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p \<^bold>\<and> (\<^bold>\<forall>t'.(\<^bold>\<not>(t \<^bold>=\<^sup>L t') \<^bold>\<rightarrow> \<^bold>\<not>(P t' z p))))) w" 
                using non_overlapping and table_x_from_y and possibility by auto

              from compossibilty3 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. ((P x y p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p \<^bold>\<and> (\<^bold>\<forall>t'.(\<^bold>\<not>(t \<^bold>=\<^sup>L t') \<^bold>\<rightarrow> \<^bold>\<not>(P t' z p))))) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. P x' z p \<^bold>\<and> (\<^bold>\<forall>x''.(\<^bold>\<not>(x' \<^bold>=\<^sup>L x'') \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p)))))) w"..
              then have "(\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. ((P x y p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p \<^bold>\<and> (\<^bold>\<forall>t'.(\<^bold>\<not>(t \<^bold>=\<^sup>L t') \<^bold>\<rightarrow> \<^bold>\<not>(P t' z p))))) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. P x' z p \<^bold>\<and> (\<^bold>\<forall>x''.(\<^bold>\<not>(x' \<^bold>=\<^sup>L x'') \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p)))))) w" by (rule allE)
              then have "(\<^bold>\<forall>z. \<^bold>\<forall>p. ((P x y p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p \<^bold>\<and> (\<^bold>\<forall>t'.(\<^bold>\<not>(t \<^bold>=\<^sup>L t') \<^bold>\<rightarrow> \<^bold>\<not>(P t' z p))))) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. P x' z p \<^bold>\<and> (\<^bold>\<forall>x''.(\<^bold>\<not>(x' \<^bold>=\<^sup>L x'') \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p)))))) w" by (rule allE)
              then have "(\<^bold>\<forall>p. ((P x y p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p \<^bold>\<and> (\<^bold>\<forall>t'.(\<^bold>\<not>(t \<^bold>=\<^sup>L t') \<^bold>\<rightarrow> \<^bold>\<not>(P t' z p))))) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. P x' z p \<^bold>\<and> (\<^bold>\<forall>x''.(\<^bold>\<not>(x' \<^bold>=\<^sup>L x'') \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p)))))) w" by (rule allE)
              then have "(((P x y p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p \<^bold>\<and> (\<^bold>\<forall>t'.(\<^bold>\<not>(t \<^bold>=\<^sup>L t') \<^bold>\<rightarrow> \<^bold>\<not>(P t' z p))))) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. P x' z p \<^bold>\<and> (\<^bold>\<forall>x''.(\<^bold>\<not>(x' \<^bold>=\<^sup>L x'') \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p)))))) w" by (rule allE)

              then have "(\<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. P x' z p \<^bold>\<and> (\<^bold>\<forall>x''.(\<^bold>\<not>(x' \<^bold>=\<^sup>L x'') \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p)))))) w" 
                using compossibilty3_ante by (rule mp)
              then obtain u where u: "(((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. P x' z p \<^bold>\<and> (\<^bold>\<forall>x''.(\<^bold>\<not>(x' \<^bold>=\<^sup>L x'') \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p)))))) u" by (rule exE)
              then have "(\<^bold>\<exists>x'. P x' z p \<^bold>\<and> (\<^bold>\<forall>x''.(\<^bold>\<not>(x' \<^bold>=\<^sup>L x'') \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p)))) u" by (rule conjE)
              then obtain x' where x': "((P x' z p) \<^bold>\<and> (\<^bold>\<forall>x''.(\<^bold>\<not>(x' \<^bold>=\<^sup>L x'') \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p)))) u" by (rule exE)
              then have sufficiency3_cons_ante: "((P x' z p) \<^bold>\<and> (\<^bold>\<forall>x''.(\<^bold>\<not>(x' \<^bold>=\<^sup>L x'') \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p)))) u" by simp

              from sufficiency3 have "(\<^bold>\<forall>z. \<^bold>\<forall>x. \<^bold>\<forall>p. \<^bold>\<diamond>(P x z p \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p)))) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. (P x' z p \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x' \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p)))) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) w"..
              then have "(\<^bold>\<forall>x. \<^bold>\<forall>p. \<^bold>\<diamond>(P x z p \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p)))) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. (P x' z p \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x' \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p)))) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) w" by (rule allE)
              then have "(\<^bold>\<forall>p. \<^bold>\<diamond>(P x z p \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p)))) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. (P x' z p \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x' \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p)))) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) w" by (rule allE)
              then have "(\<^bold>\<diamond>(P x z p \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p)))) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. (P x' z p \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x' \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p)))) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) w" by (rule allE)
              then have "(\<^bold>\<box>(\<^bold>\<forall>x'. (P x' z p \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x' \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p)))) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) w" 
                using possibility by auto
              then have "(\<^bold>\<forall>x'. ((P x' z p \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x' \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p)))) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) u" by (rule allE)
              then have "((P x' z p \<^bold>\<and> (\<^bold>\<forall>t.(\<^bold>\<not>(x' \<^bold>=\<^sup>L t) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p)))) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx)) u" by (rule allE)
              then have identity: "(x'\<^bold>=\<^sup>Lx) u" using sufficiency3_cons_ante by (rule mp)

              from sufficiency3_cons_ante have "(P x' z p) u" by auto
              then have "(P x z p) u" using identity by auto
              moreover from u have "(P x y p) u" by auto
              then have conj_existence: "(P x y p \<^bold>\<and> P x z p) u" using `(P x z p) u` by simp 
              then have impossible_arg: "(P x y p u) \<and> (P x z p u) \<and> \<not>((y \<^bold>=\<^sup>L z) u)" 
                using non_overlapping by auto 
              
              
              from origin_uniqueness3 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<not>\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) u"
                 by simp
               then have "(\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p.\<^bold>\<not>\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) u" by (rule allE)
               then have "(\<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<not>\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) u" by (rule allE)
               then have "(\<^bold>\<forall>p. \<^bold>\<not>\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) u" by (rule allE)
               then have "(\<^bold>\<not>\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) u" by (rule allE)
               then have "(\<^bold>\<box>(\<^bold>\<not>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z)))) u" by auto 
               then have "(\<^bold>\<not>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) u" by (rule allE)
               then have "\<not>((P x y p u) \<and> (P x z p u) \<and> \<not>((y \<^bold>=\<^sup>L z) u))" by simp
               then show "False" using impossible_arg by (rule notE)

             qed
           qed
         qed
       qed
     qed
   qed
 qed

end
