(*<*)
theory v2_isar
  imports Main "../QML_S5"
begin
(*>*)

text \<open>
@{text "Compossibility\<^sub>2'"}: If a table @{term x} is originally made from matter @{term y} and it
is possible for a table to be originally made from matter @{term z} according to plan @{term u}, 
then it is also possible for table @{term x} to be originally made from matter @{term y} and in 
addition some table or other @{term x'} to be originally made from matter @{term z} 
according to plan @{term u}.
\<close>


text \<open>
@{text "Origin Uniqueness\<^sub>1'"}: It is impossible that a single table @{term x} is originally made from 
matter @{term y} and in addition is originally made from matter @{term z}.
\<close>

text \<open>
@{text "Sufficiency\<^sub>2'"}: If it is possible that a table @{term x'} is originally made from matter @{term z}
according to plan @{term u}, then necessarily any table originally made from matter @{term z} 
according to plan @{term u} is the very table @{term x'} and no other.
\<close>


text \<open>
@{text "Origin Essentialism\<^sub>2'"}: If a given table is originally made from certain matter, then it is necessary 
that the given table is not originally made from any non-overlapping matter according to any plan.
\<close>

consts makeTable :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" ("T")
consts planTable :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" ("P") (* (P x y p) \<equiv> x made from y according to p *)

abbreviation overlap ::  "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>"  ("O")
  where "O x y \<equiv> x \<^bold>=\<^sup>L y" 

lemma self_identity: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<box>(x \<^bold>=\<^sup>L x) \<rfloor>" by auto
lemma necessity_of_identity: "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<diamond>(x\<^bold>=\<^sup>Ly) \<^bold>\<rightarrow> \<^bold>\<box>(x\<^bold>=\<^sup>Ly))\<rfloor>" by auto
lemma necessity_of_distinctness: "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<not>\<^bold>\<diamond>(x\<^bold>=\<^sup>Ly) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(x\<^bold>=\<^sup>Ly)))\<rfloor>" by auto

lemma 
assumes compossibilty2: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. ((P x y p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p)) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. (P x' z p))))\<rfloor>"  
assumes origin_uniqueness2: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<not>\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z)))\<rfloor>"
assumes sufficiency2: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>p. \<^bold>\<diamond>(P x y p) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. (P x' y p) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx)))\<rfloor>"
shows origin_essentialism2: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. (\<^bold>\<diamond>(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p))) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p')))\<rfloor>"
proof (rule allI)
  fix w (* for the outer \<lfloor> \<rfloor> *)
  show "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<diamond>(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w"
  proof (rule allI)
    fix x (* for table x *)
    show "(\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<diamond>(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w"
    proof (rule allI)
      fix y (* for material y *)
      show "(\<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<diamond>(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w"
      proof (rule allI)
        fix z (* for material z *)
        show "(\<^bold>\<forall>p. \<^bold>\<diamond>(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w"
        proof (rule allI)
          fix p (* for plan p *)
          show "(\<^bold>\<diamond>(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w"
          proof (rule impI)
            assume antecedent:  "(\<^bold>\<diamond>(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p))) w"
            show  "(\<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w"
              proof (rule notI)
                assume "((\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w"
                from antecedent obtain w where w: "((\<^bold>\<not>(y \<^bold>=\<^sup>L z)) \<^bold>\<and> (P x y p)) w" 
                  by (rule exE) (* Expanding \<diamond> in the same world *)
                then have non_overlapping: "\<not>(y \<^bold>=\<^sup>L z) w" by (rule conjE)
                have table_x_from_y: "(P x y p w)" 
                  using `((\<^bold>\<not>(y \<^bold>=\<^sup>L z)) \<^bold>\<and> (P x y p)) w` by (rule conjE)
                have compossibilty2_ante: "((P x y p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p)) w" 
                  using table_x_from_y and `((\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w` and non_overlapping by auto 

                have "((\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w" using `((\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w` by simp
                then obtain v where v: "((\<^bold>\<forall>p'. P x z p')) v" by (rule exE)
                then have sufficiency2_ante: "(\<^bold>\<diamond>(P x z p)) w" by auto

                from compossibilty2 have "((\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. ((P x y p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p)) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. (P x' z p))))) w"..
                then have "((\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. ((P x y p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p)) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. (P x' z p))))) w" by (rule allE)
                then have "((\<^bold>\<forall>z. \<^bold>\<forall>p. ((P x y p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p)) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. (P x' z p))))) w" by (rule allE)
                then have "((\<^bold>\<forall>p. ((P x y p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p)) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. (P x' z p))))) w" by (rule allE)
                then have "(((P x y p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p)) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. (P x' z p)))) w" by (rule allE)
                then have "\<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. (P x' z p))) w" using compossibilty2_ante by (rule mp)
                then obtain u where u: "(P x y p u  \<and> (\<exists>x'. P x' z p u)) " by (rule exE)
                then have "(\<exists>x'. P x' z p u)" by (rule conjE)
                then obtain x' where x': "P x' z p u" by (rule exE)
  
                from sufficiency2 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>p. \<^bold>\<diamond>(P x y p) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>t. (P t y p) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx))) w".. 
                then have "(\<^bold>\<forall>y. \<^bold>\<forall>p. \<^bold>\<diamond>(P x y p) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>t. (P t y p) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx))) w" by (rule allE)
                then have "(\<^bold>\<forall>p. \<^bold>\<diamond>(P x z p) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>t. (P t z p) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx))) w" by (rule allE)
                then have "(\<^bold>\<diamond>(P x z p) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>t. (P t z p) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx))) w" by (rule allE)
                then have "(\<^bold>\<box>(\<^bold>\<forall>t. (P t z p) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx))) w" using sufficiency2_ante by (rule mp)
                then have "(\<^bold>\<forall>t. (P t z p) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx)) u" by (rule allE)
                then have "((P x' z p) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx)) u" by (rule allE)
                then have "(x' \<^bold>=\<^sup>L x) u" using `P x' z p u` by (rule mp)
                then have "(P x z p) u" using `(P x' z p) u` by auto 
                moreover from u have "(P x y p) u" by simp 
                then have "(P x y p) u \<and> (P x z p) u" using `(P x z p) u` by (rule conjI)
                then have conj_existence: "(P x y p \<^bold>\<and> P x z p) u" by simp 
                then have impossible_arg: "(P x y p u) \<and> (P x z p u) \<and> \<not>((y \<^bold>=\<^sup>L z) u)" 
                  using non_overlapping by auto 
  
               from origin_uniqueness2 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<not>\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) u"
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

(*<*)
end
(*>*)
