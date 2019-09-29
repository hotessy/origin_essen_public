(*<*)
theory v2_isar_K
  imports Main "../QML"
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

consts planTable :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" ("P") 
(* (P x y p) \<equiv> x made from y according to p *)

lemma 
assumes compossibilty2: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. (P x y p \<^bold>\<and> y\<^bold>\<noteq>\<^sup>Lz \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p)) \<^bold>\<rightarrow> \<^bold>\<diamond>(P x y p \<^bold>\<and> (\<^bold>\<exists>x'. P x' z p))\<rfloor>"  
assumes origin_uniqueness2: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<not>(\<^bold>\<diamond>(P x y p \<^bold>\<and> P x z p \<^bold>\<and> y\<^bold>\<noteq>\<^sup>Lz))\<rfloor>"
assumes sufficiency2: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>p. \<^bold>\<diamond>(P x y p) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. P x' y p \<^bold>\<rightarrow> x'\<^bold>=\<^sup>Lx)\<rfloor>"
shows origin_essentialism2: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. (y\<^bold>\<noteq>\<^sup>Lz \<^bold>\<and> P x y p) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))\<rfloor>"
  text \<open>\<^item> Setting-up the worlds\<close>
(*<*)
proof (rule allI)
  fix w (* for the outer \<lfloor> \<rfloor> *)
  show "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. ( (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w"
  proof (rule allI)
    fix x (* for table x *)
    show "(\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. ( (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w"
    proof (rule allI)
      fix y (* for material y *)
      show "(\<^bold>\<forall>z. \<^bold>\<forall>p. ( (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w"
      proof (rule allI)
        fix z (* for material z *)
        show "(\<^bold>\<forall>p. ( (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w"
        proof (rule allI)
          fix p (* for plan p *)
          show "(((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w"
(*>*)

          proof (rule impI)
            assume antecedent:  "(y\<^bold>\<noteq>\<^sup>Lz \<^bold>\<and> P x y p) w"
            show  "(\<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w"
            proof (rule notI)
              assume "(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p')) w"
              then have sufficiency2_ante: "(\<^bold>\<diamond>(P x z p)) w" by auto
              then have compossibilty2_ante: "((P x y p) \<^bold>\<and>  (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p)) w" 
                using antecedent by auto 
              from antecedent have non_overlapping: " (y\<^bold>\<noteq>\<^sup>Lz) w" by (rule conjE)
              text\<open>\<^item> Deriving @{text "P x' z p"} in @{term u} using @{term compossibilty2}\<close>
              from compossibilty2 have "((\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. ((P x y p) \<^bold>\<and>  (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p)) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. (P x' z p))))) w"..
(*<*)
              then have "((\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. ((P x y p) \<^bold>\<and>  (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p)) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. (P x' z p))))) w" by (rule allE)
              then have "((\<^bold>\<forall>z. \<^bold>\<forall>p. ((P x y p) \<^bold>\<and>  (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p)) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. (P x' z p))))) w" by (rule allE)
              then have "((\<^bold>\<forall>p. ((P x y p) \<^bold>\<and>  (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p)) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. (P x' z p))))) w" by (rule allE)
              then have "(((P x y p) \<^bold>\<and>  (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p)) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. (P x' z p)))) w" by (rule allE)
(*>*)

              then have "\<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. (P x' z p))) w" 
                using compossibilty2_ante by (rule mp)
              then obtain u where u: "w r u \<and> ((P x y p \<^bold>\<and> (\<^bold>\<exists>x'. P x' z p)) u)" by (rule exE)
              then have "(\<^bold>\<exists>x'. P x' z p) u" by auto
              then obtain x' where x': "P x' z p u" by (rule exE)
              from u have "w r u" by (rule conjE)
              text \<open>\<^item> Deriving @{text "x' \<^bold>=\<^sup>L x"} in @{term u} using @{term sufficiency2}\<close>
              from sufficiency2 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>p. \<^bold>\<diamond>(P x y p) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>t. (P t y p) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx))) w".. 
(*<*)
              then have "(\<^bold>\<forall>y. \<^bold>\<forall>p. \<^bold>\<diamond>(P x y p) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>t. (P t y p) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx))) w" by (rule allE)
              then have "(\<^bold>\<forall>p. \<^bold>\<diamond>(P x z p) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>t. (P t z p) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx))) w" by (rule allE)
              then have "(\<^bold>\<diamond>(P x z p) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>t. (P t z p) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx))) w" by (rule allE)
(*>*)

              then have "(\<^bold>\<box>(\<^bold>\<forall>t. (P t z p) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx))) w" using sufficiency2_ante by (rule mp)
              then have "((P x' z p) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx)) u" using `w r u` by auto
              then have "(x' \<^bold>=\<^sup>L x) u" using `P x' z p u` by (rule mp)
              then have "(P x z p) u" using `(P x' z p) u` by auto 
              text\<open>\<^item> Framing the @{term impossible_arg}\<close>
              from u have "(P x y p) u" by simp 
              then have impossible_arg: "(P x y p \<^bold>\<and> P x z p \<^bold>\<and> ( (y\<^bold>\<noteq>\<^sup>Lz))) u" 
                using non_overlapping and `(P x z p) u`  by auto 
              text\<open>\<^item> Falsifying the @{term impossible_arg} using @{term origin_uniqueness2}\<close>
             from origin_uniqueness2 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<not>(\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and>  (y\<^bold>\<noteq>\<^sup>Lz)))) w"..
(*<*)
             then have "(\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<not>(\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and>  (y\<^bold>\<noteq>\<^sup>Lz)))) w" by (rule allE)
             then have "(\<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<not>(\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and>  (y\<^bold>\<noteq>\<^sup>Lz)))) w" by (rule allE)
             then have "(\<^bold>\<forall>p. \<^bold>\<not>(\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and>  (y\<^bold>\<noteq>\<^sup>Lz)))) w" by (rule allE)
             then have "(\<^bold>\<not>(\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and>  (y\<^bold>\<noteq>\<^sup>Lz)))) w" by (rule allE)
(*>*)

             then have "(\<^bold>\<box>(\<^bold>\<not>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and>  (y\<^bold>\<noteq>\<^sup>Lz)))) w" by auto 
             then have "(\<^bold>\<not>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and>  (y\<^bold>\<noteq>\<^sup>Lz))) u" 
               using `w r u` by auto
             then show "False" using impossible_arg by (rule notE)
(*<*)
            qed
          qed
        qed
      qed
    qed
  qed
qed
(*>*)

end
