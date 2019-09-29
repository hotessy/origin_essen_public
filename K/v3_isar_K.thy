theory v3_isar_K
  imports Main "../QML"
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
assumes compossibilty3: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. (P x y p \<^bold>\<and> y\<^bold>\<noteq>\<^sup>Lz \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p \<^bold>\<and> (\<^bold>\<forall>t'. t\<^bold>\<noteq>\<^sup>Lt' \<^bold>\<rightarrow> \<^bold>\<not>(P t' z p)))) \<^bold>\<rightarrow> \<^bold>\<diamond>(P x y p \<^bold>\<and> (\<^bold>\<exists>x'. P x' z p \<^bold>\<and> (\<^bold>\<forall>x''.(x'\<^bold>\<noteq>\<^sup>Lx'' \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p)))))\<rfloor>" 
assumes sufficiency3: "\<lfloor>\<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<forall>p. \<^bold>\<diamond>(P x' y p \<^bold>\<and> (\<^bold>\<forall>t.(x'\<^bold>\<noteq>\<^sup>Lt \<^bold>\<rightarrow> \<^bold>\<not>(P t y p)))) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x. (P x y p \<^bold>\<and> (\<^bold>\<forall>t. x\<^bold>\<noteq>\<^sup>Lt \<^bold>\<rightarrow> \<^bold>\<not>(P t y p))) \<^bold>\<rightarrow> x\<^bold>=\<^sup>Lx')\<rfloor>"  
assumes origin_uniqueness3: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<not>(\<^bold>\<diamond>(P x y p \<^bold>\<and> P x z p \<^bold>\<and> y\<^bold>\<noteq>\<^sup>Lz))\<rfloor>" 
shows origin_essentialism3: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. (y\<^bold>\<noteq>\<^sup>Lz \<^bold>\<and> P x y p) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p' \<^bold>\<and> (\<^bold>\<forall>t. x\<^bold>\<noteq>\<^sup>Lt \<^bold>\<rightarrow> \<^bold>\<not>(P t z p'))))\<rfloor>"
  text \<open>\<^item> Setting-up the worlds\<close>
(*<*)
proof (rule allI)
  fix w 
  show "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. ((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p' \<^bold>\<and> (\<^bold>\<forall>t.((x\<^bold>\<noteq>\<^sup>Lt) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p')))))) w"
  proof (rule allI)
    fix x
    show "(\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. ((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p' \<^bold>\<and> (\<^bold>\<forall>t.((x\<^bold>\<noteq>\<^sup>Lt) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p')))))) w"
    proof (rule allI)
      fix y 
      show "(\<^bold>\<forall>z. \<^bold>\<forall>p. ((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p' \<^bold>\<and> (\<^bold>\<forall>t.((x\<^bold>\<noteq>\<^sup>Lt) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p')))))) w"
      proof  (rule allI)
        fix z 
        show "(\<^bold>\<forall>p. ((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p' \<^bold>\<and> (\<^bold>\<forall>t.((x\<^bold>\<noteq>\<^sup>Lt) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p')))))) w"
        proof (rule allI)
          fix p 
          show "(((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p' \<^bold>\<and> (\<^bold>\<forall>t.((x\<^bold>\<noteq>\<^sup>Lt) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p')))))) w"
(*>*)

          proof  (rule impI)
            assume antecedent: "(((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (P x y p))) w"
            show "(\<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p' \<^bold>\<and> (\<^bold>\<forall>t.((x\<^bold>\<noteq>\<^sup>Lt) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p')))))) w"
            proof (rule notI)
              assume "(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p' \<^bold>\<and> (\<^bold>\<forall>t.((x\<^bold>\<noteq>\<^sup>Lt) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p'))))) w"
              then have sufficiency3_ante: "(\<^bold>\<diamond>(P x z p \<^bold>\<and> (\<^bold>\<forall>t.((x\<^bold>\<noteq>\<^sup>Lt) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p))))) w" 
                by auto 
              then have compossibilty3_ante: "((P x y p) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p \<^bold>\<and> (\<^bold>\<forall>t'.((t\<^bold>\<noteq>\<^sup>Lt') \<^bold>\<rightarrow> \<^bold>\<not>(P t' z p))))) w" 
                using antecedent by auto
              from antecedent have non_overlapping: "(y\<^bold>\<noteq>\<^sup>Lz) w" by (rule conjE)
              text\<open>\<^item> Deriving @{text "P x' z p"} in @{term u} using @{term compossibilty3}\<close>
              from compossibilty3 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. ((P x y p) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p \<^bold>\<and> (\<^bold>\<forall>t'.((t\<^bold>\<noteq>\<^sup>Lt') \<^bold>\<rightarrow> \<^bold>\<not>(P t' z p))))) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. P x' z p \<^bold>\<and> (\<^bold>\<forall>x''.((x'\<^bold>\<noteq>\<^sup>Lx'') \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p)))))) w"..
(*<*)
              then have "(\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. ((P x y p) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p \<^bold>\<and> (\<^bold>\<forall>t'.((t\<^bold>\<noteq>\<^sup>Lt') \<^bold>\<rightarrow> \<^bold>\<not>(P t' z p))))) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. P x' z p \<^bold>\<and> (\<^bold>\<forall>x''.((x'\<^bold>\<noteq>\<^sup>Lx'') \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p)))))) w" by (rule allE)
              then have "(\<^bold>\<forall>z. \<^bold>\<forall>p. ((P x y p) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p \<^bold>\<and> (\<^bold>\<forall>t'.((t\<^bold>\<noteq>\<^sup>Lt') \<^bold>\<rightarrow> \<^bold>\<not>(P t' z p))))) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. P x' z p \<^bold>\<and> (\<^bold>\<forall>x''.((x'\<^bold>\<noteq>\<^sup>Lx'') \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p)))))) w" by (rule allE)
              then have "(\<^bold>\<forall>p. ((P x y p) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p \<^bold>\<and> (\<^bold>\<forall>t'.((t\<^bold>\<noteq>\<^sup>Lt') \<^bold>\<rightarrow> \<^bold>\<not>(P t' z p))))) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. P x' z p \<^bold>\<and> (\<^bold>\<forall>x''.((x'\<^bold>\<noteq>\<^sup>Lx'') \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p)))))) w" by (rule allE)
              then have "(((P x y p) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p \<^bold>\<and> (\<^bold>\<forall>t'.((t\<^bold>\<noteq>\<^sup>Lt') \<^bold>\<rightarrow> \<^bold>\<not>(P t' z p))))) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. P x' z p \<^bold>\<and> (\<^bold>\<forall>x''.((x'\<^bold>\<noteq>\<^sup>Lx'') \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p)))))) w" by (rule allE)
(*>*)

              then have "(\<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. P x' z p \<^bold>\<and> (\<^bold>\<forall>x''.((x'\<^bold>\<noteq>\<^sup>Lx'') \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p)))))) w" 
                using compossibilty3_ante by (rule mp)
              then obtain u where u: "(w r u) \<and> ((((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. P x' z p \<^bold>\<and> (\<^bold>\<forall>x''.((x'\<^bold>\<noteq>\<^sup>Lx'') \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p)))))) u)" by (rule exE)
              then have "((((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. P x' z p \<^bold>\<and> (\<^bold>\<forall>x''.((x'\<^bold>\<noteq>\<^sup>Lx'') \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p)))))) u)" by (rule conjE)
              then have "(\<^bold>\<exists>x'. P x' z p \<^bold>\<and> (\<^bold>\<forall>x''.((x'\<^bold>\<noteq>\<^sup>Lx'') \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p)))) u" by (rule conjE)
              then obtain x' where x': "((P x' z p) \<^bold>\<and> (\<^bold>\<forall>x''.((x'\<^bold>\<noteq>\<^sup>Lx'') \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p)))) u" by (rule exE)
              then have sufficiency3_cons_ante: "((P x' z p) \<^bold>\<and> (\<^bold>\<forall>x''.((x'\<^bold>\<noteq>\<^sup>Lx'') \<^bold>\<rightarrow> \<^bold>\<not>(P x'' z p)))) u" by simp
              then have "P x' z p u" by (rule conjE)
              from u have "(w r u)" by (rule conjE)
              text \<open>\<^item> Deriving @{text "x' \<^bold>=\<^sup>L x"} in @{term u} using @{term sufficiency3}\<close>
              from sufficiency3 have "(\<^bold>\<forall>z. \<^bold>\<forall>x. \<^bold>\<forall>p. \<^bold>\<diamond>(P x z p \<^bold>\<and> (\<^bold>\<forall>t.((x\<^bold>\<noteq>\<^sup>Lt) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p)))) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. (P x' z p \<^bold>\<and> (\<^bold>\<forall>t.((x'\<^bold>\<noteq>\<^sup>Lt) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p)))) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) w"..
(*<*)
              then have "(\<^bold>\<forall>x. \<^bold>\<forall>p. \<^bold>\<diamond>(P x z p \<^bold>\<and> (\<^bold>\<forall>t.((x\<^bold>\<noteq>\<^sup>Lt) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p)))) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. (P x' z p \<^bold>\<and> (\<^bold>\<forall>t.((x'\<^bold>\<noteq>\<^sup>Lt) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p)))) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) w" by (rule allE)
              then have "(\<^bold>\<forall>p. \<^bold>\<diamond>(P x z p \<^bold>\<and> (\<^bold>\<forall>t.((x\<^bold>\<noteq>\<^sup>Lt) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p)))) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. (P x' z p \<^bold>\<and> (\<^bold>\<forall>t.((x'\<^bold>\<noteq>\<^sup>Lt) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p)))) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) w" by (rule allE)
              then have "(\<^bold>\<diamond>(P x z p \<^bold>\<and> (\<^bold>\<forall>t.((x\<^bold>\<noteq>\<^sup>Lt) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p)))) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. (P x' z p \<^bold>\<and> (\<^bold>\<forall>t.((x'\<^bold>\<noteq>\<^sup>Lt) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p)))) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) w" by (rule allE)
(*>*)

              then have "(\<^bold>\<box>(\<^bold>\<forall>x'. (P x' z p \<^bold>\<and> (\<^bold>\<forall>t.((x'\<^bold>\<noteq>\<^sup>Lt) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p)))) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) w" 
                using sufficiency3_ante by (rule mp)
              then have "((P x' z p \<^bold>\<and> (\<^bold>\<forall>t.((x'\<^bold>\<noteq>\<^sup>Lt) \<^bold>\<rightarrow> \<^bold>\<not>(P t z p)))) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx)) u" 
                using `w r u` by auto
              then have "(x'\<^bold>=\<^sup>Lx) u" using sufficiency3_cons_ante by (rule mp)
              then have "(P x z p) u" using `P x' z p u` by auto
              text\<open>\<^item> Framing the @{term impossible_arg}\<close>
              from u have "(P x y p) u" by auto
              then have impossible_arg: "(P x y p \<^bold>\<and> P x z p \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz)) u" 
                using non_overlapping and `(P x z p) u` by auto 
              text\<open>\<^item> Falsifying the @{term impossible_arg} using @{term origin_uniqueness3}\<close>
              from origin_uniqueness3 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<not>(\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz)))) w"..
(*<*)
              then have "(\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p.\<^bold>\<not>(\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz)))) w" by (rule allE)
              then have "(\<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<not>(\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz)))) w" by (rule allE)
              then have "(\<^bold>\<forall>p. \<^bold>\<not>(\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz)))) w" by (rule allE)
              then have "(\<^bold>\<not>(\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz)))) w" by (rule allE)
(*>*)

              then have "(\<^bold>\<box>(\<^bold>\<not>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz)))) w" by auto 
              then have "(\<^bold>\<not>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz))) u" using `w r u` by auto
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
