theory v4_isar_K
  imports Main "../QML"
begin

text \<open>
@{text "Compossibility\<^sub>4'"}: If a table @{term x} is originally made from matter @{term y} and it
is possible for a table to be the @{text "n\<^sup>t\<^sup>h"} table originally made from matter @{term z} according to plan @{term p}, 
then it is also possible for table @{term x} to be originally made from matter @{term y} and in 
addition some table or other @{term x'} to be the @{text "n\<^sup>t\<^sup>h"} table originally made from matter @{term z} 
according to plan @{term p}.



@{text "Origin Uniqueness\<^sub>4'"}: It is impossible that a single table @{term x} is originally made from 
matter @{term y} and in addition is originally made from matter @{term z}.


@{text "Sufficiency\<^sub>4'"}: If it is possible that a table @{term x'} is the @{text "n\<^sup>t\<^sup>h"} table originally made from matter @{term z}
according to plan @{term p}, then necessarily any table that is the @{text "n\<^sup>t\<^sup>h"} table originally made from matter @{term z} 
according to plan @{term p} is the very table @{term x'} and no other.
\<close>


text \<open>
@{text "Origin Essentialism\<^sub>4'"}: If a given table is originally made from certain matter, then it is necessary 
that the given table is not (the @{text "n\<^sup>t\<^sup>h"} table for any @{term n}) originally made from any non-overlapping 
matter according to any plan.
\<close>


consts kTable :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<mu> \<Rightarrow> nat \<Rightarrow> \<sigma>" ("N")
(* (N x y p k) \<equiv> x is the kth table made from y according to p *)

lemma 
assumes compossibilty4: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. (N x y p k \<^bold>\<and> y\<^bold>\<noteq>\<^sup>Lz \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. N t z p k)) \<^bold>\<rightarrow> \<^bold>\<diamond>(N x y p k \<^bold>\<and> (\<^bold>\<exists>x'. N x' z p k))\<rfloor>"  
assumes origin_uniqueness4: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<not>(\<^bold>\<diamond>(N x y p k \<^bold>\<and> N x z p k \<^bold>\<and> y\<^bold>\<noteq>\<^sup>Lz))\<rfloor>"
assumes sufficiency4: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<diamond>(N x y p k) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. N x' y p k \<^bold>\<rightarrow> x'\<^bold>=\<^sup>Lx)\<rfloor>"
shows origin_essentialism4: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. (y\<^bold>\<noteq>\<^sup>Lz \<^bold>\<and> N x y p k) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. \<^bold>\<forall>k'. N x z p' k'))\<rfloor>"
  text \<open>\<^item> Setting-up the worlds\<close>
(*<*)
proof (rule allI)
  fix w
  show "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. ((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (N x y p k)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. \<^bold>\<forall>k'. N x z p' k'))) w"
  proof (rule allI)
    fix x
    show "(\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. ((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (N x y p k)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. \<^bold>\<forall>k'. N x z p' k'))) w"
    proof (rule allI)
      fix y
      show "(\<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. ((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (N x y p k)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. \<^bold>\<forall>k'. N x z p' k'))) w"
      proof (rule allI)
        fix z
        show "(\<^bold>\<forall>p. \<^bold>\<forall>k. ((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (N x y p k)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. \<^bold>\<forall>k'. N x z p' k'))) w"
        proof (rule allI)
          fix p
          show "(\<^bold>\<forall>k. ((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (N x y p k)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. \<^bold>\<forall>k'. N x z p' k'))) w"
          proof (rule allI)
            fix k
            show "(((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (N x y p k)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. \<^bold>\<forall>k. N x z p' k))) w"
(*>*)

            proof (rule impI)
              assume antecedent: "(y\<^bold>\<noteq>\<^sup>Lz \<^bold>\<and> N x y p k) w"
              show "\<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. \<^bold>\<forall>k'. N x z p' k')) w"
              proof (rule notI)
                assume  "\<^bold>\<diamond>(\<^bold>\<forall>p'. \<^bold>\<forall>k'. N x z p' k') w"
                then have sufficiency4_ante: "\<^bold>\<diamond>(N x z p k) w" by auto
                then have compossibilty4_ante: "(N x y p k \<^bold>\<and> y\<^bold>\<noteq>\<^sup>Lz \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. N t z p k)) w"
                  using antecedent by auto
                from antecedent have non_overlapping: "(y\<^bold>\<noteq>\<^sup>Lz) w" by (rule conjE)
                text\<open>\<^item> Deriving @{text "N x' z p k"} in @{term u} using @{term compossibilty4}\<close>
                from compossibilty4 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. (N x y p k \<^bold>\<and> y\<^bold>\<noteq>\<^sup>Lz \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. N t z p k)) \<^bold>\<rightarrow> \<^bold>\<diamond>(N x y p k \<^bold>\<and> (\<^bold>\<exists>x'. N x' z p k))) w"..
(*<*)
                then have "(\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. ((N x y p k) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. N t z p k)) \<^bold>\<rightarrow> \<^bold>\<diamond>((N x y p k) \<^bold>\<and> (\<^bold>\<exists>x'. (N x' z p k)))) w" by (rule allE)
                then have "(\<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. ((N x y p k) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. N t z p k)) \<^bold>\<rightarrow> \<^bold>\<diamond>((N x y p k) \<^bold>\<and> (\<^bold>\<exists>x'. (N x' z p k)))) w" by (rule allE)
                then have "(\<^bold>\<forall>p. \<^bold>\<forall>k. ((N x y p k) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. N t z p k)) \<^bold>\<rightarrow> \<^bold>\<diamond>((N x y p k) \<^bold>\<and> (\<^bold>\<exists>x'. (N x' z p k)))) w" by (rule allE)
                then have "(\<^bold>\<forall>k. ((N x y p k) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. N t z p k)) \<^bold>\<rightarrow> \<^bold>\<diamond>((N x y p k) \<^bold>\<and> (\<^bold>\<exists>x'. (N x' z p k)))) w" by (rule allE)
                then have "(((N x y p k) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. N t z p k)) \<^bold>\<rightarrow> \<^bold>\<diamond>((N x y p k) \<^bold>\<and> (\<^bold>\<exists>x'. (N x' z p k)))) w" by (rule allE)
(*>*)

                then have "\<^bold>\<diamond>(N x y p k \<^bold>\<and> (\<^bold>\<exists>x'. N x' z p k)) w" 
                  using compossibilty4_ante by (rule mp)
                then obtain u where u: "w r u \<and> ((N x y p k \<^bold>\<and> (\<^bold>\<exists>x'. N x' z p k))  u)" by (rule exE)
                then have "(\<^bold>\<exists>x'. N x' z p k) u" by auto
                then obtain x' where x': "(N x' z p k) u" by (rule exE)
                from u have "w r u" by (rule conjE)
                text \<open>\<^item> Deriving @{text "x' \<^bold>=\<^sup>L x"} in @{term u} using @{term sufficiency4}\<close>
                from sufficiency4 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<diamond>(N x y p k) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. N x' y p k \<^bold>\<rightarrow> x'\<^bold>=\<^sup>Lx)) w"..
(*<*)
                then have "(\<^bold>\<forall>y. \<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<diamond>(N x y p k) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. (N x' y p k) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) w" by (rule allE)
                then have "(\<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<diamond>(N x z p k) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. (N x' z p k) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) w" by (rule allE)
                then have "(\<^bold>\<forall>k. \<^bold>\<diamond>(N x z p k) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. (N x' z p k) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) w" by (rule allE)
                then have "(\<^bold>\<diamond>(N x z p k) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. (N x' z p k) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) w" by (rule allE)
(*>*)

                then have "\<^bold>\<box>(\<^bold>\<forall>x'. N x' z p k \<^bold>\<rightarrow> x'\<^bold>=\<^sup>Lx) w" using sufficiency4_ante by (rule mp)
                then have "(N x' z p k \<^bold>\<rightarrow> x'\<^bold>=\<^sup>Lx) u" using `w r u` by auto
                then have "(x'\<^bold>=\<^sup>Lx) u" using `N x' z p k u` by (rule mp)
                then have "(N x z p k) u" using `(N x' z p k) u` by auto
                text\<open>\<^item> Framing the @{term impossible_arg}\<close>
                from u have "(N x y p k) u" by simp 
                then have impossible_arg: "(N x y p k \<^bold>\<and> N x z p k \<^bold>\<and> y\<^bold>\<noteq>\<^sup>Lz) u" 
                  using `(N x z p k) u` and non_overlapping by auto 
                text\<open>\<^item> Falsifying the @{term impossible_arg} using @{term origin_uniqueness4}\<close>
                from origin_uniqueness4 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<not>(\<^bold>\<diamond>(N x y p k \<^bold>\<and> N x z p k \<^bold>\<and> y\<^bold>\<noteq>\<^sup>Lz))) w"..
(*<*)
                then have "(\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<not>(\<^bold>\<diamond>((N x y p k) \<^bold>\<and> (N x z p k) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz)))) w" by (rule allE)
                then have "(\<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<not>(\<^bold>\<diamond>((N x y p k) \<^bold>\<and> (N x z p k) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz)))) w" by (rule allE)
                then have "(\<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<not>(\<^bold>\<diamond>((N x y p k) \<^bold>\<and> (N x z p k) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz)))) w" by (rule allE)
                then have "(\<^bold>\<forall>k. \<^bold>\<not>(\<^bold>\<diamond>((N x y p k) \<^bold>\<and> (N x z p k) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz)))) w" by (rule allE)
                then have "(\<^bold>\<not>(\<^bold>\<diamond>((N x y p k) \<^bold>\<and> (N x z p k) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz)))) w" by (rule allE)
(*>*)

                then have "\<^bold>\<box>(\<^bold>\<not>(N x y p k \<^bold>\<and> N x z p k \<^bold>\<and> y\<^bold>\<noteq>\<^sup>Lz)) w" by auto
                then have "\<^bold>\<not>(N x y p k \<^bold>\<and> N x z p k \<^bold>\<and> y\<^bold>\<noteq>\<^sup>Lz) u"
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
qed
(*>*)
 
end