theory v4_isar
  imports Main "../QML_S5"
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
assumes compossibilty4: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. ((N x y p k) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. N t z p k)) \<^bold>\<rightarrow> \<^bold>\<diamond>((N x y p k) \<^bold>\<and> (\<^bold>\<exists>x'. (N x' z p k))))\<rfloor>"  
assumes origin_uniqueness4: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<not>\<^bold>\<diamond>((N x y p k) \<^bold>\<and> (N x z p k) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z)))\<rfloor>"
assumes sufficiency4: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<diamond>(N x y p k) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. (N x' y p k) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx)))\<rfloor>"
shows origin_essentialism4: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<diamond>(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (N x y p k)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. \<^bold>\<forall>k'. N x z p' k')))\<rfloor>"

proof (rule allI)
  fix w
  show "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<diamond>(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (N x y p k)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. \<^bold>\<forall>k'. N x z p' k'))) w"
  proof (rule allI)
    fix x
    show "(\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<diamond>(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (N x y p k)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. \<^bold>\<forall>k'. N x z p' k'))) w"
    proof (rule allI)
      fix y
      show "(\<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<diamond>(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (N x y p k)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. \<^bold>\<forall>k'. N x z p' k'))) w"
      proof (rule allI)
        fix z
        show "(\<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<diamond>(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (N x y p k)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. \<^bold>\<forall>k'. N x z p' k'))) w"
        proof (rule allI)
          fix p
          show "(\<^bold>\<forall>k. \<^bold>\<diamond>(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (N x y p k)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. \<^bold>\<forall>k'. N x z p' k'))) w"
          proof (rule allI)
            fix k
            show "(\<^bold>\<diamond>(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (N x y p k)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. \<^bold>\<forall>k. N x z p' k))) w"
            proof (rule impI)
              assume antecedent: "(\<^bold>\<diamond>(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (N x y p k))) w"
              show "(\<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. \<^bold>\<forall>k'. N x z p' k'))) w"
              proof (rule notI)
                assume n_consequent: "(\<^bold>\<diamond>(\<^bold>\<forall>p'. \<^bold>\<forall>k'. N x z p' k')) w"
                from antecedent obtain w where w: "(\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (N x y p k)) w" by (rule exE) 
                then have table_x_from_y: "(N x y p k) w" by (rule conjE)
                have non_overlapping: "(\<^bold>\<not>(y \<^bold>=\<^sup>L z)) w" using antecedent by auto
                then have compossibilty4_ante: "((N x y p k) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. N t z p k)) w"
                  using table_x_from_y and non_overlapping and n_consequent by auto
                from compossibilty4 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. ((N x y p k) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. N t z p k)) \<^bold>\<rightarrow> \<^bold>\<diamond>((N x y p k) \<^bold>\<and> (\<^bold>\<exists>x'. (N x' z p k)))) w"..
                then have "(\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. ((N x y p k) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. N t z p k)) \<^bold>\<rightarrow> \<^bold>\<diamond>((N x y p k) \<^bold>\<and> (\<^bold>\<exists>x'. (N x' z p k)))) w" by (rule allE)
                then have "(\<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. ((N x y p k) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. N t z p k)) \<^bold>\<rightarrow> \<^bold>\<diamond>((N x y p k) \<^bold>\<and> (\<^bold>\<exists>x'. (N x' z p k)))) w" by (rule allE)
                then have "(\<^bold>\<forall>p. \<^bold>\<forall>k. ((N x y p k) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. N t z p k)) \<^bold>\<rightarrow> \<^bold>\<diamond>((N x y p k) \<^bold>\<and> (\<^bold>\<exists>x'. (N x' z p k)))) w" by (rule allE)
                then have "(\<^bold>\<forall>k. ((N x y p k) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. N t z p k)) \<^bold>\<rightarrow> \<^bold>\<diamond>((N x y p k) \<^bold>\<and> (\<^bold>\<exists>x'. (N x' z p k)))) w" by (rule allE)
                then have "(((N x y p k) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. N t z p k)) \<^bold>\<rightarrow> \<^bold>\<diamond>((N x y p k) \<^bold>\<and> (\<^bold>\<exists>x'. (N x' z p k)))) w" by (rule allE)
                then have "(\<^bold>\<diamond>((N x y p k) \<^bold>\<and> (\<^bold>\<exists>x'. (N x' z p k)))) w" using compossibilty4_ante by (rule mp)
                then obtain u where u: "(((N x y p k) \<^bold>\<and> (\<^bold>\<exists>x'. (N x' z p k)))) u" by (rule exE)
                then have "(\<^bold>\<exists>x'. (N x' z p k)) u" by (rule conjE)
                then obtain x' where x': "N x' z p k u" by (rule exE)

                from n_consequent obtain v where v: "(\<^bold>\<forall>p'. \<^bold>\<forall>k'. N x z p' k') v" by (rule exE)
                then have sufficiency4_ante:  "(\<^bold>\<diamond>(N x z p k)) w" by auto

                from sufficiency4 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<diamond>(N x y p k) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. (N x' y p k) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) w"..
                then have  "(\<^bold>\<forall>y. \<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<diamond>(N x y p k) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. (N x' y p k) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) w" by (rule allE)
                then have  "(\<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<diamond>(N x z p k) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. (N x' z p k) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) w" by (rule allE)
                then have  "(\<^bold>\<forall>k. \<^bold>\<diamond>(N x z p k) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. (N x' z p k) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) w" by (rule allE)
                then have  "(\<^bold>\<diamond>(N x z p k) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. (N x' z p k) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) w" by (rule allE)
                then have  "(\<^bold>\<box>(\<^bold>\<forall>x'. (N x' z p k) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) w" using sufficiency4_ante by (rule mp)
                then have "((\<^bold>\<forall>x'. (N x' z p k) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) u" by (rule allE)
                then have "(((N x' z p k) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx))) u" by (rule allE)
                then have "(x'\<^bold>=\<^sup>Lx) u" using `N x' z p k u` by (rule mp)
                      
                then have "(N x z p k) u" using `(N x' z p k) u` by auto
                moreover from u have "(N x y p k) u" by simp 
                then have "(N x y p k) u \<and> (N x z p k) u" using `(N x z p k) u` by (rule conjI)
                then have conj_existence: "(N x y p k \<^bold>\<and> N x z p k) u" by simp 
                then have impossible_arg: "(N x y p k u) \<and> (N x z p k u) \<and> \<not>((y \<^bold>=\<^sup>L z) u)" 
                  using non_overlapping by auto 

                from origin_uniqueness4 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<not>\<^bold>\<diamond>((N x y p k) \<^bold>\<and> (N x z p k) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) w"..
                then have "(\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<not>\<^bold>\<diamond>((N x y p k) \<^bold>\<and> (N x z p k) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) w" by (rule allE)
                then have "(\<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<not>\<^bold>\<diamond>((N x y p k) \<^bold>\<and> (N x z p k) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) w" by (rule allE)
                then have "(\<^bold>\<forall>p. \<^bold>\<forall>k. \<^bold>\<not>\<^bold>\<diamond>((N x y p k) \<^bold>\<and> (N x z p k) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) w" by (rule allE)
                then have "(\<^bold>\<forall>k. \<^bold>\<not>\<^bold>\<diamond>((N x y p k) \<^bold>\<and> (N x z p k) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) w" by (rule allE)
                then have "(\<^bold>\<not>\<^bold>\<diamond>((N x y p k) \<^bold>\<and> (N x z p k) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) w" by (rule allE)
                then have "\<^bold>\<box>(\<^bold>\<not>((N x y p k) \<^bold>\<and> (N x z p k) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) w" by auto
                then have "(\<^bold>\<not>((N x y p k) \<^bold>\<and> (N x z p k) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) u" by (rule allE)
                then show "False" using impossible_arg by (rule notE)
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed
 
end