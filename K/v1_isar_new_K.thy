theory v1_isar_new_K
  imports Main "../QML"
begin

text \<open>
@{text "Compossibility\<^sub>6'"}: Necessarily, given a table,  @{term x}, made from a hunk, @{term y}, 
for any table, @{term x'} which might be made from a hunk, @{term z}, distinct from @{term y}, it 
is also possible that both @{term x} is a table made from @{term y} and @{term x'} is a table made 
from @{term z}.


@{text "Origin Uniqueness\<^sub>6'"}:
Necessarily, if  @{term x} is a table made from  @{term y} and  @{term x'} is a table made
from  @{term z} and @{text "y\<noteq>z"}, then @{text "x\<noteq>x'"}.
\<close>

text \<open>
@{text "Origin Essentialism\<^sub>6'"}: Necessarily, given a table, @{term x}, made from a hunk, @{term y}, any table, @{term x'}, 
which might be made from a hunk, @{term z}, distinct from @{term y}, is distinct from @{term x}.
\<close>

subsection \<open>Our Formulation\<close>

text \<open>
We paraphrased the arguments mentioned above to a more logically readable form, without distorting 
their essence. 
\<close>

text \<open>
@{text "Compossibility\<^sub>6"}: If any table, say @{term x}, is made from any hunk of matter, say @{term y}, 
then necessarily if any table, say @{term x'}, is made from any hunk of matter, say @{term z}, 
such that @{term y} and @{term z} are distinct, then it is possible that both tables @{term x} (made from @{term y}) 
and @{term x'} (made from @{term z}) exist together.

@{text "Origin Uniqueness\<^sub>6"}:
If any table, say @{term x}, is made from any hunk of matter, say @{term y}, and any table, 
say @{term x'}, is made from any hunk of matter, say @{term z}, such that @{term y} and @{term z} are distinct, 
then @{term x} and @{term x'} are distinct.
\<close>

text \<open>
@{text "Origin Essentialism\<^sub>6"}: If any table, say @{term x}, is made from any hunk of matter, say @{term y}, 
then necessarily if any table, say @{term x'}, is made from any hunk of matter, say @{term z}, 
such that @{term y} and @{term z} are distinct, then @{term x} and @{term x'} are distinct
\<close>




text \<open> We will using this version henceforth.\<close>


subsection \<open>Overview of the Proof\<close>

text \<open>

\begin{enumerate}

\item Setting-up the worlds:
We begin in world @{term w} by assuming the antecedent of the thesis @{text "Origin Essentialism\<^sub>6"} 
@{text "table_x1_from_y1: T x y w"}. On expanding the necessity operator in its consequent, 
we obtain @{text "antecedent: (((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> T x' z) v"} i.e. @{term y} 
and @{term z} are distinct and table @{term x'} can be made from @{term z} in @{term v} are both true.
We fix all the variables of universal quantifiers to maintain uniformity of meaning.
We assume the negation of the consequent in a world @{term v} i.e. tables @{term x} and  @{term x'} are 
identical, @{text "identity: (x\<^bold>=\<^sup>Lx') v"}. 


\item Deriving co-existence of tables @{term x} and @{term x'} in @{term u}:
We use @{text "Compossibility\<^sub>6"} to show that tables @{term x} and @{term x'} co-exist in a world.
We derive the  @{text "Compossibility\<^sub>6 Consequent"} in @{term u} using @{term antecedent}. Using this
we obtain @{text "Origin Uniqueness\<^sub>6 Antecedent"} 
@{text "origin_uniqueness1_ante: (((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (T x y) \<^bold>\<and> (T x' z))) u"}.


\item Falsifying @{term identity}:
We obtain @{text "Origin Uniqueness\<^sub>6 Consequent"} @{text "((x\<^bold>\<noteq>\<^sup>Lx')) u"} using previously derived 
@{term origin_uniqueness1_ante}. We use this obtained result to falsify @{term identity}.

\end{enumerate}
\<close>



(* (T x y) \<equiv> x made from y *)
consts makeTable ::  "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>"  ("T") 
(* lemma necessity_of_distinctness: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y.(\<^bold>\<not>(x\<^bold>=\<^sup>Ly) \<^bold>\<rightarrow> \<^bold>\<box>((x\<^bold>\<noteq>\<^sup>Ly)))\<rfloor>" by auto *)

lemma 
  assumes compossibilty6: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<forall>z. T x y \<^bold>\<rightarrow> \<^bold>\<box>((y\<^bold>\<noteq>\<^sup>Lz \<^bold>\<and> T x' z) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x y \<^bold>\<and> T x' z))\<rfloor>"
  assumes origin_uniqueness6: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<forall>z. (y\<^bold>\<noteq>\<^sup>Lz \<^bold>\<and> T x y \<^bold>\<and> T x' z) \<^bold>\<rightarrow> x\<^bold>\<noteq>\<^sup>Lx'\<rfloor>" 
  shows origin_essentialism6: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<forall>z. T x y \<^bold>\<rightarrow> \<^bold>\<box>((y\<^bold>\<noteq>\<^sup>Lz \<^bold>\<and> T x' z) \<^bold>\<rightarrow> x\<^bold>\<noteq>\<^sup>Lx')\<rfloor>"
  text \<open>\<^item> Setting-up the worlds\<close>
(*<*)
proof(rule allI)
  fix w
  show "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<forall>z. T x y \<^bold>\<rightarrow> \<^bold>\<box>(((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> (x\<^bold>\<noteq>\<^sup>Lx'))) w" 
  proof(rule allI)
    fix x
    show "(\<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<forall>z. T x y \<^bold>\<rightarrow> \<^bold>\<box>(((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> (x\<^bold>\<noteq>\<^sup>Lx'))) w" 
    proof(rule allI)
      fix y
      show  "(\<^bold>\<forall>x'. \<^bold>\<forall>z. T x y \<^bold>\<rightarrow> \<^bold>\<box>(((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> (x\<^bold>\<noteq>\<^sup>Lx'))) w" 
      proof(rule allI)
        fix x'
        show  "(\<^bold>\<forall>z. T x y \<^bold>\<rightarrow> \<^bold>\<box>(((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> (x\<^bold>\<noteq>\<^sup>Lx'))) w" 
        proof(rule allI)
          fix z
          show  "(T x y \<^bold>\<rightarrow> \<^bold>\<box>(((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> (x\<^bold>\<noteq>\<^sup>Lx'))) w"
(*>*)
          proof(rule impI)
            assume table_x1_from_y1: "T x y w"
            show  "(\<^bold>\<box>(((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> (x\<^bold>\<noteq>\<^sup>Lx'))) w"
            proof(rule allI)
              fix v
              show  "(w r v) \<longrightarrow> (((((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> (x\<^bold>\<noteq>\<^sup>Lx'))) v)"
              proof (rule impI)
                assume "w r v"
                show "(((((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> (x\<^bold>\<noteq>\<^sup>Lx'))) v)"
                proof(rule impI)
                  assume antecedent: "(y\<^bold>\<noteq>\<^sup>Lz \<^bold>\<and> T x' z) v"
                  show "((x\<^bold>\<noteq>\<^sup>Lx')) v"
                  proof(rule notI)
                    assume identity: "(x\<^bold>=\<^sup>Lx') v"
                    from antecedent have table_x2_from_y2: "(T x' z) v" by (rule conjE)
                    from antecedent have non_overlapping: "(y\<^bold>\<noteq>\<^sup>Lz) v" by (rule conjE)
                    text\<open>\<^item> Deriving @{text "T x' z"} in @{term u} using @{term compossibilty6}\<close>
                    from compossibilty6 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<forall>z. T x y \<^bold>\<rightarrow> \<^bold>\<box>((y\<^bold>\<noteq>\<^sup>Lz \<^bold>\<and> T x' z) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x y \<^bold>\<and> T x' z))) w"..
(*<*)
                    then have "(\<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<forall>z. T x y \<^bold>\<rightarrow> \<^bold>\<box>((y\<^bold>\<noteq>\<^sup>Lz \<^bold>\<and> T x' z) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x y \<^bold>\<and> T x' z))) w" by (rule allE)
                    then have "(\<^bold>\<forall>x'. \<^bold>\<forall>z. T x y \<^bold>\<rightarrow> \<^bold>\<box>((y\<^bold>\<noteq>\<^sup>Lz \<^bold>\<and> T x' z) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x y \<^bold>\<and> T x' z))) w" by (rule allE)
                    then have "(\<^bold>\<forall>z. T x y \<^bold>\<rightarrow> \<^bold>\<box>((y\<^bold>\<noteq>\<^sup>Lz \<^bold>\<and> T x' z) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x y \<^bold>\<and> T x' z))) w" by (rule allE)
                    then have "(T x y \<^bold>\<rightarrow> \<^bold>\<box>((y\<^bold>\<noteq>\<^sup>Lz \<^bold>\<and> T x' z) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x y \<^bold>\<and> T x' z))) w" by (rule allE)
(*>*)
                    then have "(\<^bold>\<box>((y\<^bold>\<noteq>\<^sup>Lz \<^bold>\<and> T x' z) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x y \<^bold>\<and> T x' z))) w"
                      using table_x1_from_y1 by (rule mp)
                    then have "((y\<^bold>\<noteq>\<^sup>Lz \<^bold>\<and> T x' z) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x y \<^bold>\<and> T x' z)) v" using `w r v` by auto
                    then have "\<^bold>\<diamond>(T x y \<^bold>\<and> T x' z) v" using antecedent by (rule mp)
                    then obtain u where u: "v r u \<and> ((T x y \<^bold>\<and> T x' z) u)" by (rule exE)
                    text\<open>\<^item> Framing the @{term origin_uniqueness6_ante}\<close>
                    then have origin_uniqueness6_ante: "(((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (T x y) \<^bold>\<and> (T x' z))) u" 
                      using non_overlapping by auto
                    from u have "v r u" by (rule conjE)
                    text\<open>\<^item> Falsifying the @{term identity} using @{term origin_uniqueness6}\<close>
                    from origin_uniqueness6 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<forall>z. (((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (T x y) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> ((x\<^bold>\<noteq>\<^sup>Lx')))) u"..
(*<*)
                    then have "(\<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<forall>z. (((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (T x y) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> ((x\<^bold>\<noteq>\<^sup>Lx')))) u" by (rule allE)
                    then have "(\<^bold>\<forall>x'. \<^bold>\<forall>z. (((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (T x y) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> ((x\<^bold>\<noteq>\<^sup>Lx')))) u" by (rule allE)
                    then have "(\<^bold>\<forall>z. (((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (T x y) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> ((x\<^bold>\<noteq>\<^sup>Lx')))) u" by (rule allE)
                    then have "((((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (T x y) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> ((x\<^bold>\<noteq>\<^sup>Lx')))) u" by (rule allE)
(*>*)
                    then have "((x\<^bold>\<noteq>\<^sup>Lx')) u" using origin_uniqueness6_ante by (rule mp)
                    then show "False" using identity and `v r u` by auto
(*<*)
                  qed
                qed
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
