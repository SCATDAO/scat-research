theory Auditors
  imports Main
begin

datatype status = busy | available 

datatype auditor = auditor (firstName: string)
                           (secondName:string) 
                           (currentStatus:status)

definition knowCurrentStatus :: "auditor \<Rightarrow> status" where
          "knowCurrentStatus x = currentStatus x"

fun removAuditor :: "status \<Rightarrow> auditor list \<Rightarrow> auditor list" where
   "removAuditor x [] = []" |
   "removAuditor x (y#ys) = (if x = knowCurrentStatus y then removAuditor x ys
                          else y#(removAuditor x ys))"

fun contains :: "auditor list \<Rightarrow> status \<Rightarrow> bool" where
"contains [] _ = False" |
"contains (x#xs) y = (if knowCurrentStatus x = y then True else contains xs y)"

fun LengthAcc :: "auditor list  \<Rightarrow> status \<Rightarrow> nat \<Rightarrow> nat" where
"LengthAcc [] _ n = n" |
"LengthAcc (x#xs) y n = (if knowCurrentStatus x = y then LengthAcc xs y (n+1) else LengthAcc xs y n)"

fun auditorLength :: "auditor list \<Rightarrow> status \<Rightarrow> nat" where
"auditorLength xs y =  LengthAcc xs y 0"

lemma first_lemma: "\<not>(contains(removAuditor a b) a)"
  nitpick
  sorry

lemma second_lemma: "(auditorLength b a) = (auditorLength(removAuditor a b)a) + (auditorLength b a)"
  nitpick
  apply (induct b)
  apply simp
  by auto

lemma last_lemma:
  "(removAuditor a b) = (removAuditor a b) \<longrightarrow> \<not>(contains (removAuditor a b) a)"
  nitpick
  apply(induct b)
   apply simp
proof -
  fix aa :: auditor and ba :: "auditor list"
  assume "removAuditor a ba = removAuditor a ba \<longrightarrow> \<not> contains (removAuditor a ba) a"
  then have "\<not> contains (removAuditor a ba) a"
    by meson
  then show "removAuditor a (aa # ba) = removAuditor a (aa # ba) \<longrightarrow> \<not> contains (removAuditor a (aa # ba)) a"
    using contains.simps(2) removAuditor.simps(2) by presburger
qed
end

(*
value "removAuditor busy [
(auditor ''Mx'' ''Koxnan'' busy),
(auditor ''Lawrence'' ''Muggerod'' available),
(auditor ''Mikae'' ''Konan'' busy)
]"

value "auditorLength (removAuditor busy [
(auditor ''Mx'' ''Koxnan'' available),
(auditor ''Lawrence'' ''Muggerod'' available),
(auditor ''Mikae'' ''Konan'' busy
)
]) busy"
value "(auditorLength [
(auditor ''Mx'' ''Koxnan'' available),
(auditor ''Lawrence'' ''Muggerod'' available),
(auditor ''Mikae'' ''Konan'' busy
)
]) busy"

value "auditorLength (removAuditor busy [
(auditor ''Mx'' ''Koxnan'' available),
(auditor ''Lawrence'' ''Muggerod'' available),
(auditor ''Mikae'' ''Konan'' busy
)
]) busy"


value "countAuditor (removAuditor busy [
(auditor ''Mx'' ''Koxnan'' available),
(auditor ''Lawrence'' ''Muggerod'' available),
(auditor ''Mikae'' ''Konan'' busy
)
]) "
 *)
