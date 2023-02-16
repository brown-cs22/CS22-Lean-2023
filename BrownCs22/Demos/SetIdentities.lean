import BrownCs22.Library.Defs
open Set BrownCs22.Set

/-

At <https://brown-cs22.github.io/resources/math-resources/sets.pdf>
you can find a list of set identities, also called "rewrite rules."
Each rule on this list has a name in Lean! The names appear below,
following the order on the reference sheet.

-/

-- commutative laws 
#check union_comm 
#check inter_comm 

-- associative laws
#check union_assoc 
#check inter_assoc 

-- distributive laws
#check union_inter_distrib_left
#check union_inter_distrib_right 
#check inter_union_distrib_left
#check inter_union_distrib_right 

-- identity laws
#check union_empty 
#check inter_univ 

-- complement laws 
#check union_compl_self 
#check inter_compl_self 

-- double complement law 
#check compl_compl 

-- idempotent laws
#check union_self 
#check inter_self

-- universal bound laws
#check union_univ 
#check inter_empty

-- de morgan's laws
#check compl_union 
#check compl_inter

-- absorption laws 
#check union_inter_cancel_left
#check union_inter_cancel_right
#check inter_union_cancel_left 
#check inter_union_cancel_right 

-- complements of universe and empty 
#check compl_univ 
#check compl_empty 

-- set difference law 
#check diff_eq 