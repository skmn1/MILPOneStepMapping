\ENCODING=ISO-8859-1
\Problem name: 3indfunction

Minimize
 obj: 0.333333333333333 L(1) + 0.333333333333333 L(2) + 0.333333333333333 L(3)
Subject To
 c1#0:                           A({1,1})  = 1
 c2#1:                           A({2,1})  = 1
 c3#2:                           A({3,1})  = 1
 fi_and_fj_are_placed_on_the_same_node_or_not({1,10})({2,10})({1,1})#3:
                                 A({1,1}) + A({2,1}) - 2 X({1,2,1}) >= 0
 c5#4:                           A({1,1}) + A({2,1}) - 2 X({1,2,1}) <= 1
 fi_and_fj_are_placed_on_the_same_node_or_not({1,10})({3,10})({1,1})#5:
                                 A({1,1}) + A({3,1}) - 2 X({1,3,1}) >= 0
 c7#6:                           A({1,1}) + A({3,1}) - 2 X({1,3,1}) <= 1
 fi_and_fj_are_placed_on_the_same_node_or_not({2,10})({1,10})({1,1})#7:
                                 A({1,1}) + A({2,1}) - 2 X({2,1,1}) >= 0
 c9#8:                           A({1,1}) + A({2,1}) - 2 X({2,1,1}) <= 1
 fi_and_fj_are_placed_on_the_same_node_or_not({2,10})({3,10})({1,1})#9:
                                 A({2,1}) + A({3,1}) - 2 X({2,3,1}) >= 0
 c11#10:                         A({2,1}) + A({3,1}) - 2 X({2,3,1}) <= 1
 fi_and_fj_are_placed_on_the_same_node_or_not({3,10})({1,10})({1,1})#11:
                                 A({1,1}) + A({3,1}) - 2 X({3,1,1}) >= 0
 c13#12:                         A({1,1}) + A({3,1}) - 2 X({3,1,1}) <= 1
 fi_and_fj_are_placed_on_the_same_node_or_not({3,10})({2,10})({1,1})#13:
                                 A({2,1}) + A({3,1}) - 2 X({3,2,1}) >= 0
 c15#14:                         A({2,1}) + A({3,1}) - 2 X({3,2,1}) <= 1
 _execution_node_constraining({1,1})#15: 0.1 A({1,1}) + 0.6 A({2,1})
                                 + 0.2 A({3,1}) <= 1
 priority_order_for_function({1,10})({2,10})#16: Psi({1,2}) + Psi({2,1}) <= 1
 priority_order_for_function({1,10})({3,10})#17: Psi({1,3}) + Psi({3,1}) <= 1
 priority_order_for_function({2,10})({1,10})#18: Psi({1,2}) + Psi({2,1}) <= 1
 priority_order_for_function({2,10})({3,10})#19: Psi({2,3}) + Psi({3,2}) <= 1
 priority_order_for_function({3,10})({1,10})#20: Psi({1,3}) + Psi({3,1}) <= 1
 priority_order_for_function({3,10})({2,10})#21: Psi({2,3}) + Psi({3,2}) <= 1
 c23#22:                         Psi({1,2}) - Psi({1,3}) + Psi({2,3}) <= 1
 c24#23:                         Psi({1,2}) - Psi({1,3}) - Psi({2,3})
                                 - Psi({3,2}) <= 0
 c25#24:                         - Psi({1,2}) - Psi({2,1}) - Psi({1,3})
                                 + Psi({2,3}) <= 0
 c26#25:                         Psi({1,2}) + Psi({2,1}) - Psi({1,3})
                                 + Psi({2,3}) + Psi({3,2}) >= 0
 c27#26:                         Psi({1,2}) + Psi({2,1}) - Psi({3,1})
                                 + Psi({2,3}) + Psi({3,2}) >= 0
 c28#27:                         - Psi({1,2}) + Psi({1,3}) + Psi({3,2}) <= 1
 c29#28:                         - Psi({1,2}) + Psi({1,3}) - Psi({2,3})
                                 - Psi({3,2}) <= 0
 c30#29:                         - Psi({1,2}) - Psi({1,3}) - Psi({3,1})
                                 + Psi({3,2}) <= 0
 c31#30:                         - Psi({1,2}) + Psi({1,3}) + Psi({3,1})
                                 + Psi({2,3}) + Psi({3,2}) >= 0
 c32#31:                         - Psi({2,1}) + Psi({1,3}) + Psi({3,1})
                                 + Psi({2,3}) + Psi({3,2}) >= 0
 c33#32:                         Psi({2,1}) + Psi({1,3}) - Psi({2,3}) <= 1
 c34#33:                         Psi({2,1}) - Psi({1,3}) - Psi({3,1})
                                 - Psi({2,3}) <= 0
 c35#34:                         - Psi({1,2}) - Psi({2,1}) + Psi({1,3})
                                 - Psi({2,3}) <= 0
 c36#35:                         Psi({1,2}) + Psi({2,1}) + Psi({1,3})
                                 + Psi({3,1}) - Psi({2,3}) >= 0
 c37#36:                         Psi({1,2}) + Psi({2,1}) + Psi({1,3})
                                 + Psi({3,1}) - Psi({3,2}) >= 0
 c38#37:                         - Psi({2,1}) + Psi({3,1}) + Psi({2,3}) <= 1
 c39#38:                         - Psi({2,1}) - Psi({1,3}) - Psi({3,1})
                                 + Psi({2,3}) <= 0
 c40#39:                         - Psi({2,1}) + Psi({3,1}) - Psi({2,3})
                                 - Psi({3,2}) <= 0
 c41#40:                         - Psi({2,1}) + Psi({1,3}) + Psi({3,1})
                                 + Psi({2,3}) + Psi({3,2}) >= 0
 c42#41:                         - Psi({1,2}) + Psi({1,3}) + Psi({3,1})
                                 + Psi({2,3}) + Psi({3,2}) >= 0
 c43#42:                         Psi({1,2}) + Psi({3,1}) - Psi({3,2}) <= 1
 c44#43:                         - Psi({1,2}) - Psi({2,1}) + Psi({3,1})
                                 - Psi({3,2}) <= 0
 c45#44:                         Psi({1,2}) - Psi({1,3}) - Psi({3,1})
                                 - Psi({3,2}) <= 0
 c46#45:                         Psi({1,2}) + Psi({2,1}) + Psi({1,3})
                                 + Psi({3,1}) - Psi({3,2}) >= 0
 c47#46:                         Psi({1,2}) + Psi({2,1}) + Psi({1,3})
                                 + Psi({3,1}) - Psi({2,3}) >= 0
 c48#47:                         Psi({2,1}) - Psi({3,1}) + Psi({3,2}) <= 1
 c49#48:                         - Psi({1,2}) - Psi({2,1}) - Psi({3,1})
                                 + Psi({3,2}) <= 0
 c50#49:                         Psi({2,1}) - Psi({3,1}) - Psi({2,3})
                                 - Psi({3,2}) <= 0
 c51#50:                         Psi({1,2}) + Psi({2,1}) - Psi({3,1})
                                 + Psi({2,3}) + Psi({3,2}) >= 0
 c52#51:                         Psi({1,2}) + Psi({2,1}) - Psi({1,3})
                                 + Psi({2,3}) + Psi({3,2}) >= 0
 functions_placed_on_same_nodes_and_i_has_priority_lower_than_j({1,10})({2,10})({1,1})#52:
                                 X({1,2,1}) + Psi({2,1}) - 2 SnHp({1,2,1}) >= 0
 c54#53:                         X({1,2,1}) + Psi({2,1}) - 2 SnHp({1,2,1}) <= 1
 functions_placed_on_same_nodes_and_i_has_priority_lower_than_j({1,10})({3,10})({1,1})#54:
                                 X({1,3,1}) + Psi({3,1}) - 2 SnHp({1,3,1}) >= 0
 c56#55:                         X({1,3,1}) + Psi({3,1}) - 2 SnHp({1,3,1}) <= 1
 functions_placed_on_same_nodes_and_i_has_priority_lower_than_j({2,10})({1,10})({1,1})#56:
                                 X({2,1,1}) + Psi({1,2}) - 2 SnHp({2,1,1}) >= 0
 c58#57:                         X({2,1,1}) + Psi({1,2}) - 2 SnHp({2,1,1}) <= 1
 functions_placed_on_same_nodes_and_i_has_priority_lower_than_j({2,10})({3,10})({1,1})#58:
                                 X({2,3,1}) + Psi({3,2}) - 2 SnHp({2,3,1}) >= 0
 c60#59:                         X({2,3,1}) + Psi({3,2}) - 2 SnHp({2,3,1}) <= 1
 functions_placed_on_same_nodes_and_i_has_priority_lower_than_j({3,10})({1,10})({1,1})#60:
                                 X({3,1,1}) + Psi({1,3}) - 2 SnHp({3,1,1}) >= 0
 c62#61:                         X({3,1,1}) + Psi({1,3}) - 2 SnHp({3,1,1}) <= 1
 functions_placed_on_same_nodes_and_i_has_priority_lower_than_j({3,10})({2,10})({1,1})#62:
                                 X({3,2,1}) + Psi({2,3}) - 2 SnHp({3,2,1}) >= 0
 c64#63:                         X({3,2,1}) + Psi({2,3}) - 2 SnHp({3,2,1}) <= 1
 functions_placed_on_same_nodes_and_partitioned_on_different_tasks({1,10})({2,10})({1,1})#64:
                                 - SnHp({1,2,1}) - SnHp({2,1,1})
                                 + SnDp({1,2,1})  = 0
 functions_placed_on_same_nodes_and_partitioned_on_different_tasks({1,10})({3,10})({1,1})#65:
                                 - SnHp({1,3,1}) - SnHp({3,1,1})
                                 + SnDp({1,3,1})  = 0
 functions_placed_on_same_nodes_and_partitioned_on_different_tasks({2,10})({1,10})({1,1})#66:
                                 - SnHp({1,2,1}) - SnHp({2,1,1})
                                 + SnDp({2,1,1})  = 0
 functions_placed_on_same_nodes_and_partitioned_on_different_tasks({2,10})({3,10})({1,1})#67:
                                 - SnHp({2,3,1}) - SnHp({3,2,1})
                                 + SnDp({2,3,1})  = 0
 functions_placed_on_same_nodes_and_partitioned_on_different_tasks({3,10})({1,10})({1,1})#68:
                                 - SnHp({1,3,1}) - SnHp({3,1,1})
                                 + SnDp({3,1,1})  = 0
 functions_placed_on_same_nodes_and_partitioned_on_different_tasks({3,10})({2,10})({1,1})#69:
                                 - SnHp({2,3,1}) - SnHp({3,2,1})
                                 + SnDp({3,2,1})  = 0
 functions_placed_on_same_nodes_and_partitioned_on_same_tasks({1,10})({2,10})({1,1})#70:
                                 - X({1,2,1}) + SnDp({1,2,1}) + SnSp({1,2,1})
                                  = 0
 functions_placed_on_same_nodes_and_partitioned_on_same_tasks({1,10})({3,10})({1,1})#71:
                                 - X({1,3,1}) + SnDp({1,3,1}) + SnSp({1,3,1})
                                  = 0
 functions_placed_on_same_nodes_and_partitioned_on_same_tasks({2,10})({1,10})({1,1})#72:
                                 - X({2,1,1}) + SnDp({2,1,1}) + SnSp({2,1,1})
                                  = 0
 functions_placed_on_same_nodes_and_partitioned_on_same_tasks({2,10})({3,10})({1,1})#73:
                                 - X({2,3,1}) + SnDp({2,3,1}) + SnSp({2,3,1})
                                  = 0
 functions_placed_on_same_nodes_and_partitioned_on_same_tasks({3,10})({1,10})({1,1})#74:
                                 - X({3,1,1}) + SnDp({3,1,1}) + SnSp({3,1,1})
                                  = 0
 functions_placed_on_same_nodes_and_partitioned_on_same_tasks({3,10})({2,10})({1,1})#75:
                                 - X({3,2,1}) + SnDp({3,2,1}) + SnSp({3,2,1})
                                  = 0
 WCRT_computation({1,10})#76:    R(1) - W(1) - J(1)  = 0
 WCRT_computation({2,10})#77:    R(2) - W(2) - J(2)  = 0
 WCRT_computation({3,10})#78:    R(3) - W(3) - J(3)  = 0
 c80#79:                         - 0.1 W(1) - 0.1 J(2) + Sigma({1,2}) >= 0
 c81#80:                         - 0.1 W(1) - 0.1 J(2) + Sigma({1,2})
                                 <= 0.999999999
 c82#81:                         - 0.1 W(1) - 0.1 J(3) + Sigma({1,3}) >= 0
 c83#82:                         - 0.1 W(1) - 0.1 J(3) + Sigma({1,3})
                                 <= 0.999999999
 c84#83:                         - 0.1 J(1) - 0.1 W(2) + Sigma({2,1}) >= 0
 c85#84:                         - 0.1 J(1) - 0.1 W(2) + Sigma({2,1})
                                 <= 0.999999999
 c86#85:                         - 0.1 W(2) - 0.1 J(3) + Sigma({2,3}) >= 0
 c87#86:                         - 0.1 W(2) - 0.1 J(3) + Sigma({2,3})
                                 <= 0.999999999
 c88#87:                         - 0.1 J(1) - 0.1 W(3) + Sigma({3,1}) >= 0
 c89#88:                         - 0.1 J(1) - 0.1 W(3) + Sigma({3,1})
                                 <= 0.999999999
 c90#89:                         - 0.1 J(2) - 0.1 W(3) + Sigma({3,2}) >= 0
 c91#90:                         - 0.1 J(2) - 0.1 W(3) + Sigma({3,2})
                                 <= 0.999999999
 worst_case_number_of_interf_fj_on_fi_within_Ck({1,10})({2,10})({1,1})#91:
                                 10000 SnHp({1,2,1}) + Sigma({1,2})
                                 - I({1,2,1}) <= 10000
 c93#92:                         - Sigma({1,2}) + I({1,2,1}) <= 0
 c94#93:                         - 10000 SnHp({1,2,1}) + I({1,2,1}) <= 0
 worst_case_number_of_interf_fj_on_fi_within_Ck({1,10})({3,10})({1,1})#94:
                                 10000 SnHp({1,3,1}) + Sigma({1,3})
                                 - I({1,3,1}) <= 10000
 c96#95:                         - Sigma({1,3}) + I({1,3,1}) <= 0
 c97#96:                         - 10000 SnHp({1,3,1}) + I({1,3,1}) <= 0
 worst_case_number_of_interf_fj_on_fi_within_Ck({2,10})({1,10})({1,1})#97:
                                 10000 SnHp({2,1,1}) + Sigma({2,1})
                                 - I({2,1,1}) <= 10000
 c99#98:                         - Sigma({2,1}) + I({2,1,1}) <= 0
 c100#99:                        - 10000 SnHp({2,1,1}) + I({2,1,1}) <= 0
 worst_case_number_of_interf_fj_on_fi_within_Ck({2,10})({3,10})({1,1})#100:
                                 10000 SnHp({2,3,1}) + Sigma({2,3})
                                 - I({2,3,1}) <= 10000
 c102#101:                       - Sigma({2,3}) + I({2,3,1}) <= 0
 c103#102:                       - 10000 SnHp({2,3,1}) + I({2,3,1}) <= 0
 worst_case_number_of_interf_fj_on_fi_within_Ck({3,10})({1,10})({1,1})#103:
                                 10000 SnHp({3,1,1}) + Sigma({3,1})
                                 - I({3,1,1}) <= 10000
 c105#104:                       - Sigma({3,1}) + I({3,1,1}) <= 0
 c106#105:                       - 10000 SnHp({3,1,1}) + I({3,1,1}) <= 0
 worst_case_number_of_interf_fj_on_fi_within_Ck({3,10})({2,10})({1,1})#106:
                                 10000 SnHp({3,2,1}) + Sigma({3,2})
                                 - I({3,2,1}) <= 10000
 c108#107:                       - Sigma({3,2}) + I({3,2,1}) <= 0
 c109#108:                       - 10000 SnHp({3,2,1}) + I({3,2,1}) <= 0
 completion_time_W_of_a_function({1,10})#109: - A({1,1}) - 6 SnSp({1,2,1})
                                 - 2 SnSp({1,3,1}) + W(1) - 6 I({1,2,1})
                                 - 2 I({1,3,1})  = 0
 completion_time_W_of_a_function({2,10})#110: - 6 A({2,1}) - SnSp({2,1,1})
                                 - 2 SnSp({2,3,1}) + W(2) - I({2,1,1})
                                 - 2 I({2,3,1})  = 0
 completion_time_W_of_a_function({3,10})#111: - 2 A({3,1}) - SnSp({3,1,1})
                                 - 6 SnSp({3,2,1}) + W(3) - I({3,1,1})
                                 - 6 I({3,2,1})  = 0
 c113#112:                       10000 SnSp({1,2,1}) + Phi(2) - Theta({1,2})
                                 <= 10000
 c114#113:                       10000 SnSp({1,3,1}) + Phi(3) - Theta({1,3})
                                 <= 10000
 c115#114:                       10000 SnSp({2,1,1}) + Phi(1) - Theta({2,1})
                                 <= 10000
 c116#115:                       10000 SnSp({2,3,1}) + Phi(3) - Theta({2,3})
                                 <= 10000
 c117#116:                       10000 SnSp({3,1,1}) + Phi(1) - Theta({3,1})
                                 <= 10000
 c118#117:                       10000 SnSp({3,2,1}) + Phi(2) - Theta({3,2})
                                 <= 10000
 c119#118:                       - Phi(2) + Theta({1,2}) <= 0
 c120#119:                       - Phi(3) + Theta({1,3}) <= 0
 c121#120:                       - Phi(1) + Theta({2,1}) <= 0
 c122#121:                       - Phi(3) + Theta({2,3}) <= 0
 c123#122:                       - Phi(1) + Theta({3,1}) <= 0
 c124#123:                       - Phi(2) + Theta({3,2}) <= 0
 c125#124:                       - 10000 SnSp({1,2,1}) + Theta({1,2}) <= 0
 c126#125:                       - 10000 SnSp({1,3,1}) + Theta({1,3}) <= 0
 c127#126:                       - 10000 SnSp({2,1,1}) + Theta({2,1}) <= 0
 c128#127:                       - 10000 SnSp({2,3,1}) + Theta({2,3}) <= 0
 c129#128:                       - 10000 SnSp({3,1,1}) + Theta({3,1}) <= 0
 c130#129:                       - 10000 SnSp({3,2,1}) + Theta({3,2}) <= 0
 c131#130:                       J(1) - Theta({1,2}) >= 0
 c132#131:                       J(1) - Theta({1,3}) >= 0
 c133#132:                       J(2) - Theta({2,1}) >= 0
 c134#133:                       J(2) - Theta({2,3}) >= 0
 c135#134:                       J(3) - Theta({3,1}) >= 0
 c136#135:                       J(3) - Theta({3,2}) >= 0
 c137#136:                       L(1) - R(1)  = 0
 c138#137:                       L(2) - R(2)  = 0
 c139#138:                       L(3) - R(3)  = 0
 c140#139:                       L(1) <= 3
 c141#140:                       L(2) <= 8
 c142#141:                       L(3) <= 4
Bounds
 0 <= A({1,1}) <= 1
 0 <= A({2,1}) <= 1
 0 <= A({3,1}) <= 1
 0 <= X({1,2,1}) <= 1
 0 <= X({1,3,1}) <= 1
 0 <= X({2,1,1}) <= 1
 0 <= X({2,3,1}) <= 1
 0 <= X({3,1,1}) <= 1
 0 <= X({3,2,1}) <= 1
 0 <= Psi({1,2}) <= 1
 0 <= Psi({2,1}) <= 1
 0 <= Psi({1,3}) <= 1
 0 <= Psi({3,1}) <= 1
 0 <= Psi({2,3}) <= 1
 0 <= Psi({3,2}) <= 1
 0 <= SnHp({1,2,1}) <= 1
 0 <= SnHp({1,3,1}) <= 1
 0 <= SnHp({2,1,1}) <= 1
 0 <= SnHp({2,3,1}) <= 1
 0 <= SnHp({3,1,1}) <= 1
 0 <= SnHp({3,2,1}) <= 1
 0 <= SnDp({1,2,1}) <= 1
 0 <= SnDp({1,3,1}) <= 1
 0 <= SnDp({2,1,1}) <= 1
 0 <= SnDp({2,3,1}) <= 1
 0 <= SnDp({3,1,1}) <= 1
 0 <= SnDp({3,2,1}) <= 1
 0 <= SnSp({1,2,1}) <= 1
 0 <= SnSp({1,3,1}) <= 1
 0 <= SnSp({2,1,1}) <= 1
 0 <= SnSp({2,3,1}) <= 1
 0 <= SnSp({3,1,1}) <= 1
 0 <= SnSp({3,2,1}) <= 1
      Sigma({1,2}) >= 0
      Sigma({1,3}) >= 0
      Sigma({2,1}) >= 0
      Sigma({2,3}) >= 0
      Sigma({3,1}) >= 0
      Sigma({3,2}) >= 0
      I({1,2,1}) >= 0
      I({1,3,1}) >= 0
      I({2,1,1}) >= 0
      I({2,3,1}) >= 0
      I({3,1,1}) >= 0
      I({3,2,1}) >= 0
      Phi(2) Free
      Theta({1,2}) Free
      Phi(3) Free
      Theta({1,3}) Free
      Phi(1) Free
      Theta({2,1}) Free
      Theta({2,3}) Free
      Theta({3,1}) Free
      Theta({3,2}) Free
Binaries
 A({1,1})  A({2,1})  A({3,1})  X({1,2,1})  X({1,3,1})  X({2,1,1})  X({2,3,1}) 
 X({3,1,1})  X({3,2,1})  Psi({1,2})  Psi({2,1})  Psi({1,3})  Psi({3,1}) 
 Psi({2,3})  Psi({3,2})  SnHp({1,2,1})  SnHp({1,3,1})  SnHp({2,1,1}) 
 SnHp({2,3,1})  SnHp({3,1,1})  SnHp({3,2,1})  SnDp({1,2,1})  SnDp({1,3,1}) 
 SnDp({2,1,1})  SnDp({2,3,1})  SnDp({3,1,1})  SnDp({3,2,1})  SnSp({1,2,1}) 
 SnSp({1,3,1})  SnSp({2,1,1})  SnSp({2,3,1})  SnSp({3,1,1})  SnSp({3,2,1}) 
Generals
 Sigma({1,2})  Sigma({1,3})  Sigma({2,1})  Sigma({2,3})  Sigma({3,1}) 
 Sigma({3,2})  I({1,2,1})  I({1,3,1})  I({2,1,1})  I({2,3,1})  I({3,1,1}) 
 I({3,2,1})  Phi(2)  Theta({1,2})  Phi(3)  Theta({1,3})  Phi(1)  Theta({2,1}) 
 Theta({2,3})  Theta({3,1})  Theta({3,2}) 
End
