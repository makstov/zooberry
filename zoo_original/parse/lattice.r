
lattice L1 = {a,b,c} order a < b | b < c (* valid *)

lattice L2 = {a,b,c} order a < b < b < c (* invalid *)

lattice L3 = {a,b,c} order a < b < c < a (* invalid *)

lattice L4 = {a,b,c} order a < c | b < c (* invalid *)

lattice L5 = {a,b,c} order a < b | a < c (* invalid *)

lattice L6 = {a,b,c,d} order a < b < d | a < c < d (* valid *)

