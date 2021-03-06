@BE1
@invar
(ANDA ANDB EXORA EXORB CARRYIN A[0] B[0] A[1] B[1] A[2] B[2] A[3] B[3] 
A[4] B[4] A[5] B[5] A[6] B[6] A[7] B[7])

@sub
aftbuf1 = (NOT ANDA)
aftbuf2 = (NOT ANDB)
aftbuf3 = (NOT EXORA)
aftbuf4 = (NOT EXORB)
aftbuf5 = (NOT CARRYIN)

n1[0] = (AND aftbuf1 A[0])
n1[1] = (AND aftbuf1 A[1])
n1[2] = (AND aftbuf1 A[2])
n1[3] = (AND aftbuf1 A[3])
n1[4] = (AND aftbuf1 A[4])
n1[5] = (AND aftbuf1 A[5])
n1[6] = (AND aftbuf1 A[6])
n1[7] = (AND aftbuf1 A[7])

n3[0] = (AND aftbuf2 B[0])
n3[1] = (AND aftbuf2 B[1])
n3[2] = (AND aftbuf2 B[2])
n3[3] = (AND aftbuf2 B[3])
n3[4] = (AND aftbuf2 B[4])
n3[5] = (AND aftbuf2 B[5])
n3[6] = (AND aftbuf2 B[6])
n3[7] = (AND aftbuf2 B[7])

n2[0] = (OR (AND aftbuf3 (NOT n1[0])) (AND (NOT aftbuf3) n1[0]))
n2[1] = (OR (AND aftbuf3 (NOT n1[1])) (AND (NOT aftbuf3) n1[1]))
n2[2] = (OR (AND aftbuf3 (NOT n1[2])) (AND (NOT aftbuf3) n1[2]))
n2[3] = (OR (AND aftbuf3 (NOT n1[3])) (AND (NOT aftbuf3) n1[3]))
n2[4] = (OR (AND aftbuf3 (NOT n1[4])) (AND (NOT aftbuf3) n1[4]))
n2[5] = (OR (AND aftbuf3 (NOT n1[5])) (AND (NOT aftbuf3) n1[5]))
n2[6] = (OR (AND aftbuf3 (NOT n1[6])) (AND (NOT aftbuf3) n1[6]))
n2[7] = (OR (AND aftbuf3 (NOT n1[7])) (AND (NOT aftbuf3) n1[7]))

n4[0] = (OR (AND aftbuf4 (NOT n3[0])) (AND (NOT aftbuf4) n3[0]))
n4[1] = (OR (AND aftbuf4 (NOT n3[1])) (AND (NOT aftbuf4) n3[1]))
n4[2] = (OR (AND aftbuf4 (NOT n3[2])) (AND (NOT aftbuf4) n3[2]))
n4[3] = (OR (AND aftbuf4 (NOT n3[3])) (AND (NOT aftbuf4) n3[3]))
n4[4] = (OR (AND aftbuf4 (NOT n3[4])) (AND (NOT aftbuf4) n3[4]))
n4[5] = (OR (AND aftbuf4 (NOT n3[5])) (AND (NOT aftbuf4) n3[5]))
n4[6] = (OR (AND aftbuf4 (NOT n3[6])) (AND (NOT aftbuf4) n3[6]))
n4[7] = (OR (AND aftbuf4 (NOT n3[7])) (AND (NOT aftbuf4) n3[7]))


COUT1 = (OR (AND aftbuf5 n4[0]) (AND aftbuf5 n2[0]) (AND n4[0] n2[0]))
COUT2 = (OR (AND COUT1 n4[1]) (AND COUT1 n2[1]) (AND n4[1] n2[1]))
COUT3 = (OR (AND COUT2 n4[2]) (AND COUT2 n2[2]) (AND n4[2] n2[2]))
COUT4 = (OR (AND COUT3 n4[3]) (AND COUT3 n2[3]) (AND n4[3] n2[3]))
COUT5 = (OR (AND COUT4 n4[4]) (AND COUT4 n2[4]) (AND n4[4] n2[4]))
COUT6 = (OR (AND COUT5 n4[5]) (AND COUT5 n2[5]) (AND n4[5] n2[5]))
COUT7 = (OR (AND COUT6 n4[6]) (AND COUT6 n2[6]) (AND n4[6] n2[6]))

hulp0 = (EXOR n2[0] n4[0]  aftbuf5)
hulp1 = (EXOR n2[1] n4[1]  COUT1)
hulp2 = (EXOR n2[2] n4[2]  COUT2)
hulp3 = (EXOR n2[3] n4[3]  COUT3)
hulp4 = (EXOR n2[4] n4[4]  COUT4)
hulp5 = (EXOR n2[5] n4[5]  COUT5)
hulp6 = (EXOR n2[6] n4[6]  COUT6)
hulp7 = (EXOR n2[7] n4[7]  COUT7)
hulp8 = (OR (AND COUT7 n4[7]) (AND COUT7 n2[7]) (AND n4[7] n2[7]))

@out
O[0] = (hulp0)
O[1] = (hulp1)
O[2] = (hulp2)
O[3] = (hulp3)
O[4] = (hulp4)
O[5] = (hulp5)
O[6] = (hulp6)
O[7] = (hulp7)
CARRYOUT = (NOT hulp8)
OVERFLOW = (NOT (EXOR COUT7 hulp8))
SIGN = (NOT hulp7)

@end


@BE2
@invar
(CARRYIN ANDA ANDB EXORA EXORB A[0] B[0] A[1] B[1] A[2] B[2] A[3] B[3] A[4] B[4]
A[5] B[5] A[6] B[6] A[7] B[7])

@sub
N3 = (A[1]) 
N4 = (A[4]) 
N5 = (A[6]) 
N6 = (A[5])
N7 = (A[0]) 
N8 = (A[2]) 
N9 = (A[7]) 
N10 = (A[3]) 
N11 = (ANDA) 
N12 = (EXORA)
N13 = (B[4]) 
N14 = (B[6]) 
N15 = (B[3]) 
N16 = (B[0]) 
N17 = (B[1]) 
N18 = (B[7]) 
N19 = (B[5])
N20 = (B[2]) 
N21 = (ANDB) 
N22 = (EXORB)
N23 = (CARRYIN)

N74 = (NOT N23)
N70 = (NOT N21)
N76 = (NOT N22)
N69 = (NOT N11)
N75 = (NOT N12) 
N165 = (OR (NOT N9) (NOT N69))
N173 = (NOT N75)
N166 = (OR (NOT N18) (NOT N70))
N174 = (NOT N76)
N160 = (OR (NOT N14) (NOT N70))
N152 = (NOT N76)
N159 = (OR (NOT N5) (NOT N69))
N151 = (NOT N75)
N134 = (OR (NOT N13) (NOT N70))
N126 = (NOT N76)
N133 = (OR (NOT N4) (NOT N69))
N125 = (NOT N75)
N113 = (OR (NOT N10) (NOT N69))
N121 = (NOT N75)
N114 = (OR (NOT N15) (NOT N70))
N122 = (NOT N76)
N140 = (OR (NOT N19) (NOT N70))
N148 = (NOT N76)
N139 = (OR (NOT N6) (NOT N69))
N147 = (NOT N75)
N87 = (OR (NOT N3) (NOT N69))
N95 = (NOT N75)
N88 = (OR (NOT N17) (NOT N70))
N96 = (NOT N76)
N108 = (OR (NOT N20) (NOT N70))
N100 = (NOT N76)
N107 = (OR (NOT N8) (NOT N69))
N99 = (NOT N75)
N77 = (NOT N74)
N82 = (OR (NOT N16) (NOT N70))
N72 = (NOT N76)
N81 = (OR (NOT N7) (NOT N69))
N71 = (NOT N75)
N65 = (NOT N165)
N63 = (NOT N166)
N61 = (NOT N160)
N59 = (NOT N159)
N53 = (NOT N134)
N51 = (NOT N133)
N49 = (NOT N113)
N47 = (NOT N114)
N55 = (NOT N140)
N57 = (NOT N139)
N41 = (NOT N87)
N39 = (NOT N88)
N45 = (NOT N108)
N43 = (NOT N107)
N37 = (NOT N82)
N35 = (NOT N81)
N168 = (NOT (EXOR N65 N75))
N169 = (NOT (EXOR N63 N76))
N158 = (NOT (EXOR N61 N76))
N157 = (NOT (EXOR N59 N75))
N132 = (NOT (EXOR N53 N76))
N131 = (NOT (EXOR N51 N75))
N116 = (NOT (EXOR N49 N75))
N117 = (NOT (EXOR N47 N76))
N143 = (NOT (EXOR N55 N76))
N142 = (NOT (EXOR N57 N75))
N90 = (NOT (EXOR N41 N75))
N91 = (NOT (EXOR N39 N76))
N106 = (NOT (EXOR N45 N76))
N105 = (NOT (EXOR N43 N75))
N80 = (NOT (EXOR N37 N76))
N79 = (NOT (EXOR N35 N75))
N66 = (NOT N168)
N64 = (NOT N169)
N62 = (NOT N158)
N60 = (NOT N157)
N54 = (NOT N132)
N52 = (NOT N131)
N50 = (NOT N116)
N48 = (NOT N117)
N56 = (NOT N143)
N58 = (NOT N142)
N42 = (NOT N90)
N40 = (NOT N91)
N46 = (NOT N106)
N44 = (NOT N105)
N38 = (NOT N80)
N36 = (NOT N79)
N172 = (NOT N66)
N150 = (NOT N60)
N124 = (NOT N52)
N120 = (NOT N50)
N146 = (NOT N58)
N94 = (NOT N42)
N98 = (NOT N44)
N68 = (NOT N36)
N171 = (NOT (EXOR N64 N66))
N153 = (NOT (EXOR N62 N60))
N127 = (NOT (EXOR N54 N52))
N119 = (NOT (EXOR N48 N50))
N145 = (NOT (EXOR N56 N58))
N93 = (NOT (EXOR N40 N42))
N101 = (NOT (EXOR N46 N44))
N73 = (NOT (EXOR N38 N36))
N163 = (NOT N171)
N149 = (NOT N153)
N123 = (NOT N127)
N111 = (NOT N119)
N137 = (NOT N145)
N85 = (NOT N93)
N97 = (NOT N101)
N67 = (NOT N73)
N170 = (NOT N163)
N161 = (NOT N149)
N135 = (NOT N123)
N118 = (NOT N111)
N144 = (NOT N137)
N92 = (NOT N85)
N109 = (NOT N97)
N83 = (NOT N67)
N84 = (OR (AND (NOT N67) (NOT N36)) (AND (NOT N83) (NOT N74)))
N78 = (EXOR N77 N67)
N86 = (NOT N84)
N102 = (OR (AND (NOT N92) (NOT N84)) (AND (NOT N94) (NOT N85)))
N28 = (NOT N78)
N110 = (OR (AND (NOT N97) (NOT N44)) (AND (NOT N109) (NOT N102)))
N89 = (NOT (EXOR N86 N85))
N103 = (NOT N102)
N112 = (NOT N110)
N128 = (OR (AND (NOT N118) (NOT N110)) (AND (NOT N120) (NOT N111)))
N24 = (NOT N89)
N104 = (EXOR N103 N97)
N115 = (NOT (EXOR N112 N111))
N129 = (NOT N128)
N136 = (OR (AND (NOT N123) (NOT N52)) (AND (NOT N135) (NOT N128)))
N26 = (NOT N104)
N25 = (NOT N115)
N130 = (EXOR N129 N123)
N154 = (OR (AND (NOT N144) (NOT N136)) (AND (NOT N146) (NOT N137)))
N138 = (NOT N136)
N27 = (NOT N130)
N162 = (OR (AND (NOT N149) (NOT N60)) (AND (NOT N161) (NOT N154)))
N155 = (NOT N154)
N141 = (NOT (EXOR N138 N137)) 
N164 = (NOT N162)
N175 = (NOT N162)
N176 = (OR (AND (NOT N170) (NOT N162)) (AND (NOT N172) (NOT N163)))
N156 = (EXOR N155 N149) 
N30 = (NOT N141)
N167 = (NOT (EXOR N164 N163))
N177 = (NOT (EXOR N176 N162))
N31 = (NOT N176)
N29 = (NOT N156)
N34 = (NOT N167)
N32 = (NOT N177)
N33 = (NOT N34) 

@out
O[1] = (N24)
O[3] = (N25)
O[2] = (N26)
O[4] = (N27)
O[0] = (N28)
O[6] = (N29)
O[5] = (N30)
CARRYOUT =  (N31)
OVERFLOW =  (N32)
SIGN =  (N33)
O[7] =  (N34)

@end
