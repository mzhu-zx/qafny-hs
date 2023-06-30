{-# OPTIONS_GHC -w #-}
module Qafny.Parser(scanAndParse) where
import qualified Qafny.Lexer as L
import           Qafny.ParserUtils
import           Qafny.AST
import           Control.Monad
import qualified Data.Array as Happy_Data_Array
import qualified Data.Bits as Bits
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.19.12

data HappyAbsSyn t4 t5 t6 t7 t8 t10 t11 t12 t13 t14 t16 t17 t18 t20 t23 t28 t29 t30 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42
	= HappyTerminal (L.SToken)
	| HappyErrorToken Int
	| HappyAbsSyn4 t4
	| HappyAbsSyn5 t5
	| HappyAbsSyn6 t6
	| HappyAbsSyn7 t7
	| HappyAbsSyn8 t8
	| HappyAbsSyn9 (Partition)
	| HappyAbsSyn10 t10
	| HappyAbsSyn11 t11
	| HappyAbsSyn12 t12
	| HappyAbsSyn13 t13
	| HappyAbsSyn14 t14
	| HappyAbsSyn15 (QTy)
	| HappyAbsSyn16 t16
	| HappyAbsSyn17 t17
	| HappyAbsSyn18 t18
	| HappyAbsSyn20 t20
	| HappyAbsSyn21 (Exp)
	| HappyAbsSyn23 t23
	| HappyAbsSyn25 (Op2)
	| HappyAbsSyn28 t28
	| HappyAbsSyn29 t29
	| HappyAbsSyn30 t30
	| HappyAbsSyn31 t31
	| HappyAbsSyn32 t32
	| HappyAbsSyn33 t33
	| HappyAbsSyn34 t34
	| HappyAbsSyn35 t35
	| HappyAbsSyn36 t36
	| HappyAbsSyn37 t37
	| HappyAbsSyn38 t38
	| HappyAbsSyn39 t39
	| HappyAbsSyn40 t40
	| HappyAbsSyn41 t41
	| HappyAbsSyn42 t42

happyExpList :: Happy_Data_Array.Array Int Int
happyExpList = Happy_Data_Array.listArray (0,628) ([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6144,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1024,0,0,0,0,0,1024,0,0,0,0,0,0,1024,0,0,0,0,0,2048,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4096,0,0,0,0,0,0,32,0,0,0,864,2,0,0,0,0,0,0,0,4,0,0,0,8,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24576,1,0,0,0,0,0,0,0,1024,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4096,0,0,0,0,0,0,64,0,0,0,4,0,0,0,0,0,0,864,2,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,4100,8436,1024,12,0,0,1024,62480,32,3076,0,0,0,4100,8436,1024,12,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,1024,6144,4,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,12768,3072,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6144,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1024,0,0,1024,0,0,0,0,0,1024,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,4,0,0,0,4100,8436,1024,13,0,0,0,0,0,1024,0,0,0,0,0,17408,0,0,0,0,0,0,0,0,0,0,0,0,12768,3072,0,0,0,0,57344,49,12,0,0,0,0,2048,0,0,0,0,0,0,32,0,0,0,0,0,32768,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4100,8436,1024,12,0,0,1024,62480,32,3076,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,4,0,0,1024,62480,32,3332,0,0,0,0,0,0,32,0,0,0,0,0,64,0,0,0,0,0,14816,3072,0,0,0,0,0,1024,0,0,0,0,0,0,0,0,0,1024,0,0,1024,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,1024,0,0,1024,0,0,0,4,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,8192,0,0,0,0,0,1024,0,0,0,0,0,0,4,0,0,0,0,0,4,0,0,0,4100,8436,1024,13,0,0,0,0,0,64,16,0,0,0,0,0,0,0,0,1024,62480,32,3332,0,0,0,0,0,12768,3200,0,0,1024,62480,32,3332,0,0,0,0,0,0,4224,0,0,0,128,0,0,0,0,0,4100,8436,1024,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,3072,5,0,0,0,0,0,0,12768,19456,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1024,62480,32,3332,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1024,62480,32,3332,0,0,0,4,0,0,0,0,0,0,0,57344,32817,12,0,0,0,0,16384,0,0,0,0,0,0,0,0,0,0,4100,8436,1024,13,0,0,0,0,57344,57,12,0,0,0,0,0,0,0,0,0,0,57344,32817,12,0,0,0,0,0,0,0,0,32768,0,0,0,0,0,0,0,0,12768,3200,0,0,1024,62480,32,3332,0,0,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,14816,3072,0,0,0,0,64,0,0,0,0,0,0,45536,3072,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,1024,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,12768,19456,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1024,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4100,8436,1024,13,0,0,0,0,256,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,45536,3072,0,0,0,2,0,0,0,0,0,4100,8436,1024,13,0,0,0,0,57344,49,76,0,0,4100,8436,1024,13,0,0,0,0,57344,49,12,0,0,4100,8436,1024,13,0,0,0,0,57344,177,12,0,0,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,16384,0,0,0,0,32768,1024,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1024,0,0,0,4100,8436,1024,13,0,0,0,0,57344,49,12,0,0,0,0,2048,0,0,0,0,0,0,4096,0,0,0,0,0,1,0,0,0,0,0,0,64,0,0,0,4100,8436,1024,13,0,0,0,0,0,0,0,0,0,0,0,12768,3072,0,0,1024,62480,32,3332,0,0,0,0,0,12768,19456,0,0,1024,62480,32,3332,0,0,0,0,0,45536,3072,0,0,0,0,0,16384,0,0,0,0,0,1024,0,0,0,0,0,0,0,0,0
	])

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_runParser","AST","toplevels","toplevel","requireEnsures","invs","separates","conds","cond","bindings","binding","ty","qty","block","stmts","stmt","partition","range","spec","qspec","expr","cmpExpr","cmp","arithExpr","arith","atomic","many__cond__","many__stmt__","many__toplevel__","manyComma__binding__","manyComma__range__","opt__block__","tuple__expr__","manyComma__expr__","manyComma___binding__","manyComma___range__","many___cond__","many___stmt__","many___toplevel__","manyComma___expr__","digits","dafny","\"method\"","\"ensures\"","\"requires\"","\"separates\"","\"invariant\"","\"with\"","\"for\"","\"returns\"","\"not\"","\"nat\"","\"int\"","\"in\"","\"bool\"","\"seq\"","\"nor\"","\"had\"","\"H\"","\"QFT\"","\"RQFT\"","\"meas\"","\"ch\"","\"qreg\"","\"ch01\"","\"var\"","\"if\"","\"\955\"","\"\931\"","\"\8855\"","\"\8712\"","\"\8614\"","\"assert\"","\"||\"","\"&&\"","'+'","'-'","'*'","'\\%'","'|'","'('","')'","'<'","'>'","'['","']'","'{'","'}'","id","'_'","','","':'","'.'","';'","\"==\"","\"=>\"","\">=\"","\"<=\"","\":=\"","\"*=\"","\"..\"","%eof"]
        bit_start = st * 104
        bit_end = (st + 1) * 104
        read_bit = readArrayBit happyExpList
        bits = map read_bit [bit_start..bit_end - 1]
        bits_indexed = zip bits [0..103]
        token_strs_expected = concatMap f bits_indexed
        f (False, _) = []
        f (True, nr) = [token_strs !! nr]

action_0 (4) = happyGoto action_5
action_0 (5) = happyGoto action_2
action_0 (31) = happyGoto action_3
action_0 (41) = happyGoto action_4
action_0 _ = happyReduce_87

action_1 (5) = happyGoto action_2
action_1 (31) = happyGoto action_3
action_1 (41) = happyGoto action_4
action_1 _ = happyFail (happyExpListPerState 1)

action_2 _ = happyReduce_1

action_3 _ = happyReduce_2

action_4 (44) = happyShift action_7
action_4 (45) = happyShift action_8
action_4 (6) = happyGoto action_6
action_4 _ = happyReduce_70

action_5 (104) = happyAccept
action_5 _ = happyFail (happyExpListPerState 5)

action_6 _ = happyReduce_88

action_7 _ = happyReduce_3

action_8 (91) = happyShift action_9
action_8 _ = happyFail (happyExpListPerState 8)

action_9 (83) = happyShift action_10
action_9 _ = happyFail (happyExpListPerState 9)

action_10 (91) = happyShift action_15
action_10 (12) = happyGoto action_11
action_10 (13) = happyGoto action_12
action_10 (32) = happyGoto action_13
action_10 (37) = happyGoto action_14
action_10 _ = happyReduce_77

action_11 (84) = happyShift action_18
action_11 _ = happyFail (happyExpListPerState 11)

action_12 _ = happyReduce_78

action_13 _ = happyReduce_13

action_14 (93) = happyShift action_17
action_14 _ = happyReduce_71

action_15 (94) = happyShift action_16
action_15 _ = happyFail (happyExpListPerState 15)

action_16 (54) = happyShift action_26
action_16 (55) = happyShift action_27
action_16 (57) = happyShift action_28
action_16 (58) = happyShift action_29
action_16 (66) = happyShift action_30
action_16 (14) = happyGoto action_25
action_16 _ = happyFail (happyExpListPerState 16)

action_17 (91) = happyShift action_15
action_17 (13) = happyGoto action_24
action_17 _ = happyFail (happyExpListPerState 17)

action_18 (52) = happyShift action_23
action_18 (7) = happyGoto action_19
action_18 (10) = happyGoto action_20
action_18 (29) = happyGoto action_21
action_18 (39) = happyGoto action_22
action_18 _ = happyReduce_83

action_19 (89) = happyShift action_40
action_19 (16) = happyGoto action_38
action_19 (34) = happyGoto action_39
action_19 _ = happyReduce_73

action_20 _ = happyReduce_6

action_21 _ = happyReduce_9

action_22 (46) = happyShift action_35
action_22 (47) = happyShift action_36
action_22 (49) = happyShift action_37
action_22 (11) = happyGoto action_34
action_22 _ = happyReduce_68

action_23 (83) = happyShift action_33
action_23 _ = happyFail (happyExpListPerState 23)

action_24 _ = happyReduce_79

action_25 _ = happyReduce_14

action_26 _ = happyReduce_15

action_27 _ = happyReduce_16

action_28 _ = happyReduce_17

action_29 (85) = happyShift action_32
action_29 _ = happyFail (happyExpListPerState 29)

action_30 (87) = happyShift action_31
action_30 _ = happyFail (happyExpListPerState 30)

action_31 (43) = happyShift action_69
action_31 _ = happyFail (happyExpListPerState 31)

action_32 (54) = happyShift action_26
action_32 (55) = happyShift action_27
action_32 (57) = happyShift action_28
action_32 (58) = happyShift action_29
action_32 (66) = happyShift action_30
action_32 (14) = happyGoto action_68
action_32 _ = happyFail (happyExpListPerState 32)

action_33 (91) = happyShift action_15
action_33 (12) = happyGoto action_67
action_33 (13) = happyGoto action_12
action_33 (32) = happyGoto action_13
action_33 (37) = happyGoto action_14
action_33 _ = happyReduce_77

action_34 _ = happyReduce_84

action_35 (43) = happyShift action_53
action_35 (53) = happyShift action_54
action_35 (59) = happyShift action_55
action_35 (61) = happyShift action_56
action_35 (62) = happyShift action_57
action_35 (63) = happyShift action_58
action_35 (64) = happyShift action_59
action_35 (70) = happyShift action_60
action_35 (83) = happyShift action_61
action_35 (89) = happyShift action_62
action_35 (91) = happyShift action_63
action_35 (92) = happyShift action_64
action_35 (19) = happyGoto action_44
action_35 (20) = happyGoto action_45
action_35 (21) = happyGoto action_46
action_35 (23) = happyGoto action_66
action_35 (24) = happyGoto action_48
action_35 (26) = happyGoto action_49
action_35 (28) = happyGoto action_50
action_35 (33) = happyGoto action_51
action_35 (38) = happyGoto action_52
action_35 _ = happyReduce_80

action_36 (43) = happyShift action_53
action_36 (53) = happyShift action_54
action_36 (59) = happyShift action_55
action_36 (61) = happyShift action_56
action_36 (62) = happyShift action_57
action_36 (63) = happyShift action_58
action_36 (64) = happyShift action_59
action_36 (70) = happyShift action_60
action_36 (83) = happyShift action_61
action_36 (89) = happyShift action_62
action_36 (91) = happyShift action_63
action_36 (92) = happyShift action_64
action_36 (19) = happyGoto action_44
action_36 (20) = happyGoto action_45
action_36 (21) = happyGoto action_46
action_36 (23) = happyGoto action_65
action_36 (24) = happyGoto action_48
action_36 (26) = happyGoto action_49
action_36 (28) = happyGoto action_50
action_36 (33) = happyGoto action_51
action_36 (38) = happyGoto action_52
action_36 _ = happyReduce_80

action_37 (43) = happyShift action_53
action_37 (53) = happyShift action_54
action_37 (59) = happyShift action_55
action_37 (61) = happyShift action_56
action_37 (62) = happyShift action_57
action_37 (63) = happyShift action_58
action_37 (64) = happyShift action_59
action_37 (70) = happyShift action_60
action_37 (83) = happyShift action_61
action_37 (89) = happyShift action_62
action_37 (91) = happyShift action_63
action_37 (92) = happyShift action_64
action_37 (19) = happyGoto action_44
action_37 (20) = happyGoto action_45
action_37 (21) = happyGoto action_46
action_37 (23) = happyGoto action_47
action_37 (24) = happyGoto action_48
action_37 (26) = happyGoto action_49
action_37 (28) = happyGoto action_50
action_37 (33) = happyGoto action_51
action_37 (38) = happyGoto action_52
action_37 _ = happyReduce_80

action_38 _ = happyReduce_74

action_39 _ = happyReduce_4

action_40 (17) = happyGoto action_41
action_40 (30) = happyGoto action_42
action_40 (40) = happyGoto action_43
action_40 _ = happyReduce_85

action_41 (90) = happyShift action_103
action_41 _ = happyFail (happyExpListPerState 41)

action_42 _ = happyReduce_25

action_43 (51) = happyShift action_98
action_43 (68) = happyShift action_99
action_43 (69) = happyShift action_100
action_43 (75) = happyShift action_101
action_43 (91) = happyShift action_102
action_43 (93) = happyReduce_80
action_43 (102) = happyReduce_80
action_43 (18) = happyGoto action_96
action_43 (19) = happyGoto action_97
action_43 (20) = happyGoto action_45
action_43 (33) = happyGoto action_51
action_43 (38) = happyGoto action_52
action_43 _ = happyReduce_69

action_44 _ = happyReduce_42

action_45 _ = happyReduce_81

action_46 _ = happyReduce_41

action_47 (78) = happyShift action_75
action_47 (79) = happyShift action_76
action_47 (80) = happyShift action_77
action_47 (81) = happyShift action_78
action_47 (85) = happyShift action_79
action_47 (86) = happyShift action_80
action_47 (99) = happyShift action_81
action_47 (100) = happyShift action_82
action_47 (25) = happyGoto action_73
action_47 (27) = happyGoto action_74
action_47 _ = happyReduce_12

action_48 _ = happyReduce_53

action_49 _ = happyReduce_54

action_50 (76) = happyShift action_94
action_50 (77) = happyShift action_95
action_50 _ = happyReduce_39

action_51 _ = happyReduce_33

action_52 (93) = happyShift action_93
action_52 _ = happyReduce_72

action_53 _ = happyReduce_66

action_54 (43) = happyShift action_53
action_54 (91) = happyShift action_92
action_54 (28) = happyGoto action_91
action_54 _ = happyFail (happyExpListPerState 54)

action_55 (83) = happyShift action_90
action_55 _ = happyFail (happyExpListPerState 55)

action_56 _ = happyReduce_43

action_57 _ = happyReduce_44

action_58 _ = happyReduce_45

action_59 (91) = happyShift action_89
action_59 _ = happyFail (happyExpListPerState 59)

action_60 (83) = happyShift action_88
action_60 _ = happyFail (happyExpListPerState 60)

action_61 (43) = happyShift action_53
action_61 (53) = happyShift action_54
action_61 (59) = happyShift action_55
action_61 (61) = happyShift action_56
action_61 (62) = happyShift action_57
action_61 (63) = happyShift action_58
action_61 (64) = happyShift action_59
action_61 (70) = happyShift action_60
action_61 (83) = happyShift action_61
action_61 (89) = happyShift action_62
action_61 (91) = happyShift action_63
action_61 (92) = happyShift action_64
action_61 (19) = happyGoto action_44
action_61 (20) = happyGoto action_45
action_61 (21) = happyGoto action_46
action_61 (23) = happyGoto action_87
action_61 (24) = happyGoto action_48
action_61 (26) = happyGoto action_49
action_61 (28) = happyGoto action_50
action_61 (33) = happyGoto action_51
action_61 (38) = happyGoto action_52
action_61 _ = happyReduce_80

action_62 (91) = happyShift action_86
action_62 (19) = happyGoto action_85
action_62 (20) = happyGoto action_45
action_62 (33) = happyGoto action_51
action_62 (38) = happyGoto action_52
action_62 _ = happyReduce_80

action_63 (83) = happyShift action_83
action_63 (87) = happyShift action_84
action_63 _ = happyReduce_67

action_64 _ = happyReduce_40

action_65 (78) = happyShift action_75
action_65 (79) = happyShift action_76
action_65 (80) = happyShift action_77
action_65 (81) = happyShift action_78
action_65 (85) = happyShift action_79
action_65 (86) = happyShift action_80
action_65 (99) = happyShift action_81
action_65 (100) = happyShift action_82
action_65 (25) = happyGoto action_73
action_65 (27) = happyGoto action_74
action_65 _ = happyReduce_10

action_66 (78) = happyShift action_75
action_66 (79) = happyShift action_76
action_66 (80) = happyShift action_77
action_66 (81) = happyShift action_78
action_66 (85) = happyShift action_79
action_66 (86) = happyShift action_80
action_66 (99) = happyShift action_81
action_66 (100) = happyShift action_82
action_66 (25) = happyGoto action_73
action_66 (27) = happyGoto action_74
action_66 _ = happyReduce_11

action_67 (84) = happyShift action_72
action_67 _ = happyFail (happyExpListPerState 67)

action_68 (86) = happyShift action_71
action_68 _ = happyFail (happyExpListPerState 68)

action_69 (88) = happyShift action_70
action_69 _ = happyFail (happyExpListPerState 69)

action_70 _ = happyReduce_19

action_71 _ = happyReduce_18

action_72 (7) = happyGoto action_121
action_72 (10) = happyGoto action_20
action_72 (29) = happyGoto action_21
action_72 (39) = happyGoto action_22
action_72 _ = happyReduce_83

action_73 (43) = happyShift action_53
action_73 (53) = happyShift action_54
action_73 (59) = happyShift action_55
action_73 (61) = happyShift action_56
action_73 (62) = happyShift action_57
action_73 (63) = happyShift action_58
action_73 (64) = happyShift action_59
action_73 (70) = happyShift action_60
action_73 (83) = happyShift action_61
action_73 (89) = happyShift action_62
action_73 (91) = happyShift action_63
action_73 (92) = happyShift action_64
action_73 (19) = happyGoto action_44
action_73 (20) = happyGoto action_45
action_73 (21) = happyGoto action_46
action_73 (23) = happyGoto action_120
action_73 (24) = happyGoto action_48
action_73 (26) = happyGoto action_49
action_73 (28) = happyGoto action_50
action_73 (33) = happyGoto action_51
action_73 (38) = happyGoto action_52
action_73 _ = happyReduce_80

action_74 (43) = happyShift action_53
action_74 (53) = happyShift action_54
action_74 (59) = happyShift action_55
action_74 (61) = happyShift action_56
action_74 (62) = happyShift action_57
action_74 (63) = happyShift action_58
action_74 (64) = happyShift action_59
action_74 (70) = happyShift action_60
action_74 (83) = happyShift action_61
action_74 (89) = happyShift action_62
action_74 (91) = happyShift action_63
action_74 (92) = happyShift action_64
action_74 (19) = happyGoto action_44
action_74 (20) = happyGoto action_45
action_74 (21) = happyGoto action_46
action_74 (23) = happyGoto action_119
action_74 (24) = happyGoto action_48
action_74 (26) = happyGoto action_49
action_74 (28) = happyGoto action_50
action_74 (33) = happyGoto action_51
action_74 (38) = happyGoto action_52
action_74 _ = happyReduce_80

action_75 _ = happyReduce_62

action_76 _ = happyReduce_63

action_77 _ = happyReduce_64

action_78 _ = happyReduce_65

action_79 _ = happyReduce_58

action_80 _ = happyReduce_57

action_81 _ = happyReduce_59

action_82 _ = happyReduce_60

action_83 (43) = happyShift action_53
action_83 (91) = happyShift action_92
action_83 (28) = happyGoto action_118
action_83 _ = happyFail (happyExpListPerState 83)

action_84 (43) = happyShift action_53
action_84 (53) = happyShift action_54
action_84 (59) = happyShift action_55
action_84 (61) = happyShift action_56
action_84 (62) = happyShift action_57
action_84 (63) = happyShift action_58
action_84 (64) = happyShift action_59
action_84 (70) = happyShift action_60
action_84 (83) = happyShift action_61
action_84 (89) = happyShift action_62
action_84 (91) = happyShift action_63
action_84 (92) = happyShift action_64
action_84 (19) = happyGoto action_44
action_84 (20) = happyGoto action_45
action_84 (21) = happyGoto action_46
action_84 (23) = happyGoto action_117
action_84 (24) = happyGoto action_48
action_84 (26) = happyGoto action_49
action_84 (28) = happyGoto action_50
action_84 (33) = happyGoto action_51
action_84 (38) = happyGoto action_52
action_84 _ = happyReduce_80

action_85 (94) = happyShift action_116
action_85 _ = happyFail (happyExpListPerState 85)

action_86 (87) = happyShift action_84
action_86 _ = happyFail (happyExpListPerState 86)

action_87 (78) = happyShift action_75
action_87 (79) = happyShift action_76
action_87 (80) = happyShift action_77
action_87 (81) = happyShift action_78
action_87 (84) = happyShift action_115
action_87 (85) = happyShift action_79
action_87 (86) = happyShift action_80
action_87 (99) = happyShift action_81
action_87 (100) = happyShift action_82
action_87 (25) = happyGoto action_73
action_87 (27) = happyGoto action_74
action_87 _ = happyFail (happyExpListPerState 87)

action_88 (91) = happyShift action_114
action_88 _ = happyFail (happyExpListPerState 88)

action_89 _ = happyReduce_46

action_90 (43) = happyShift action_53
action_90 (91) = happyShift action_92
action_90 (28) = happyGoto action_113
action_90 _ = happyFail (happyExpListPerState 90)

action_91 _ = happyReduce_47

action_92 _ = happyReduce_67

action_93 (91) = happyShift action_86
action_93 (20) = happyGoto action_112
action_93 _ = happyFail (happyExpListPerState 93)

action_94 (43) = happyShift action_53
action_94 (91) = happyShift action_92
action_94 (28) = happyGoto action_111
action_94 _ = happyFail (happyExpListPerState 94)

action_95 (43) = happyShift action_53
action_95 (91) = happyShift action_92
action_95 (28) = happyGoto action_110
action_95 _ = happyFail (happyExpListPerState 95)

action_96 _ = happyReduce_86

action_97 (102) = happyShift action_109
action_97 _ = happyFail (happyExpListPerState 97)

action_98 (91) = happyShift action_108
action_98 _ = happyFail (happyExpListPerState 98)

action_99 (91) = happyShift action_15
action_99 (13) = happyGoto action_107
action_99 _ = happyFail (happyExpListPerState 99)

action_100 (83) = happyShift action_106
action_100 _ = happyFail (happyExpListPerState 100)

action_101 (43) = happyShift action_53
action_101 (53) = happyShift action_54
action_101 (59) = happyShift action_55
action_101 (61) = happyShift action_56
action_101 (62) = happyShift action_57
action_101 (63) = happyShift action_58
action_101 (64) = happyShift action_59
action_101 (70) = happyShift action_60
action_101 (83) = happyShift action_61
action_101 (89) = happyShift action_62
action_101 (91) = happyShift action_63
action_101 (92) = happyShift action_64
action_101 (19) = happyGoto action_44
action_101 (20) = happyGoto action_45
action_101 (21) = happyGoto action_46
action_101 (23) = happyGoto action_105
action_101 (24) = happyGoto action_48
action_101 (26) = happyGoto action_49
action_101 (28) = happyGoto action_50
action_101 (33) = happyGoto action_51
action_101 (38) = happyGoto action_52
action_101 _ = happyReduce_80

action_102 (87) = happyShift action_84
action_102 (101) = happyShift action_104
action_102 _ = happyFail (happyExpListPerState 102)

action_103 _ = happyReduce_24

action_104 (43) = happyShift action_53
action_104 (53) = happyShift action_54
action_104 (59) = happyShift action_55
action_104 (61) = happyShift action_56
action_104 (62) = happyShift action_57
action_104 (63) = happyShift action_58
action_104 (64) = happyShift action_59
action_104 (70) = happyShift action_60
action_104 (83) = happyShift action_61
action_104 (89) = happyShift action_62
action_104 (91) = happyShift action_63
action_104 (92) = happyShift action_64
action_104 (19) = happyGoto action_44
action_104 (20) = happyGoto action_45
action_104 (21) = happyGoto action_46
action_104 (23) = happyGoto action_138
action_104 (24) = happyGoto action_48
action_104 (26) = happyGoto action_49
action_104 (28) = happyGoto action_50
action_104 (33) = happyGoto action_51
action_104 (38) = happyGoto action_52
action_104 _ = happyReduce_80

action_105 (78) = happyShift action_75
action_105 (79) = happyShift action_76
action_105 (80) = happyShift action_77
action_105 (81) = happyShift action_78
action_105 (85) = happyShift action_79
action_105 (86) = happyShift action_80
action_105 (96) = happyShift action_137
action_105 (99) = happyShift action_81
action_105 (100) = happyShift action_82
action_105 (25) = happyGoto action_73
action_105 (27) = happyGoto action_74
action_105 _ = happyFail (happyExpListPerState 105)

action_106 (43) = happyShift action_53
action_106 (53) = happyShift action_54
action_106 (59) = happyShift action_55
action_106 (61) = happyShift action_56
action_106 (62) = happyShift action_57
action_106 (63) = happyShift action_58
action_106 (64) = happyShift action_59
action_106 (70) = happyShift action_60
action_106 (83) = happyShift action_61
action_106 (89) = happyShift action_62
action_106 (91) = happyShift action_63
action_106 (92) = happyShift action_64
action_106 (19) = happyGoto action_44
action_106 (20) = happyGoto action_45
action_106 (21) = happyGoto action_46
action_106 (23) = happyGoto action_136
action_106 (24) = happyGoto action_48
action_106 (26) = happyGoto action_49
action_106 (28) = happyGoto action_50
action_106 (33) = happyGoto action_51
action_106 (38) = happyGoto action_52
action_106 _ = happyReduce_80

action_107 (96) = happyShift action_134
action_107 (101) = happyShift action_135
action_107 _ = happyFail (happyExpListPerState 107)

action_108 (56) = happyShift action_133
action_108 _ = happyFail (happyExpListPerState 108)

action_109 (43) = happyShift action_53
action_109 (53) = happyShift action_54
action_109 (59) = happyShift action_55
action_109 (61) = happyShift action_56
action_109 (62) = happyShift action_57
action_109 (63) = happyShift action_58
action_109 (64) = happyShift action_59
action_109 (70) = happyShift action_60
action_109 (83) = happyShift action_61
action_109 (89) = happyShift action_62
action_109 (91) = happyShift action_63
action_109 (92) = happyShift action_64
action_109 (19) = happyGoto action_44
action_109 (20) = happyGoto action_45
action_109 (21) = happyGoto action_46
action_109 (23) = happyGoto action_132
action_109 (24) = happyGoto action_48
action_109 (26) = happyGoto action_49
action_109 (28) = happyGoto action_50
action_109 (33) = happyGoto action_51
action_109 (38) = happyGoto action_52
action_109 _ = happyReduce_80

action_110 _ = happyReduce_51

action_111 _ = happyReduce_52

action_112 _ = happyReduce_82

action_113 (93) = happyShift action_131
action_113 _ = happyFail (happyExpListPerState 113)

action_114 (98) = happyShift action_130
action_114 _ = happyFail (happyExpListPerState 114)

action_115 _ = happyReduce_55

action_116 (59) = happyShift action_126
action_116 (60) = happyShift action_127
action_116 (65) = happyShift action_128
action_116 (67) = happyShift action_129
action_116 (15) = happyGoto action_125
action_116 _ = happyFail (happyExpListPerState 116)

action_117 (78) = happyShift action_75
action_117 (79) = happyShift action_76
action_117 (80) = happyShift action_77
action_117 (81) = happyShift action_78
action_117 (85) = happyShift action_79
action_117 (86) = happyShift action_80
action_117 (99) = happyShift action_81
action_117 (100) = happyShift action_82
action_117 (103) = happyShift action_124
action_117 (25) = happyGoto action_73
action_117 (27) = happyGoto action_74
action_117 _ = happyFail (happyExpListPerState 117)

action_118 (84) = happyShift action_123
action_118 _ = happyFail (happyExpListPerState 118)

action_119 (78) = happyShift action_75
action_119 (79) = happyShift action_76
action_119 (80) = happyShift action_77
action_119 (81) = happyShift action_78
action_119 (85) = happyShift action_79
action_119 (86) = happyShift action_80
action_119 (99) = happyShift action_81
action_119 (100) = happyShift action_82
action_119 (25) = happyGoto action_73
action_119 (27) = happyGoto action_74
action_119 _ = happyReduce_61

action_120 (78) = happyShift action_75
action_120 (79) = happyShift action_76
action_120 (80) = happyShift action_77
action_120 (81) = happyShift action_78
action_120 (85) = happyShift action_79
action_120 (86) = happyShift action_80
action_120 (99) = happyShift action_81
action_120 (100) = happyShift action_82
action_120 (25) = happyGoto action_73
action_120 (27) = happyGoto action_74
action_120 _ = happyReduce_56

action_121 (89) = happyShift action_40
action_121 (16) = happyGoto action_38
action_121 (34) = happyGoto action_122
action_121 _ = happyReduce_73

action_122 _ = happyReduce_5

action_123 _ = happyReduce_50

action_124 (43) = happyShift action_53
action_124 (53) = happyShift action_54
action_124 (59) = happyShift action_55
action_124 (61) = happyShift action_56
action_124 (62) = happyShift action_57
action_124 (63) = happyShift action_58
action_124 (64) = happyShift action_59
action_124 (70) = happyShift action_60
action_124 (83) = happyShift action_61
action_124 (89) = happyShift action_62
action_124 (91) = happyShift action_63
action_124 (92) = happyShift action_64
action_124 (19) = happyGoto action_44
action_124 (20) = happyGoto action_45
action_124 (21) = happyGoto action_46
action_124 (23) = happyGoto action_147
action_124 (24) = happyGoto action_48
action_124 (26) = happyGoto action_49
action_124 (28) = happyGoto action_50
action_124 (33) = happyGoto action_51
action_124 (38) = happyGoto action_52
action_124 _ = happyReduce_80

action_125 (74) = happyShift action_146
action_125 _ = happyFail (happyExpListPerState 125)

action_126 _ = happyReduce_20

action_127 _ = happyReduce_21

action_128 _ = happyReduce_22

action_129 _ = happyReduce_23

action_130 (43) = happyShift action_53
action_130 (53) = happyShift action_54
action_130 (59) = happyShift action_55
action_130 (61) = happyShift action_56
action_130 (62) = happyShift action_57
action_130 (63) = happyShift action_58
action_130 (64) = happyShift action_59
action_130 (70) = happyShift action_60
action_130 (83) = happyShift action_61
action_130 (89) = happyShift action_62
action_130 (91) = happyShift action_63
action_130 (92) = happyShift action_64
action_130 (19) = happyGoto action_44
action_130 (20) = happyGoto action_45
action_130 (21) = happyGoto action_46
action_130 (23) = happyGoto action_145
action_130 (24) = happyGoto action_48
action_130 (26) = happyGoto action_49
action_130 (28) = happyGoto action_50
action_130 (33) = happyGoto action_51
action_130 (38) = happyGoto action_52
action_130 _ = happyReduce_80

action_131 (43) = happyShift action_144
action_131 _ = happyFail (happyExpListPerState 131)

action_132 (78) = happyShift action_75
action_132 (79) = happyShift action_76
action_132 (80) = happyShift action_77
action_132 (81) = happyShift action_78
action_132 (85) = happyShift action_79
action_132 (86) = happyShift action_80
action_132 (96) = happyShift action_143
action_132 (99) = happyShift action_81
action_132 (100) = happyShift action_82
action_132 (25) = happyGoto action_73
action_132 (27) = happyGoto action_74
action_132 _ = happyFail (happyExpListPerState 132)

action_133 (87) = happyShift action_142
action_133 _ = happyFail (happyExpListPerState 133)

action_134 _ = happyReduce_27

action_135 (43) = happyShift action_53
action_135 (53) = happyShift action_54
action_135 (59) = happyShift action_55
action_135 (61) = happyShift action_56
action_135 (62) = happyShift action_57
action_135 (63) = happyShift action_58
action_135 (64) = happyShift action_59
action_135 (70) = happyShift action_60
action_135 (83) = happyShift action_61
action_135 (89) = happyShift action_62
action_135 (91) = happyShift action_63
action_135 (92) = happyShift action_64
action_135 (19) = happyGoto action_44
action_135 (20) = happyGoto action_45
action_135 (21) = happyGoto action_46
action_135 (23) = happyGoto action_141
action_135 (24) = happyGoto action_48
action_135 (26) = happyGoto action_49
action_135 (28) = happyGoto action_50
action_135 (33) = happyGoto action_51
action_135 (38) = happyGoto action_52
action_135 _ = happyReduce_80

action_136 (78) = happyShift action_75
action_136 (79) = happyShift action_76
action_136 (80) = happyShift action_77
action_136 (81) = happyShift action_78
action_136 (84) = happyShift action_140
action_136 (85) = happyShift action_79
action_136 (86) = happyShift action_80
action_136 (99) = happyShift action_81
action_136 (100) = happyShift action_82
action_136 (25) = happyGoto action_73
action_136 (27) = happyGoto action_74
action_136 _ = happyFail (happyExpListPerState 136)

action_137 _ = happyReduce_26

action_138 (78) = happyShift action_75
action_138 (79) = happyShift action_76
action_138 (80) = happyShift action_77
action_138 (81) = happyShift action_78
action_138 (85) = happyShift action_79
action_138 (86) = happyShift action_80
action_138 (96) = happyShift action_139
action_138 (99) = happyShift action_81
action_138 (100) = happyShift action_82
action_138 (25) = happyGoto action_73
action_138 (27) = happyGoto action_74
action_138 _ = happyFail (happyExpListPerState 138)

action_139 _ = happyReduce_29

action_140 (48) = happyShift action_156
action_140 (9) = happyGoto action_155
action_140 _ = happyFail (happyExpListPerState 140)

action_141 (78) = happyShift action_75
action_141 (79) = happyShift action_76
action_141 (80) = happyShift action_77
action_141 (81) = happyShift action_78
action_141 (85) = happyShift action_79
action_141 (86) = happyShift action_80
action_141 (96) = happyShift action_154
action_141 (99) = happyShift action_81
action_141 (100) = happyShift action_82
action_141 (25) = happyGoto action_73
action_141 (27) = happyGoto action_74
action_141 _ = happyFail (happyExpListPerState 141)

action_142 (43) = happyShift action_53
action_142 (53) = happyShift action_54
action_142 (59) = happyShift action_55
action_142 (61) = happyShift action_56
action_142 (62) = happyShift action_57
action_142 (63) = happyShift action_58
action_142 (64) = happyShift action_59
action_142 (70) = happyShift action_60
action_142 (83) = happyShift action_61
action_142 (89) = happyShift action_62
action_142 (91) = happyShift action_63
action_142 (92) = happyShift action_64
action_142 (19) = happyGoto action_44
action_142 (20) = happyGoto action_45
action_142 (21) = happyGoto action_46
action_142 (23) = happyGoto action_153
action_142 (24) = happyGoto action_48
action_142 (26) = happyGoto action_49
action_142 (28) = happyGoto action_50
action_142 (33) = happyGoto action_51
action_142 (38) = happyGoto action_52
action_142 _ = happyReduce_80

action_143 _ = happyReduce_30

action_144 (84) = happyShift action_152
action_144 _ = happyFail (happyExpListPerState 144)

action_145 (78) = happyShift action_75
action_145 (79) = happyShift action_76
action_145 (80) = happyShift action_77
action_145 (81) = happyShift action_78
action_145 (84) = happyShift action_151
action_145 (85) = happyShift action_79
action_145 (86) = happyShift action_80
action_145 (99) = happyShift action_81
action_145 (100) = happyShift action_82
action_145 (25) = happyGoto action_73
action_145 (27) = happyGoto action_74
action_145 _ = happyFail (happyExpListPerState 145)

action_146 (71) = happyShift action_150
action_146 (22) = happyGoto action_149
action_146 _ = happyReduce_38

action_147 (78) = happyShift action_75
action_147 (79) = happyShift action_76
action_147 (80) = happyShift action_77
action_147 (81) = happyShift action_78
action_147 (85) = happyShift action_79
action_147 (86) = happyShift action_80
action_147 (88) = happyShift action_148
action_147 (99) = happyShift action_81
action_147 (100) = happyShift action_82
action_147 (25) = happyGoto action_73
action_147 (27) = happyGoto action_74
action_147 _ = happyFail (happyExpListPerState 147)

action_148 _ = happyReduce_34

action_149 (90) = happyShift action_161
action_149 _ = happyFail (happyExpListPerState 149)

action_150 (91) = happyShift action_160
action_150 _ = happyFail (happyExpListPerState 150)

action_151 _ = happyReduce_49

action_152 _ = happyReduce_48

action_153 (78) = happyShift action_75
action_153 (79) = happyShift action_76
action_153 (80) = happyShift action_77
action_153 (81) = happyShift action_78
action_153 (85) = happyShift action_79
action_153 (86) = happyShift action_80
action_153 (99) = happyShift action_81
action_153 (100) = happyShift action_82
action_153 (103) = happyShift action_159
action_153 (25) = happyGoto action_73
action_153 (27) = happyGoto action_74
action_153 _ = happyFail (happyExpListPerState 153)

action_154 _ = happyReduce_28

action_155 (89) = happyShift action_40
action_155 (16) = happyGoto action_158
action_155 _ = happyFail (happyExpListPerState 155)

action_156 (91) = happyShift action_86
action_156 (19) = happyGoto action_157
action_156 (20) = happyGoto action_45
action_156 (33) = happyGoto action_51
action_156 (38) = happyGoto action_52
action_156 _ = happyReduce_80

action_157 _ = happyReduce_8

action_158 _ = happyReduce_31

action_159 (43) = happyShift action_53
action_159 (53) = happyShift action_54
action_159 (59) = happyShift action_55
action_159 (61) = happyShift action_56
action_159 (62) = happyShift action_57
action_159 (63) = happyShift action_58
action_159 (64) = happyShift action_59
action_159 (70) = happyShift action_60
action_159 (83) = happyShift action_61
action_159 (89) = happyShift action_62
action_159 (91) = happyShift action_63
action_159 (92) = happyShift action_64
action_159 (19) = happyGoto action_44
action_159 (20) = happyGoto action_45
action_159 (21) = happyGoto action_46
action_159 (23) = happyGoto action_163
action_159 (24) = happyGoto action_48
action_159 (26) = happyGoto action_49
action_159 (28) = happyGoto action_50
action_159 (33) = happyGoto action_51
action_159 (38) = happyGoto action_52
action_159 _ = happyReduce_80

action_160 (73) = happyShift action_162
action_160 _ = happyFail (happyExpListPerState 160)

action_161 _ = happyReduce_35

action_162 (87) = happyShift action_165
action_162 _ = happyFail (happyExpListPerState 162)

action_163 (78) = happyShift action_75
action_163 (79) = happyShift action_76
action_163 (80) = happyShift action_77
action_163 (81) = happyShift action_78
action_163 (85) = happyShift action_79
action_163 (86) = happyShift action_80
action_163 (88) = happyShift action_164
action_163 (99) = happyShift action_81
action_163 (100) = happyShift action_82
action_163 (25) = happyGoto action_73
action_163 (27) = happyGoto action_74
action_163 _ = happyFail (happyExpListPerState 163)

action_164 (50) = happyShift action_167
action_164 _ = happyFail (happyExpListPerState 164)

action_165 (43) = happyShift action_53
action_165 (53) = happyShift action_54
action_165 (59) = happyShift action_55
action_165 (61) = happyShift action_56
action_165 (62) = happyShift action_57
action_165 (63) = happyShift action_58
action_165 (64) = happyShift action_59
action_165 (70) = happyShift action_60
action_165 (83) = happyShift action_61
action_165 (89) = happyShift action_62
action_165 (91) = happyShift action_63
action_165 (92) = happyShift action_64
action_165 (19) = happyGoto action_44
action_165 (20) = happyGoto action_45
action_165 (21) = happyGoto action_46
action_165 (23) = happyGoto action_166
action_165 (24) = happyGoto action_48
action_165 (26) = happyGoto action_49
action_165 (28) = happyGoto action_50
action_165 (33) = happyGoto action_51
action_165 (38) = happyGoto action_52
action_165 _ = happyReduce_80

action_166 (78) = happyShift action_75
action_166 (79) = happyShift action_76
action_166 (80) = happyShift action_77
action_166 (81) = happyShift action_78
action_166 (85) = happyShift action_79
action_166 (86) = happyShift action_80
action_166 (99) = happyShift action_81
action_166 (100) = happyShift action_82
action_166 (103) = happyShift action_169
action_166 (25) = happyGoto action_73
action_166 (27) = happyGoto action_74
action_166 _ = happyFail (happyExpListPerState 166)

action_167 (43) = happyShift action_53
action_167 (53) = happyShift action_54
action_167 (59) = happyShift action_55
action_167 (61) = happyShift action_56
action_167 (62) = happyShift action_57
action_167 (63) = happyShift action_58
action_167 (64) = happyShift action_59
action_167 (70) = happyShift action_60
action_167 (83) = happyShift action_61
action_167 (89) = happyShift action_62
action_167 (91) = happyShift action_63
action_167 (92) = happyShift action_64
action_167 (19) = happyGoto action_44
action_167 (20) = happyGoto action_45
action_167 (21) = happyGoto action_46
action_167 (23) = happyGoto action_168
action_167 (24) = happyGoto action_48
action_167 (26) = happyGoto action_49
action_167 (28) = happyGoto action_50
action_167 (33) = happyGoto action_51
action_167 (38) = happyGoto action_52
action_167 _ = happyReduce_80

action_168 (78) = happyShift action_75
action_168 (79) = happyShift action_76
action_168 (80) = happyShift action_77
action_168 (81) = happyShift action_78
action_168 (85) = happyShift action_79
action_168 (86) = happyShift action_80
action_168 (99) = happyShift action_81
action_168 (100) = happyShift action_82
action_168 (8) = happyGoto action_171
action_168 (10) = happyGoto action_172
action_168 (25) = happyGoto action_73
action_168 (27) = happyGoto action_74
action_168 (29) = happyGoto action_21
action_168 (39) = happyGoto action_22
action_168 _ = happyReduce_83

action_169 (43) = happyShift action_53
action_169 (53) = happyShift action_54
action_169 (59) = happyShift action_55
action_169 (61) = happyShift action_56
action_169 (62) = happyShift action_57
action_169 (63) = happyShift action_58
action_169 (64) = happyShift action_59
action_169 (70) = happyShift action_60
action_169 (83) = happyShift action_61
action_169 (89) = happyShift action_62
action_169 (91) = happyShift action_63
action_169 (92) = happyShift action_64
action_169 (19) = happyGoto action_44
action_169 (20) = happyGoto action_45
action_169 (21) = happyGoto action_46
action_169 (23) = happyGoto action_170
action_169 (24) = happyGoto action_48
action_169 (26) = happyGoto action_49
action_169 (28) = happyGoto action_50
action_169 (33) = happyGoto action_51
action_169 (38) = happyGoto action_52
action_169 _ = happyReduce_80

action_170 (78) = happyShift action_75
action_170 (79) = happyShift action_76
action_170 (80) = happyShift action_77
action_170 (81) = happyShift action_78
action_170 (85) = happyShift action_79
action_170 (86) = happyShift action_80
action_170 (88) = happyShift action_174
action_170 (99) = happyShift action_81
action_170 (100) = happyShift action_82
action_170 (25) = happyGoto action_73
action_170 (27) = happyGoto action_74
action_170 _ = happyFail (happyExpListPerState 170)

action_171 (48) = happyShift action_156
action_171 (9) = happyGoto action_173
action_171 _ = happyFail (happyExpListPerState 171)

action_172 _ = happyReduce_7

action_173 (89) = happyShift action_40
action_173 (16) = happyGoto action_176
action_173 _ = happyFail (happyExpListPerState 173)

action_174 (95) = happyShift action_175
action_174 _ = happyFail (happyExpListPerState 174)

action_175 (72) = happyShift action_178
action_175 (83) = happyShift action_179
action_175 (35) = happyGoto action_177
action_175 _ = happyFail (happyExpListPerState 175)

action_176 _ = happyReduce_32

action_177 _ = happyReduce_36

action_178 (91) = happyShift action_183
action_178 _ = happyFail (happyExpListPerState 178)

action_179 (43) = happyShift action_53
action_179 (53) = happyShift action_54
action_179 (59) = happyShift action_55
action_179 (61) = happyShift action_56
action_179 (62) = happyShift action_57
action_179 (63) = happyShift action_58
action_179 (64) = happyShift action_59
action_179 (70) = happyShift action_60
action_179 (83) = happyShift action_61
action_179 (84) = happyReduce_89
action_179 (89) = happyShift action_62
action_179 (91) = happyShift action_63
action_179 (92) = happyShift action_64
action_179 (93) = happyReduce_89
action_179 (19) = happyGoto action_44
action_179 (20) = happyGoto action_45
action_179 (21) = happyGoto action_46
action_179 (23) = happyGoto action_180
action_179 (24) = happyGoto action_48
action_179 (26) = happyGoto action_49
action_179 (28) = happyGoto action_50
action_179 (33) = happyGoto action_51
action_179 (36) = happyGoto action_181
action_179 (38) = happyGoto action_52
action_179 (42) = happyGoto action_182
action_179 _ = happyReduce_80

action_180 (78) = happyShift action_75
action_180 (79) = happyShift action_76
action_180 (80) = happyShift action_77
action_180 (81) = happyShift action_78
action_180 (85) = happyShift action_79
action_180 (86) = happyShift action_80
action_180 (99) = happyShift action_81
action_180 (100) = happyShift action_82
action_180 (25) = happyGoto action_73
action_180 (27) = happyGoto action_74
action_180 _ = happyReduce_90

action_181 (84) = happyShift action_186
action_181 _ = happyFail (happyExpListPerState 181)

action_182 (93) = happyShift action_185
action_182 _ = happyReduce_76

action_183 (73) = happyShift action_184
action_183 _ = happyFail (happyExpListPerState 183)

action_184 (87) = happyShift action_188
action_184 _ = happyFail (happyExpListPerState 184)

action_185 (43) = happyShift action_53
action_185 (53) = happyShift action_54
action_185 (59) = happyShift action_55
action_185 (61) = happyShift action_56
action_185 (62) = happyShift action_57
action_185 (63) = happyShift action_58
action_185 (64) = happyShift action_59
action_185 (70) = happyShift action_60
action_185 (83) = happyShift action_61
action_185 (89) = happyShift action_62
action_185 (91) = happyShift action_63
action_185 (92) = happyShift action_64
action_185 (19) = happyGoto action_44
action_185 (20) = happyGoto action_45
action_185 (21) = happyGoto action_46
action_185 (23) = happyGoto action_187
action_185 (24) = happyGoto action_48
action_185 (26) = happyGoto action_49
action_185 (28) = happyGoto action_50
action_185 (33) = happyGoto action_51
action_185 (38) = happyGoto action_52
action_185 _ = happyReduce_80

action_186 _ = happyReduce_75

action_187 (78) = happyShift action_75
action_187 (79) = happyShift action_76
action_187 (80) = happyShift action_77
action_187 (81) = happyShift action_78
action_187 (85) = happyShift action_79
action_187 (86) = happyShift action_80
action_187 (99) = happyShift action_81
action_187 (100) = happyShift action_82
action_187 (25) = happyGoto action_73
action_187 (27) = happyGoto action_74
action_187 _ = happyReduce_91

action_188 (43) = happyShift action_53
action_188 (53) = happyShift action_54
action_188 (59) = happyShift action_55
action_188 (61) = happyShift action_56
action_188 (62) = happyShift action_57
action_188 (63) = happyShift action_58
action_188 (64) = happyShift action_59
action_188 (70) = happyShift action_60
action_188 (83) = happyShift action_61
action_188 (89) = happyShift action_62
action_188 (91) = happyShift action_63
action_188 (92) = happyShift action_64
action_188 (19) = happyGoto action_44
action_188 (20) = happyGoto action_45
action_188 (21) = happyGoto action_46
action_188 (23) = happyGoto action_189
action_188 (24) = happyGoto action_48
action_188 (26) = happyGoto action_49
action_188 (28) = happyGoto action_50
action_188 (33) = happyGoto action_51
action_188 (38) = happyGoto action_52
action_188 _ = happyReduce_80

action_189 (78) = happyShift action_75
action_189 (79) = happyShift action_76
action_189 (80) = happyShift action_77
action_189 (81) = happyShift action_78
action_189 (85) = happyShift action_79
action_189 (86) = happyShift action_80
action_189 (99) = happyShift action_81
action_189 (100) = happyShift action_82
action_189 (103) = happyShift action_190
action_189 (25) = happyGoto action_73
action_189 (27) = happyGoto action_74
action_189 _ = happyFail (happyExpListPerState 189)

action_190 (43) = happyShift action_53
action_190 (53) = happyShift action_54
action_190 (59) = happyShift action_55
action_190 (61) = happyShift action_56
action_190 (62) = happyShift action_57
action_190 (63) = happyShift action_58
action_190 (64) = happyShift action_59
action_190 (70) = happyShift action_60
action_190 (83) = happyShift action_61
action_190 (89) = happyShift action_62
action_190 (91) = happyShift action_63
action_190 (92) = happyShift action_64
action_190 (19) = happyGoto action_44
action_190 (20) = happyGoto action_45
action_190 (21) = happyGoto action_46
action_190 (23) = happyGoto action_191
action_190 (24) = happyGoto action_48
action_190 (26) = happyGoto action_49
action_190 (28) = happyGoto action_50
action_190 (33) = happyGoto action_51
action_190 (38) = happyGoto action_52
action_190 _ = happyReduce_80

action_191 (78) = happyShift action_75
action_191 (79) = happyShift action_76
action_191 (80) = happyShift action_77
action_191 (81) = happyShift action_78
action_191 (85) = happyShift action_79
action_191 (86) = happyShift action_80
action_191 (88) = happyShift action_192
action_191 (99) = happyShift action_81
action_191 (100) = happyShift action_82
action_191 (25) = happyGoto action_73
action_191 (27) = happyGoto action_74
action_191 _ = happyFail (happyExpListPerState 191)

action_192 (95) = happyShift action_193
action_192 _ = happyFail (happyExpListPerState 192)

action_193 (83) = happyShift action_179
action_193 (35) = happyGoto action_194
action_193 _ = happyFail (happyExpListPerState 193)

action_194 _ = happyReduce_37

happyReduce_1 = happySpecReduce_1  4 happyReduction_1
happyReduction_1 (HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn4
		 (reverse happy_var_1
	)
happyReduction_1 _  = notHappyAtAll 

happyReduce_2 = happySpecReduce_1  5 happyReduction_2
happyReduction_2 (HappyAbsSyn31  happy_var_1)
	 =  HappyAbsSyn5
		 (happy_var_1
	)
happyReduction_2 _  = notHappyAtAll 

happyReduce_3 = happySpecReduce_1  6 happyReduction_3
happyReduction_3 (HappyTerminal (( _, L.TDafny happy_var_1  )))
	 =  HappyAbsSyn6
		 (QDafny happy_var_1
	)
happyReduction_3 _  = notHappyAtAll 

happyReduce_4 = happyReduce 7 6 happyReduction_4
happyReduction_4 ((HappyAbsSyn34  happy_var_7) `HappyStk`
	(HappyAbsSyn7  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn12  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (( _, L.TId happy_var_2     ))) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn6
		 (let (rs, es) = happy_var_6 in                 
                                          QMethod happy_var_2 happy_var_4 [] rs es happy_var_7
	) `HappyStk` happyRest

happyReduce_5 = happyReduce 11 6 happyReduction_5
happyReduction_5 ((HappyAbsSyn34  happy_var_11) `HappyStk`
	(HappyAbsSyn7  happy_var_10) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn12  happy_var_8) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn12  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (( _, L.TId happy_var_2     ))) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn6
		 (let (rs, es) = happy_var_10 in                
                                          QMethod happy_var_2 happy_var_4 happy_var_8 rs es happy_var_11
	) `HappyStk` happyRest

happyReduce_6 = happySpecReduce_1  7 happyReduction_6
happyReduction_6 (HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn7
		 ((reverse [e | (Requires e) <- happy_var_1], 
                                         reverse [e | (Ensures  e) <- happy_var_1])
	)
happyReduction_6 _  = notHappyAtAll 

happyReduce_7 = happySpecReduce_1  8 happyReduction_7
happyReduction_7 (HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn8
		 (reverse [e | (Invariants e) <- happy_var_1]
	)
happyReduction_7 _  = notHappyAtAll 

happyReduce_8 = happySpecReduce_2  9 happyReduction_8
happyReduction_8 (HappyAbsSyn9  happy_var_2)
	_
	 =  HappyAbsSyn9
		 (happy_var_2
	)
happyReduction_8 _ _  = notHappyAtAll 

happyReduce_9 = happySpecReduce_1  10 happyReduction_9
happyReduction_9 (HappyAbsSyn29  happy_var_1)
	 =  HappyAbsSyn10
		 (happy_var_1
	)
happyReduction_9 _  = notHappyAtAll 

happyReduce_10 = happySpecReduce_2  11 happyReduction_10
happyReduction_10 (HappyAbsSyn23  happy_var_2)
	_
	 =  HappyAbsSyn11
		 (Requires happy_var_2
	)
happyReduction_10 _ _  = notHappyAtAll 

happyReduce_11 = happySpecReduce_2  11 happyReduction_11
happyReduction_11 (HappyAbsSyn23  happy_var_2)
	_
	 =  HappyAbsSyn11
		 (Ensures happy_var_2
	)
happyReduction_11 _ _  = notHappyAtAll 

happyReduce_12 = happySpecReduce_2  11 happyReduction_12
happyReduction_12 (HappyAbsSyn23  happy_var_2)
	_
	 =  HappyAbsSyn11
		 (Invariants happy_var_2
	)
happyReduction_12 _ _  = notHappyAtAll 

happyReduce_13 = happySpecReduce_1  12 happyReduction_13
happyReduction_13 (HappyAbsSyn32  happy_var_1)
	 =  HappyAbsSyn12
		 (happy_var_1
	)
happyReduction_13 _  = notHappyAtAll 

happyReduce_14 = happySpecReduce_3  13 happyReduction_14
happyReduction_14 (HappyAbsSyn14  happy_var_3)
	_
	(HappyTerminal (( _, L.TId happy_var_1     )))
	 =  HappyAbsSyn13
		 (Binding happy_var_1 happy_var_3
	)
happyReduction_14 _ _ _  = notHappyAtAll 

happyReduce_15 = happySpecReduce_1  14 happyReduction_15
happyReduction_15 _
	 =  HappyAbsSyn14
		 (TNat
	)

happyReduce_16 = happySpecReduce_1  14 happyReduction_16
happyReduction_16 _
	 =  HappyAbsSyn14
		 (TInt
	)

happyReduce_17 = happySpecReduce_1  14 happyReduction_17
happyReduction_17 _
	 =  HappyAbsSyn14
		 (TBool
	)

happyReduce_18 = happyReduce 4 14 happyReduction_18
happyReduction_18 (_ `HappyStk`
	(HappyAbsSyn14  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn14
		 (TSeq happy_var_3
	) `HappyStk` happyRest

happyReduce_19 = happyReduce 4 14 happyReduction_19
happyReduction_19 (_ `HappyStk`
	(HappyTerminal (( _, L.TLitInt happy_var_3 ))) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn14
		 (TQReg happy_var_3
	) `HappyStk` happyRest

happyReduce_20 = happySpecReduce_1  15 happyReduction_20
happyReduction_20 _
	 =  HappyAbsSyn15
		 (TNor
	)

happyReduce_21 = happySpecReduce_1  15 happyReduction_21
happyReduction_21 _
	 =  HappyAbsSyn15
		 (THad
	)

happyReduce_22 = happySpecReduce_1  15 happyReduction_22
happyReduction_22 _
	 =  HappyAbsSyn15
		 (TCH
	)

happyReduce_23 = happySpecReduce_1  15 happyReduction_23
happyReduction_23 _
	 =  HappyAbsSyn15
		 (TCH01
	)

happyReduce_24 = happySpecReduce_3  16 happyReduction_24
happyReduction_24 _
	(HappyAbsSyn17  happy_var_2)
	_
	 =  HappyAbsSyn16
		 (Block happy_var_2
	)
happyReduction_24 _ _ _  = notHappyAtAll 

happyReduce_25 = happySpecReduce_1  17 happyReduction_25
happyReduction_25 (HappyAbsSyn30  happy_var_1)
	 =  HappyAbsSyn17
		 (reverse happy_var_1
	)
happyReduction_25 _  = notHappyAtAll 

happyReduce_26 = happySpecReduce_3  18 happyReduction_26
happyReduction_26 _
	(HappyAbsSyn23  happy_var_2)
	_
	 =  HappyAbsSyn18
		 (SAssert happy_var_2
	)
happyReduction_26 _ _ _  = notHappyAtAll 

happyReduce_27 = happySpecReduce_3  18 happyReduction_27
happyReduction_27 _
	(HappyAbsSyn13  happy_var_2)
	_
	 =  HappyAbsSyn18
		 (SVar happy_var_2 Nothing
	)
happyReduction_27 _ _ _  = notHappyAtAll 

happyReduce_28 = happyReduce 5 18 happyReduction_28
happyReduction_28 (_ `HappyStk`
	(HappyAbsSyn23  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn13  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn18
		 (SVar happy_var_2 (Just happy_var_4)
	) `HappyStk` happyRest

happyReduce_29 = happyReduce 4 18 happyReduction_29
happyReduction_29 (_ `HappyStk`
	(HappyAbsSyn23  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (( _, L.TId happy_var_1     ))) `HappyStk`
	happyRest)
	 = HappyAbsSyn18
		 (SAssign happy_var_1 happy_var_3
	) `HappyStk` happyRest

happyReduce_30 = happyReduce 4 18 happyReduction_30
happyReduction_30 (_ `HappyStk`
	(HappyAbsSyn23  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn9  happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn18
		 (SApply happy_var_1 happy_var_3
	) `HappyStk` happyRest

happyReduce_31 = happyReduce 6 18 happyReduction_31
happyReduction_31 ((HappyAbsSyn16  happy_var_6) `HappyStk`
	(HappyAbsSyn9  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn18
		 (SIf happy_var_3 happy_var_5 happy_var_6
	) `HappyStk` happyRest

happyReduce_32 = happyReduce 13 18 happyReduction_32
happyReduction_32 ((HappyAbsSyn16  happy_var_13) `HappyStk`
	(HappyAbsSyn9  happy_var_12) `HappyStk`
	(HappyAbsSyn8  happy_var_11) `HappyStk`
	(HappyAbsSyn23  happy_var_10) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_5) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyTerminal (( _, L.TId happy_var_2     ))) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn18
		 (SFor happy_var_2 happy_var_5 happy_var_7 happy_var_10 happy_var_11 happy_var_12 happy_var_13
	) `HappyStk` happyRest

happyReduce_33 = happySpecReduce_1  19 happyReduction_33
happyReduction_33 (HappyAbsSyn33  happy_var_1)
	 =  HappyAbsSyn9
		 (Partition $ reverse happy_var_1
	)
happyReduction_33 _  = notHappyAtAll 

happyReduce_34 = happyReduce 6 20 happyReduction_34
happyReduction_34 (_ `HappyStk`
	(HappyAbsSyn23  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (( _, L.TId happy_var_1     ))) `HappyStk`
	happyRest)
	 = HappyAbsSyn20
		 (Range happy_var_1 happy_var_3 happy_var_5
	) `HappyStk` happyRest

happyReduce_35 = happyReduce 7 21 happyReduction_35
happyReduction_35 (_ `HappyStk`
	(HappyAbsSyn21  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn15  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn9  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn21
		 (ESpec happy_var_2 happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_36 = happyReduce 10 22 happyReduction_36
happyReduction_36 ((HappyAbsSyn35  happy_var_10) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_5) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyTerminal (( _, L.TId happy_var_2     ))) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn21
		 (EQSpec happy_var_2 (Intv happy_var_5 happy_var_7) happy_var_10
	) `HappyStk` happyRest

happyReduce_37 = happyReduce 19 22 happyReduction_37
happyReduction_37 ((HappyAbsSyn35  happy_var_19) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_16) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_14) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyTerminal (( _, L.TId happy_var_11     ))) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_5) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyTerminal (( _, L.TId happy_var_2     ))) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn21
		 (EQSpec01 happy_var_2 (Intv happy_var_5 happy_var_7) happy_var_11 (Intv happy_var_14 happy_var_16) happy_var_19
	) `HappyStk` happyRest

happyReduce_38 = happySpecReduce_0  22 happyReduction_38
happyReduction_38  =  HappyAbsSyn21
		 (EWildcard
	)

happyReduce_39 = happySpecReduce_1  23 happyReduction_39
happyReduction_39 (HappyAbsSyn28  happy_var_1)
	 =  HappyAbsSyn23
		 (happy_var_1
	)
happyReduction_39 _  = notHappyAtAll 

happyReduce_40 = happySpecReduce_1  23 happyReduction_40
happyReduction_40 _
	 =  HappyAbsSyn23
		 (EWildcard
	)

happyReduce_41 = happySpecReduce_1  23 happyReduction_41
happyReduction_41 (HappyAbsSyn21  happy_var_1)
	 =  HappyAbsSyn23
		 (happy_var_1
	)
happyReduction_41 _  = notHappyAtAll 

happyReduce_42 = happySpecReduce_1  23 happyReduction_42
happyReduction_42 (HappyAbsSyn9  happy_var_1)
	 =  HappyAbsSyn23
		 (EPartition happy_var_1
	)
happyReduction_42 _  = notHappyAtAll 

happyReduce_43 = happySpecReduce_1  23 happyReduction_43
happyReduction_43 _
	 =  HappyAbsSyn23
		 (EHad
	)

happyReduce_44 = happySpecReduce_1  23 happyReduction_44
happyReduction_44 _
	 =  HappyAbsSyn23
		 (EQFT
	)

happyReduce_45 = happySpecReduce_1  23 happyReduction_45
happyReduction_45 _
	 =  HappyAbsSyn23
		 (ERQFT
	)

happyReduce_46 = happySpecReduce_2  23 happyReduction_46
happyReduction_46 (HappyTerminal (( _, L.TId happy_var_2     )))
	_
	 =  HappyAbsSyn23
		 (EMea happy_var_2
	)
happyReduction_46 _ _  = notHappyAtAll 

happyReduce_47 = happySpecReduce_2  23 happyReduction_47
happyReduction_47 (HappyAbsSyn28  happy_var_2)
	_
	 =  HappyAbsSyn23
		 (EOp1 ONot happy_var_2
	)
happyReduction_47 _ _  = notHappyAtAll 

happyReduce_48 = happyReduce 6 23 happyReduction_48
happyReduction_48 (_ `HappyStk`
	(HappyTerminal (( _, L.TLitInt happy_var_5 ))) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn28  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn23
		 (EOp2 ONor happy_var_3 (ENum happy_var_5)
	) `HappyStk` happyRest

happyReduce_49 = happyReduce 6 23 happyReduction_49
happyReduction_49 (_ `HappyStk`
	(HappyAbsSyn23  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (( _, L.TId happy_var_3     ))) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn23
		 (EEmit $ ELambda happy_var_3 happy_var_5
	) `HappyStk` happyRest

happyReduce_50 = happyReduce 4 23 happyReduction_50
happyReduction_50 (_ `HappyStk`
	(HappyAbsSyn28  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (( _, L.TId happy_var_1     ))) `HappyStk`
	happyRest)
	 = HappyAbsSyn23
		 (EApp happy_var_1 happy_var_3
	) `HappyStk` happyRest

happyReduce_51 = happySpecReduce_3  23 happyReduction_51
happyReduction_51 (HappyAbsSyn28  happy_var_3)
	_
	(HappyAbsSyn28  happy_var_1)
	 =  HappyAbsSyn23
		 (EOp2 OAnd happy_var_1 happy_var_3
	)
happyReduction_51 _ _ _  = notHappyAtAll 

happyReduce_52 = happySpecReduce_3  23 happyReduction_52
happyReduction_52 (HappyAbsSyn28  happy_var_3)
	_
	(HappyAbsSyn28  happy_var_1)
	 =  HappyAbsSyn23
		 (EOp2 OOr happy_var_1 happy_var_3
	)
happyReduction_52 _ _ _  = notHappyAtAll 

happyReduce_53 = happySpecReduce_1  23 happyReduction_53
happyReduction_53 (HappyAbsSyn21  happy_var_1)
	 =  HappyAbsSyn23
		 (happy_var_1
	)
happyReduction_53 _  = notHappyAtAll 

happyReduce_54 = happySpecReduce_1  23 happyReduction_54
happyReduction_54 (HappyAbsSyn21  happy_var_1)
	 =  HappyAbsSyn23
		 (happy_var_1
	)
happyReduction_54 _  = notHappyAtAll 

happyReduce_55 = happySpecReduce_3  23 happyReduction_55
happyReduction_55 _
	(HappyAbsSyn23  happy_var_2)
	_
	 =  HappyAbsSyn23
		 (happy_var_2
	)
happyReduction_55 _ _ _  = notHappyAtAll 

happyReduce_56 = happySpecReduce_3  24 happyReduction_56
happyReduction_56 (HappyAbsSyn23  happy_var_3)
	(HappyAbsSyn25  happy_var_2)
	(HappyAbsSyn23  happy_var_1)
	 =  HappyAbsSyn21
		 (EOp2 happy_var_2 happy_var_1 happy_var_3
	)
happyReduction_56 _ _ _  = notHappyAtAll 

happyReduce_57 = happySpecReduce_1  25 happyReduction_57
happyReduction_57 _
	 =  HappyAbsSyn25
		 (OGt
	)

happyReduce_58 = happySpecReduce_1  25 happyReduction_58
happyReduction_58 _
	 =  HappyAbsSyn25
		 (OLt
	)

happyReduce_59 = happySpecReduce_1  25 happyReduction_59
happyReduction_59 _
	 =  HappyAbsSyn25
		 (OGe
	)

happyReduce_60 = happySpecReduce_1  25 happyReduction_60
happyReduction_60 _
	 =  HappyAbsSyn25
		 (OLe
	)

happyReduce_61 = happySpecReduce_3  26 happyReduction_61
happyReduction_61 (HappyAbsSyn23  happy_var_3)
	(HappyAbsSyn25  happy_var_2)
	(HappyAbsSyn23  happy_var_1)
	 =  HappyAbsSyn21
		 (EOp2 happy_var_2 happy_var_1 happy_var_3
	)
happyReduction_61 _ _ _  = notHappyAtAll 

happyReduce_62 = happySpecReduce_1  27 happyReduction_62
happyReduction_62 _
	 =  HappyAbsSyn25
		 (OAdd
	)

happyReduce_63 = happySpecReduce_1  27 happyReduction_63
happyReduction_63 _
	 =  HappyAbsSyn25
		 (OSub
	)

happyReduce_64 = happySpecReduce_1  27 happyReduction_64
happyReduction_64 _
	 =  HappyAbsSyn25
		 (OMul
	)

happyReduce_65 = happySpecReduce_1  27 happyReduction_65
happyReduction_65 _
	 =  HappyAbsSyn25
		 (OMod
	)

happyReduce_66 = happySpecReduce_1  28 happyReduction_66
happyReduction_66 (HappyTerminal (( _, L.TLitInt happy_var_1 )))
	 =  HappyAbsSyn28
		 (ENum happy_var_1
	)
happyReduction_66 _  = notHappyAtAll 

happyReduce_67 = happySpecReduce_1  28 happyReduction_67
happyReduction_67 (HappyTerminal (( _, L.TId happy_var_1     )))
	 =  HappyAbsSyn28
		 (EVar happy_var_1
	)
happyReduction_67 _  = notHappyAtAll 

happyReduce_68 = happySpecReduce_1  29 happyReduction_68
happyReduction_68 (HappyAbsSyn39  happy_var_1)
	 =  HappyAbsSyn29
		 (reverse happy_var_1
	)
happyReduction_68 _  = notHappyAtAll 

happyReduce_69 = happySpecReduce_1  30 happyReduction_69
happyReduction_69 (HappyAbsSyn40  happy_var_1)
	 =  HappyAbsSyn30
		 (reverse happy_var_1
	)
happyReduction_69 _  = notHappyAtAll 

happyReduce_70 = happySpecReduce_1  31 happyReduction_70
happyReduction_70 (HappyAbsSyn41  happy_var_1)
	 =  HappyAbsSyn31
		 (reverse happy_var_1
	)
happyReduction_70 _  = notHappyAtAll 

happyReduce_71 = happySpecReduce_1  32 happyReduction_71
happyReduction_71 (HappyAbsSyn37  happy_var_1)
	 =  HappyAbsSyn32
		 (reverse happy_var_1
	)
happyReduction_71 _  = notHappyAtAll 

happyReduce_72 = happySpecReduce_1  33 happyReduction_72
happyReduction_72 (HappyAbsSyn38  happy_var_1)
	 =  HappyAbsSyn33
		 (reverse happy_var_1
	)
happyReduction_72 _  = notHappyAtAll 

happyReduce_73 = happySpecReduce_0  34 happyReduction_73
happyReduction_73  =  HappyAbsSyn34
		 (Nothing
	)

happyReduce_74 = happySpecReduce_1  34 happyReduction_74
happyReduction_74 (HappyAbsSyn16  happy_var_1)
	 =  HappyAbsSyn34
		 (Just happy_var_1
	)
happyReduction_74 _  = notHappyAtAll 

happyReduce_75 = happySpecReduce_3  35 happyReduction_75
happyReduction_75 _
	(HappyAbsSyn36  happy_var_2)
	_
	 =  HappyAbsSyn35
		 (happy_var_2
	)
happyReduction_75 _ _ _  = notHappyAtAll 

happyReduce_76 = happySpecReduce_1  36 happyReduction_76
happyReduction_76 (HappyAbsSyn42  happy_var_1)
	 =  HappyAbsSyn36
		 (reverse happy_var_1
	)
happyReduction_76 _  = notHappyAtAll 

happyReduce_77 = happySpecReduce_0  37 happyReduction_77
happyReduction_77  =  HappyAbsSyn37
		 ([]
	)

happyReduce_78 = happySpecReduce_1  37 happyReduction_78
happyReduction_78 (HappyAbsSyn13  happy_var_1)
	 =  HappyAbsSyn37
		 ([happy_var_1]
	)
happyReduction_78 _  = notHappyAtAll 

happyReduce_79 = happySpecReduce_3  37 happyReduction_79
happyReduction_79 (HappyAbsSyn13  happy_var_3)
	_
	(HappyAbsSyn37  happy_var_1)
	 =  HappyAbsSyn37
		 (happy_var_3 : happy_var_1
	)
happyReduction_79 _ _ _  = notHappyAtAll 

happyReduce_80 = happySpecReduce_0  38 happyReduction_80
happyReduction_80  =  HappyAbsSyn38
		 ([]
	)

happyReduce_81 = happySpecReduce_1  38 happyReduction_81
happyReduction_81 (HappyAbsSyn20  happy_var_1)
	 =  HappyAbsSyn38
		 ([happy_var_1]
	)
happyReduction_81 _  = notHappyAtAll 

happyReduce_82 = happySpecReduce_3  38 happyReduction_82
happyReduction_82 (HappyAbsSyn20  happy_var_3)
	_
	(HappyAbsSyn38  happy_var_1)
	 =  HappyAbsSyn38
		 (happy_var_3 : happy_var_1
	)
happyReduction_82 _ _ _  = notHappyAtAll 

happyReduce_83 = happySpecReduce_0  39 happyReduction_83
happyReduction_83  =  HappyAbsSyn39
		 ([]
	)

happyReduce_84 = happySpecReduce_2  39 happyReduction_84
happyReduction_84 (HappyAbsSyn11  happy_var_2)
	(HappyAbsSyn39  happy_var_1)
	 =  HappyAbsSyn39
		 (happy_var_2 : happy_var_1
	)
happyReduction_84 _ _  = notHappyAtAll 

happyReduce_85 = happySpecReduce_0  40 happyReduction_85
happyReduction_85  =  HappyAbsSyn40
		 ([]
	)

happyReduce_86 = happySpecReduce_2  40 happyReduction_86
happyReduction_86 (HappyAbsSyn18  happy_var_2)
	(HappyAbsSyn40  happy_var_1)
	 =  HappyAbsSyn40
		 (happy_var_2 : happy_var_1
	)
happyReduction_86 _ _  = notHappyAtAll 

happyReduce_87 = happySpecReduce_0  41 happyReduction_87
happyReduction_87  =  HappyAbsSyn41
		 ([]
	)

happyReduce_88 = happySpecReduce_2  41 happyReduction_88
happyReduction_88 (HappyAbsSyn6  happy_var_2)
	(HappyAbsSyn41  happy_var_1)
	 =  HappyAbsSyn41
		 (happy_var_2 : happy_var_1
	)
happyReduction_88 _ _  = notHappyAtAll 

happyReduce_89 = happySpecReduce_0  42 happyReduction_89
happyReduction_89  =  HappyAbsSyn42
		 ([]
	)

happyReduce_90 = happySpecReduce_1  42 happyReduction_90
happyReduction_90 (HappyAbsSyn23  happy_var_1)
	 =  HappyAbsSyn42
		 ([happy_var_1]
	)
happyReduction_90 _  = notHappyAtAll 

happyReduce_91 = happySpecReduce_3  42 happyReduction_91
happyReduction_91 (HappyAbsSyn23  happy_var_3)
	_
	(HappyAbsSyn42  happy_var_1)
	 =  HappyAbsSyn42
		 (happy_var_3 : happy_var_1
	)
happyReduction_91 _ _ _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 104 104 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	( _, L.TLitInt happy_dollar_dollar ) -> cont 43;
	( _, L.TDafny happy_dollar_dollar  ) -> cont 44;
	( _, L.TMethod    ) -> cont 45;
	( _, L.TEnsures   ) -> cont 46;
	( _, L.TRequires  ) -> cont 47;
	( _, L.TSeparates ) -> cont 48;
	( _, L.TInv       ) -> cont 49;
	( _, L.TWith      ) -> cont 50;
	( _, L.TFor       ) -> cont 51;
	( _, L.TReturns   ) -> cont 52;
	( _, L.TNot       ) -> cont 53;
	( _, L.TNat       ) -> cont 54;
	( _, L.TInt       ) -> cont 55;
	( _, L.TIn        ) -> cont 56;
	( _, L.TBool      ) -> cont 57;
	( _, L.TSeq       ) -> cont 58;
	( _, L.TNor       ) -> cont 59;
	( _, L.THad       ) -> cont 60;
	( _, L.THApp      ) -> cont 61;
	( _, L.TQFT       ) -> cont 62;
	( _, L.TRQFT      ) -> cont 63;
	( _, L.TMea       ) -> cont 64;
	( _, L.TCH        ) -> cont 65;
	( _, L.TQReg      ) -> cont 66;
	( _, L.TCH01      ) -> cont 67;
	( _, L.TVar       ) -> cont 68;
	( _, L.TIf        ) -> cont 69;
	( _, L.TCl        ) -> cont 70;
	( _, L.TUnicodeSum    ) -> cont 71;
	( _, L.TUnicodeTensor ) -> cont 72;
	( _, L.TUnicodeIn     ) -> cont 73;
	( _, L.TUnicodeMap    ) -> cont 74;
	( _, L.TAssert    ) -> cont 75;
	( _, L.TOr        ) -> cont 76;
	( _, L.TAnd       ) -> cont 77;
	( _, L.TAdd       ) -> cont 78;
	( _, L.TSub       ) -> cont 79;
	( _, L.TMul       ) -> cont 80;
	( _, L.TMod       ) -> cont 81;
	( _, L.TBar       ) -> cont 82;
	( _, L.TLPar      ) -> cont 83;
	( _, L.TRPar      ) -> cont 84;
	( _, L.TLAng      ) -> cont 85;
	( _, L.TRAng      ) -> cont 86;
	( _, L.TLBracket  ) -> cont 87;
	( _, L.TRBracket  ) -> cont 88;
	( _, L.TLBrace    ) -> cont 89;
	( _, L.TRBrace    ) -> cont 90;
	( _, L.TId happy_dollar_dollar     ) -> cont 91;
	( _, L.TWildcard  ) -> cont 92;
	( _, L.TComma     ) -> cont 93;
	( _, L.TColon     ) -> cont 94;
	( _, L.TDot       ) -> cont 95;
	( _, L.TSemi      ) -> cont 96;
	( _, L.TEq        ) -> cont 97;
	( _, L.TArrow     ) -> cont 98;
	( _, L.TGe        ) -> cont 99;
	( _, L.TLe        ) -> cont 100;
	( _, L.TAssign    ) -> cont 101;
	( _, L.TApply     ) -> cont 102;
	( _, L.TDots      ) -> cont 103;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 104 tk tks = happyError' (tks, explist)
happyError_ explist _ tk tks = happyError' ((tk:tks), explist)

happyThen :: () => Parser a -> (a -> Parser b) -> Parser b
happyThen = (>>=)
happyReturn :: () => a -> Parser a
happyReturn = (return)
happyThen1 m k tks = (>>=) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> Parser a
happyReturn1 = \a tks -> (return) a
happyError' :: () => ([(L.SToken)], [String]) -> Parser a
happyError' = (\(tokens, _) -> parseError tokens)
runParser tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn4 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


scanAndParse :: String -> Parser AST
scanAndParse = runParser <=< L.runScanner
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- $Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp $










































data Happy_IntList = HappyCons Int Happy_IntList








































infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is ERROR_TOK, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept (1) tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
         (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action









































indexShortOffAddr arr off = arr Happy_Data_Array.! off


{-# INLINE happyLt #-}
happyLt x y = (x < y)






readArrayBit arr bit =
    Bits.testBit (indexShortOffAddr arr (bit `div` 16)) (bit `mod` 16)






-----------------------------------------------------------------------------
-- HappyState data type (not arrays)



newtype HappyState b c = HappyState
        (Int ->                    -- token number
         Int ->                    -- token number (yes, again)
         b ->                           -- token semantic value
         HappyState b c ->              -- current state
         [HappyState b c] ->            -- state stack
         c)



-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state (1) tk st sts stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--     trace "shifting the error token" $
     new_state i i tk (HappyState (new_state)) ((st):(sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state ((st):(sts)) ((HappyTerminal (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_0 nt fn j tk st@((HappyState (action))) sts stk
     = action nt j tk st ((st):(sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@(((st@(HappyState (action))):(_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_2 nt fn j tk _ ((_):(sts@(((st@(HappyState (action))):(_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_3 nt fn j tk _ ((_):(((_):(sts@(((st@(HappyState (action))):(_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k - ((1) :: Int)) sts of
         sts1@(((st1@(HappyState (action))):(_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (action nt j tk st1 sts1 r)

happyMonadReduce k nt fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> action nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
         let drop_stk = happyDropStk k stk





             _ = nt :: Int
             new_state = action

          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop (0) l = l
happyDrop n ((_):(t)) = happyDrop (n - ((1) :: Int)) t

happyDropStk (0) l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n - ((1)::Int)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction









happyGoto action j tk st = action j j tk (HappyState action)


-----------------------------------------------------------------------------
-- Error recovery (ERROR_TOK is the error token)

-- parse error if we are in recovery and we fail again
happyFail explist (1) tk old_st _ stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--      trace "failing" $ 
        happyError_ explist i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  ERROR_TOK tk old_st CONS(HAPPYSTATE(action),sts) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        DO_ACTION(action,ERROR_TOK,tk,sts,(saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail explist i tk (HappyState (action)) sts stk =
--      trace "entering error recovery" $
        action (1) (1) tk (HappyState (action)) sts ((HappyErrorToken (i)) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions







-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.









{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
