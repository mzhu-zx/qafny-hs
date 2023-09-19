{-# OPTIONS_GHC -w #-}
{-# LANGUAGE TypeFamilies, FlexibleContexts, FlexibleInstances #-}


module Qafny.Syntax.Parser(scanAndParse) where
import qualified Qafny.Syntax.Lexer as L
import           Qafny.Syntax.ParserUtils
import           Qafny.Syntax.AST
import           Control.Monad
import           Data.Sum
import qualified Data.Array as Happy_Data_Array
import qualified Data.Bits as Bits
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.19.12

data HappyAbsSyn t4 t5 t9 t10 t11 t13 t14 t19 t22 t23 t26 t31 t32 t33 t34 t35 t36 t37 t38 t39 t40 t41 t42 t43 t44 t45 t46 t47 t48
	= HappyTerminal (L.SToken)
	| HappyErrorToken Int
	| HappyAbsSyn4 t4
	| HappyAbsSyn5 t5
	| HappyAbsSyn6 (Toplevel')
	| HappyAbsSyn7 ([ Conds ])
	| HappyAbsSyn8 (Conds)
	| HappyAbsSyn9 t9
	| HappyAbsSyn10 t10
	| HappyAbsSyn11 t11
	| HappyAbsSyn12 (QTy)
	| HappyAbsSyn13 t13
	| HappyAbsSyn14 t14
	| HappyAbsSyn15 (Stmt')
	| HappyAbsSyn16 (Exp')
	| HappyAbsSyn17 (GuardExp)
	| HappyAbsSyn18 (Partition)
	| HappyAbsSyn19 t19
	| HappyAbsSyn21 (SpecExp')
	| HappyAbsSyn22 t22
	| HappyAbsSyn23 t23
	| HappyAbsSyn26 t26
	| HappyAbsSyn28 (Op2)
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
	| HappyAbsSyn43 t43
	| HappyAbsSyn44 t44
	| HappyAbsSyn45 t45
	| HappyAbsSyn46 t46
	| HappyAbsSyn47 t47
	| HappyAbsSyn48 t48

happyExpList :: Happy_Data_Array.Array Int Int
happyExpList = Happy_Data_Array.listArray (0,644) ([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2048,0,0,0,0,0,0,16,0,0,0,0,0,0,8192,0,0,0,0,0,0,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,32,0,0,0,24576,515,0,0,0,0,0,0,0,0,16,0,0,0,8192,0,0,0,0,0,0,0,0,0,16,0,0,0,0,0,0,0,0,0,0,3840,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,512,0,0,0,0,0,0,4096,0,0,0,16384,0,0,0,2,0,0,0,45056,257,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,16388,33744,8192,96,0,0,0,32776,1952,16385,192,0,0,0,0,0,0,128,0,0,0,32,7810,4,769,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2048,0,0,0,0,0,0,0,0,0,0,4096,32,16576,16384,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,256,0,0,0,0,0,0,0,0,0,0,0,0,0,30720,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,512,0,0,4112,0,0,0,0,0,0,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,1024,0,0,0,0,4097,8436,2048,26,0,0,0,0,0,0,16,0,0,0,0,0,8192,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,0,0,0,0,0,0,128,0,0,0,0,0,0,1024,0,0,0,0,0,0,2048,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4097,8436,2048,26,0,0,0,0,0,0,0,0,0,0,16388,33744,8192,104,0,0,0,0,0,0,512,0,0,0,0,0,0,1,0,0,0,0,0,0,256,0,0,0,0,0,0,0,0,0,0,128,0,0,1028,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8192,0,0,0,2048,0,0,16448,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,49152,12288,0,0,0,4,0,8192,32,0,0,0,8,0,16384,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,1024,0,0,0,0,0,0,2048,0,0,0,0,0,0,16,0,0,0,1024,53312,131,26656,0,0,0,0,0,0,1088,256,0,0,0,0,0,0,0,0,0,0,0,0,0,32,0,0,16384,1024,2109,33280,6,0,0,0,0,0,0,128,0,0,0,0,0,0,8,0,0,0,0,0,0,16896,0,0,0,0,2,0,0,0,0,0,32776,1952,16385,208,0,0,0,0,0,0,0,0,0,0,0,0,30720,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,256,0,0,2056,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,0,0,0,0,0,0,1024,0,0,0,0,0,0,0,0,0,0,0,5168,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1024,0,0,0,0,0,0,0,32,0,0,0,0,0,256,0,0,0,0,0,0,0,0,0,0,512,59424,65,13328,0,0,0,1024,53312,131,26656,0,0,0,0,0,0,0,0,0,0,0,0,16384,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8194,16872,4096,52,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4096,0,0,0,0,0,0,16,0,0,0,0,0,0,0,0,0,0,128,31240,16,3332,0,0,0,0,0,0,16,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,256,0,0,0,0,0,0,240,0,0,0,0,0,0,0,0,0,1024,0,0,0,32776,1952,16385,208,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,4,0,0,0,0,0,96,2048,0,0,0,0,0,0,0,0,0,0,0,0,0,512,0,0,0,0,0,0,0,0,0,0,0,0,0,8192,0,0,0,0,0,0,32768,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,16,0,0,0,16,3905,32770,384,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,128,31240,16,3332,0,0,0,0,0,0,32768,0,0,0,0,0,1024,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1024,0,0,0,0,0,0,128,0,0,0,0,0,0,8192,0,0,0,0,32,0,0,0,0,0,0,0,0,0,0,0,0,0,4097,8436,2048,26,0,0,0,0,0,0,0,1,0,0,0,0,0,32,0,0,0,0,0,0,0,0,0,0,16,3905,32770,416,0,0,0,0,0,0,32,0,0,0,0,0,0,128,0,0,0,0,0,0,0,0,0,0,0,0,0,32768,0,0,0,0,0,256,16,0,0,0,0,0,0,0,0,0,0,0,0,0,16384,0,0,0,0,0,8192,0,0,0,0,0,0,0,4096,0,0,0,16384,1024,2109,33280,6,0,0,0,0,0,0,16384,0,0,0,4097,8436,2048,26,0,0,0,0,0,0,2,0,0,0,0,0,0,512,0,0,0,0,0,16384,0,0,0,0,0,0,0,0,0,0
	])

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_runParser","AST","toplevels","toplevel","conds","cond","bindings","binding","ty","qty","block","stmts","stmt","splitAt","guardExpr","partition","range","spec","qspec","expr","qops","logicOrExp","logicAndExp","cmpPartial","cmpExpr","cmp","arithExpr","arith","atomic","many__cmpPartial__","many__cond__","many__stmt__","many__toplevel__","manyComma__binding__","manyComma__range__","opt__block__","opt__splitAt__","tuple__expr__","manyComma__expr__","manyComma___binding__","manyComma___range__","many___cmpPartial__","many___cond__","many___stmt__","many___toplevel__","manyComma___expr__","digits","dafny","\"method\"","\"ensures\"","\"requires\"","\"separates\"","\"invariant\"","\"with\"","\"at\"","\"split\"","\"for\"","\"returns\"","\"not\"","\"nat\"","\"int\"","\"in\"","\"bool\"","\"seq\"","\"nor\"","\"had\"","\"H\"","\"QFT\"","\"RQFT\"","\"meas\"","\"en\"","\"qreg\"","\"en01\"","\"var\"","\"if\"","\"\955\"","\"\931\"","\"\8855\"","\"\969\"","\"\8712\"","\"\8614\"","\"assert\"","\"||\"","\"&&\"","'+'","'-'","'*'","'\\%'","'|'","'('","')'","'<'","'>'","'['","']'","'{'","'}'","id","'_'","','","':'","'.'","';'","\"==\"","\"=>\"","\">=\"","\"<=\"","\":=\"","\"*=\"","\"..\"","%eof"]
        bit_start = st * 113
        bit_end = (st + 1) * 113
        read_bit = readArrayBit happyExpList
        bits = map read_bit [bit_start..bit_end - 1]
        bits_indexed = zip bits [0..112]
        token_strs_expected = concatMap f bits_indexed
        f (False, _) = []
        f (True, nr) = [token_strs !! nr]

action_0 (4) = happyGoto action_5
action_0 (5) = happyGoto action_2
action_0 (35) = happyGoto action_3
action_0 (47) = happyGoto action_4
action_0 _ = happyReduce_100

action_1 (5) = happyGoto action_2
action_1 (35) = happyGoto action_3
action_1 (47) = happyGoto action_4
action_1 _ = happyFail (happyExpListPerState 1)

action_2 _ = happyReduce_1

action_3 _ = happyReduce_2

action_4 (50) = happyShift action_7
action_4 (51) = happyShift action_8
action_4 (6) = happyGoto action_6
action_4 _ = happyReduce_79

action_5 (113) = happyAccept
action_5 _ = happyFail (happyExpListPerState 5)

action_6 _ = happyReduce_101

action_7 _ = happyReduce_3

action_8 (100) = happyShift action_9
action_8 _ = happyFail (happyExpListPerState 8)

action_9 (92) = happyShift action_10
action_9 _ = happyFail (happyExpListPerState 9)

action_10 (100) = happyShift action_15
action_10 (9) = happyGoto action_11
action_10 (10) = happyGoto action_12
action_10 (36) = happyGoto action_13
action_10 (42) = happyGoto action_14
action_10 _ = happyReduce_88

action_11 (93) = happyShift action_18
action_11 _ = happyFail (happyExpListPerState 11)

action_12 _ = happyReduce_89

action_13 _ = happyReduce_11

action_14 (102) = happyShift action_17
action_14 _ = happyReduce_80

action_15 (103) = happyShift action_16
action_15 _ = happyFail (happyExpListPerState 15)

action_16 (62) = happyShift action_25
action_16 (63) = happyShift action_26
action_16 (65) = happyShift action_27
action_16 (66) = happyShift action_28
action_16 (74) = happyShift action_29
action_16 (11) = happyGoto action_24
action_16 _ = happyFail (happyExpListPerState 16)

action_17 (100) = happyShift action_15
action_17 (10) = happyGoto action_23
action_17 _ = happyFail (happyExpListPerState 17)

action_18 (60) = happyShift action_22
action_18 (7) = happyGoto action_19
action_18 (33) = happyGoto action_20
action_18 (45) = happyGoto action_21
action_18 _ = happyReduce_96

action_19 (98) = happyShift action_40
action_19 (13) = happyGoto action_38
action_19 (38) = happyGoto action_39
action_19 _ = happyReduce_82

action_20 _ = happyReduce_6

action_21 (52) = happyShift action_34
action_21 (53) = happyShift action_35
action_21 (54) = happyShift action_36
action_21 (55) = happyShift action_37
action_21 (8) = happyGoto action_33
action_21 _ = happyReduce_77

action_22 (92) = happyShift action_32
action_22 _ = happyFail (happyExpListPerState 22)

action_23 _ = happyReduce_90

action_24 _ = happyReduce_12

action_25 _ = happyReduce_13

action_26 _ = happyReduce_14

action_27 _ = happyReduce_15

action_28 (94) = happyShift action_31
action_28 _ = happyFail (happyExpListPerState 28)

action_29 (96) = happyShift action_30
action_29 _ = happyFail (happyExpListPerState 29)

action_30 (49) = happyShift action_74
action_30 (100) = happyShift action_75
action_30 _ = happyFail (happyExpListPerState 30)

action_31 (62) = happyShift action_25
action_31 (63) = happyShift action_26
action_31 (65) = happyShift action_27
action_31 (66) = happyShift action_28
action_31 (74) = happyShift action_29
action_31 (11) = happyGoto action_73
action_31 _ = happyFail (happyExpListPerState 31)

action_32 (100) = happyShift action_15
action_32 (9) = happyGoto action_72
action_32 (10) = happyGoto action_12
action_32 (36) = happyGoto action_13
action_32 (42) = happyGoto action_14
action_32 _ = happyReduce_88

action_33 _ = happyReduce_97

action_34 (49) = happyShift action_56
action_34 (61) = happyShift action_57
action_34 (67) = happyShift action_58
action_34 (69) = happyShift action_59
action_34 (70) = happyShift action_60
action_34 (71) = happyShift action_61
action_34 (72) = happyShift action_62
action_34 (78) = happyShift action_63
action_34 (92) = happyShift action_64
action_34 (98) = happyShift action_65
action_34 (100) = happyShift action_66
action_34 (101) = happyShift action_67
action_34 (18) = happyGoto action_44
action_34 (19) = happyGoto action_45
action_34 (20) = happyGoto action_46
action_34 (22) = happyGoto action_71
action_34 (23) = happyGoto action_48
action_34 (24) = happyGoto action_49
action_34 (25) = happyGoto action_50
action_34 (27) = happyGoto action_51
action_34 (29) = happyGoto action_52
action_34 (31) = happyGoto action_53
action_34 (37) = happyGoto action_54
action_34 (43) = happyGoto action_55
action_34 _ = happyReduce_91

action_35 (49) = happyShift action_56
action_35 (61) = happyShift action_57
action_35 (67) = happyShift action_58
action_35 (69) = happyShift action_59
action_35 (70) = happyShift action_60
action_35 (71) = happyShift action_61
action_35 (72) = happyShift action_62
action_35 (78) = happyShift action_63
action_35 (92) = happyShift action_64
action_35 (98) = happyShift action_65
action_35 (100) = happyShift action_66
action_35 (101) = happyShift action_67
action_35 (18) = happyGoto action_44
action_35 (19) = happyGoto action_45
action_35 (20) = happyGoto action_46
action_35 (22) = happyGoto action_70
action_35 (23) = happyGoto action_48
action_35 (24) = happyGoto action_49
action_35 (25) = happyGoto action_50
action_35 (27) = happyGoto action_51
action_35 (29) = happyGoto action_52
action_35 (31) = happyGoto action_53
action_35 (37) = happyGoto action_54
action_35 (43) = happyGoto action_55
action_35 _ = happyReduce_91

action_36 (100) = happyShift action_69
action_36 (18) = happyGoto action_68
action_36 (19) = happyGoto action_45
action_36 (37) = happyGoto action_54
action_36 (43) = happyGoto action_55
action_36 _ = happyReduce_91

action_37 (49) = happyShift action_56
action_37 (61) = happyShift action_57
action_37 (67) = happyShift action_58
action_37 (69) = happyShift action_59
action_37 (70) = happyShift action_60
action_37 (71) = happyShift action_61
action_37 (72) = happyShift action_62
action_37 (78) = happyShift action_63
action_37 (92) = happyShift action_64
action_37 (98) = happyShift action_65
action_37 (100) = happyShift action_66
action_37 (101) = happyShift action_67
action_37 (18) = happyGoto action_44
action_37 (19) = happyGoto action_45
action_37 (20) = happyGoto action_46
action_37 (22) = happyGoto action_47
action_37 (23) = happyGoto action_48
action_37 (24) = happyGoto action_49
action_37 (25) = happyGoto action_50
action_37 (27) = happyGoto action_51
action_37 (29) = happyGoto action_52
action_37 (31) = happyGoto action_53
action_37 (37) = happyGoto action_54
action_37 (43) = happyGoto action_55
action_37 _ = happyReduce_91

action_38 _ = happyReduce_83

action_39 _ = happyReduce_5

action_40 (14) = happyGoto action_41
action_40 (34) = happyGoto action_42
action_40 (46) = happyGoto action_43
action_40 _ = happyReduce_98

action_41 (99) = happyShift action_108
action_41 _ = happyFail (happyExpListPerState 41)

action_42 _ = happyReduce_24

action_43 (50) = happyShift action_102
action_43 (59) = happyShift action_103
action_43 (76) = happyShift action_104
action_43 (77) = happyShift action_105
action_43 (84) = happyShift action_106
action_43 (100) = happyShift action_107
action_43 (102) = happyReduce_91
action_43 (111) = happyReduce_91
action_43 (15) = happyGoto action_100
action_43 (18) = happyGoto action_101
action_43 (19) = happyGoto action_45
action_43 (37) = happyGoto action_54
action_43 (43) = happyGoto action_55
action_43 _ = happyReduce_78

action_44 _ = happyReduce_46

action_45 _ = happyReduce_92

action_46 _ = happyReduce_45

action_47 _ = happyReduce_9

action_48 _ = happyReduce_47

action_49 _ = happyReduce_53

action_50 (85) = happyShift action_99
action_50 _ = happyReduce_58

action_51 (86) = happyShift action_98
action_51 _ = happyReduce_60

action_52 (32) = happyGoto action_96
action_52 (44) = happyGoto action_97
action_52 _ = happyReduce_94

action_53 (50) = happyReduce_68
action_53 (51) = happyReduce_68
action_53 (52) = happyReduce_68
action_53 (53) = happyReduce_68
action_53 (54) = happyReduce_68
action_53 (55) = happyReduce_68
action_53 (87) = happyShift action_92
action_53 (88) = happyShift action_93
action_53 (89) = happyShift action_94
action_53 (90) = happyShift action_95
action_53 (93) = happyReduce_68
action_53 (97) = happyReduce_68
action_53 (98) = happyReduce_68
action_53 (102) = happyReduce_68
action_53 (105) = happyReduce_68
action_53 (112) = happyReduce_68
action_53 (113) = happyReduce_68
action_53 (30) = happyGoto action_91
action_53 _ = happyReduce_68

action_54 _ = happyReduce_36

action_55 (102) = happyShift action_90
action_55 _ = happyReduce_81

action_56 _ = happyReduce_73

action_57 (49) = happyShift action_56
action_57 (92) = happyShift action_64
action_57 (100) = happyShift action_89
action_57 (31) = happyGoto action_88
action_57 _ = happyFail (happyExpListPerState 57)

action_58 (92) = happyShift action_87
action_58 _ = happyFail (happyExpListPerState 58)

action_59 _ = happyReduce_54

action_60 _ = happyReduce_55

action_61 _ = happyReduce_56

action_62 (100) = happyShift action_86
action_62 _ = happyFail (happyExpListPerState 62)

action_63 (92) = happyShift action_85
action_63 _ = happyFail (happyExpListPerState 63)

action_64 (49) = happyShift action_56
action_64 (61) = happyShift action_57
action_64 (67) = happyShift action_58
action_64 (69) = happyShift action_59
action_64 (70) = happyShift action_60
action_64 (71) = happyShift action_61
action_64 (72) = happyShift action_62
action_64 (78) = happyShift action_63
action_64 (92) = happyShift action_64
action_64 (98) = happyShift action_65
action_64 (100) = happyShift action_66
action_64 (101) = happyShift action_67
action_64 (18) = happyGoto action_44
action_64 (19) = happyGoto action_45
action_64 (20) = happyGoto action_46
action_64 (22) = happyGoto action_84
action_64 (23) = happyGoto action_48
action_64 (24) = happyGoto action_49
action_64 (25) = happyGoto action_50
action_64 (27) = happyGoto action_51
action_64 (29) = happyGoto action_52
action_64 (31) = happyGoto action_53
action_64 (37) = happyGoto action_54
action_64 (43) = happyGoto action_55
action_64 _ = happyReduce_91

action_65 (100) = happyShift action_69
action_65 (18) = happyGoto action_83
action_65 (19) = happyGoto action_45
action_65 (37) = happyGoto action_54
action_65 (43) = happyGoto action_55
action_65 _ = happyReduce_91

action_66 (92) = happyShift action_82
action_66 (96) = happyShift action_80
action_66 (40) = happyGoto action_81
action_66 _ = happyReduce_74

action_67 _ = happyReduce_44

action_68 _ = happyReduce_10

action_69 (96) = happyShift action_80
action_69 _ = happyFail (happyExpListPerState 69)

action_70 _ = happyReduce_7

action_71 _ = happyReduce_8

action_72 (93) = happyShift action_79
action_72 _ = happyFail (happyExpListPerState 72)

action_73 (95) = happyShift action_78
action_73 _ = happyFail (happyExpListPerState 73)

action_74 (97) = happyShift action_77
action_74 _ = happyFail (happyExpListPerState 74)

action_75 (97) = happyShift action_76
action_75 _ = happyFail (happyExpListPerState 75)

action_76 _ = happyReduce_18

action_77 _ = happyReduce_17

action_78 _ = happyReduce_16

action_79 (7) = happyGoto action_135
action_79 (33) = happyGoto action_20
action_79 (45) = happyGoto action_21
action_79 _ = happyReduce_96

action_80 (49) = happyShift action_56
action_80 (61) = happyShift action_57
action_80 (67) = happyShift action_58
action_80 (69) = happyShift action_59
action_80 (70) = happyShift action_60
action_80 (71) = happyShift action_61
action_80 (72) = happyShift action_62
action_80 (78) = happyShift action_63
action_80 (92) = happyShift action_64
action_80 (98) = happyShift action_65
action_80 (100) = happyShift action_66
action_80 (101) = happyShift action_67
action_80 (18) = happyGoto action_44
action_80 (19) = happyGoto action_45
action_80 (20) = happyGoto action_46
action_80 (22) = happyGoto action_134
action_80 (23) = happyGoto action_48
action_80 (24) = happyGoto action_49
action_80 (25) = happyGoto action_50
action_80 (27) = happyGoto action_51
action_80 (29) = happyGoto action_52
action_80 (31) = happyGoto action_53
action_80 (37) = happyGoto action_54
action_80 (43) = happyGoto action_55
action_80 _ = happyReduce_91

action_81 _ = happyReduce_52

action_82 (49) = happyShift action_56
action_82 (61) = happyShift action_57
action_82 (67) = happyShift action_58
action_82 (69) = happyShift action_59
action_82 (70) = happyShift action_60
action_82 (71) = happyShift action_61
action_82 (72) = happyShift action_62
action_82 (78) = happyShift action_63
action_82 (92) = happyShift action_64
action_82 (93) = happyReduce_102
action_82 (98) = happyShift action_65
action_82 (100) = happyShift action_66
action_82 (101) = happyShift action_67
action_82 (102) = happyReduce_102
action_82 (18) = happyGoto action_44
action_82 (19) = happyGoto action_45
action_82 (20) = happyGoto action_46
action_82 (22) = happyGoto action_131
action_82 (23) = happyGoto action_48
action_82 (24) = happyGoto action_49
action_82 (25) = happyGoto action_50
action_82 (27) = happyGoto action_51
action_82 (29) = happyGoto action_52
action_82 (31) = happyGoto action_53
action_82 (37) = happyGoto action_54
action_82 (41) = happyGoto action_132
action_82 (43) = happyGoto action_55
action_82 (48) = happyGoto action_133
action_82 _ = happyReduce_102

action_83 (103) = happyShift action_130
action_83 _ = happyFail (happyExpListPerState 83)

action_84 (93) = happyShift action_129
action_84 _ = happyFail (happyExpListPerState 84)

action_85 (100) = happyShift action_128
action_85 _ = happyFail (happyExpListPerState 85)

action_86 _ = happyReduce_48

action_87 (49) = happyShift action_56
action_87 (92) = happyShift action_64
action_87 (100) = happyShift action_89
action_87 (31) = happyGoto action_127
action_87 _ = happyFail (happyExpListPerState 87)

action_88 _ = happyReduce_49

action_89 _ = happyReduce_74

action_90 (100) = happyShift action_69
action_90 (19) = happyGoto action_126
action_90 _ = happyFail (happyExpListPerState 90)

action_91 (49) = happyShift action_56
action_91 (92) = happyShift action_64
action_91 (100) = happyShift action_89
action_91 (29) = happyGoto action_125
action_91 (31) = happyGoto action_117
action_91 _ = happyFail (happyExpListPerState 91)

action_92 _ = happyReduce_69

action_93 _ = happyReduce_70

action_94 _ = happyReduce_71

action_95 _ = happyReduce_72

action_96 _ = happyReduce_62

action_97 (94) = happyShift action_121
action_97 (95) = happyShift action_122
action_97 (108) = happyShift action_123
action_97 (109) = happyShift action_124
action_97 (26) = happyGoto action_119
action_97 (28) = happyGoto action_120
action_97 _ = happyReduce_76

action_98 (49) = happyShift action_56
action_98 (92) = happyShift action_64
action_98 (100) = happyShift action_89
action_98 (25) = happyGoto action_118
action_98 (27) = happyGoto action_51
action_98 (29) = happyGoto action_52
action_98 (31) = happyGoto action_117
action_98 _ = happyFail (happyExpListPerState 98)

action_99 (49) = happyShift action_56
action_99 (92) = happyShift action_64
action_99 (100) = happyShift action_89
action_99 (24) = happyGoto action_116
action_99 (25) = happyGoto action_50
action_99 (27) = happyGoto action_51
action_99 (29) = happyGoto action_52
action_99 (31) = happyGoto action_117
action_99 _ = happyFail (happyExpListPerState 99)

action_100 _ = happyReduce_99

action_101 (111) = happyShift action_115
action_101 _ = happyFail (happyExpListPerState 101)

action_102 _ = happyReduce_25

action_103 (100) = happyShift action_114
action_103 _ = happyFail (happyExpListPerState 103)

action_104 (100) = happyShift action_15
action_104 (10) = happyGoto action_113
action_104 _ = happyFail (happyExpListPerState 104)

action_105 (92) = happyShift action_112
action_105 _ = happyFail (happyExpListPerState 105)

action_106 (49) = happyShift action_56
action_106 (61) = happyShift action_57
action_106 (67) = happyShift action_58
action_106 (69) = happyShift action_59
action_106 (70) = happyShift action_60
action_106 (71) = happyShift action_61
action_106 (72) = happyShift action_62
action_106 (78) = happyShift action_63
action_106 (92) = happyShift action_64
action_106 (98) = happyShift action_65
action_106 (100) = happyShift action_66
action_106 (101) = happyShift action_67
action_106 (18) = happyGoto action_44
action_106 (19) = happyGoto action_45
action_106 (20) = happyGoto action_46
action_106 (22) = happyGoto action_111
action_106 (23) = happyGoto action_48
action_106 (24) = happyGoto action_49
action_106 (25) = happyGoto action_50
action_106 (27) = happyGoto action_51
action_106 (29) = happyGoto action_52
action_106 (31) = happyGoto action_53
action_106 (37) = happyGoto action_54
action_106 (43) = happyGoto action_55
action_106 _ = happyReduce_91

action_107 (92) = happyShift action_82
action_107 (96) = happyShift action_80
action_107 (110) = happyShift action_110
action_107 (40) = happyGoto action_109
action_107 _ = happyFail (happyExpListPerState 107)

action_108 _ = happyReduce_23

action_109 (105) = happyShift action_156
action_109 _ = happyFail (happyExpListPerState 109)

action_110 (49) = happyShift action_56
action_110 (61) = happyShift action_57
action_110 (67) = happyShift action_58
action_110 (69) = happyShift action_59
action_110 (70) = happyShift action_60
action_110 (71) = happyShift action_61
action_110 (72) = happyShift action_62
action_110 (78) = happyShift action_63
action_110 (92) = happyShift action_64
action_110 (98) = happyShift action_65
action_110 (100) = happyShift action_66
action_110 (101) = happyShift action_67
action_110 (18) = happyGoto action_44
action_110 (19) = happyGoto action_45
action_110 (20) = happyGoto action_46
action_110 (22) = happyGoto action_155
action_110 (23) = happyGoto action_48
action_110 (24) = happyGoto action_49
action_110 (25) = happyGoto action_50
action_110 (27) = happyGoto action_51
action_110 (29) = happyGoto action_52
action_110 (31) = happyGoto action_53
action_110 (37) = happyGoto action_54
action_110 (43) = happyGoto action_55
action_110 _ = happyReduce_91

action_111 (105) = happyShift action_154
action_111 _ = happyFail (happyExpListPerState 111)

action_112 (100) = happyShift action_69
action_112 (17) = happyGoto action_152
action_112 (18) = happyGoto action_153
action_112 (19) = happyGoto action_45
action_112 (37) = happyGoto action_54
action_112 (43) = happyGoto action_55
action_112 _ = happyReduce_91

action_113 (105) = happyShift action_150
action_113 (110) = happyShift action_151
action_113 _ = happyFail (happyExpListPerState 113)

action_114 (64) = happyShift action_149
action_114 _ = happyFail (happyExpListPerState 114)

action_115 (49) = happyShift action_56
action_115 (61) = happyShift action_57
action_115 (67) = happyShift action_58
action_115 (69) = happyShift action_59
action_115 (70) = happyShift action_60
action_115 (71) = happyShift action_61
action_115 (72) = happyShift action_62
action_115 (78) = happyShift action_63
action_115 (92) = happyShift action_64
action_115 (98) = happyShift action_65
action_115 (100) = happyShift action_66
action_115 (101) = happyShift action_67
action_115 (18) = happyGoto action_44
action_115 (19) = happyGoto action_45
action_115 (20) = happyGoto action_46
action_115 (22) = happyGoto action_148
action_115 (23) = happyGoto action_48
action_115 (24) = happyGoto action_49
action_115 (25) = happyGoto action_50
action_115 (27) = happyGoto action_51
action_115 (29) = happyGoto action_52
action_115 (31) = happyGoto action_53
action_115 (37) = happyGoto action_54
action_115 (43) = happyGoto action_55
action_115 _ = happyReduce_91

action_116 _ = happyReduce_57

action_117 (87) = happyShift action_92
action_117 (88) = happyShift action_93
action_117 (89) = happyShift action_94
action_117 (90) = happyShift action_95
action_117 (30) = happyGoto action_91
action_117 _ = happyReduce_68

action_118 _ = happyReduce_59

action_119 _ = happyReduce_95

action_120 (49) = happyShift action_56
action_120 (92) = happyShift action_64
action_120 (100) = happyShift action_89
action_120 (29) = happyGoto action_147
action_120 (31) = happyGoto action_117
action_120 _ = happyFail (happyExpListPerState 120)

action_121 _ = happyReduce_64

action_122 _ = happyReduce_63

action_123 _ = happyReduce_65

action_124 _ = happyReduce_66

action_125 _ = happyReduce_67

action_126 _ = happyReduce_93

action_127 (102) = happyShift action_146
action_127 _ = happyFail (happyExpListPerState 127)

action_128 (107) = happyShift action_145
action_128 _ = happyFail (happyExpListPerState 128)

action_129 _ = happyReduce_75

action_130 (67) = happyShift action_141
action_130 (68) = happyShift action_142
action_130 (73) = happyShift action_143
action_130 (75) = happyShift action_144
action_130 (12) = happyGoto action_140
action_130 _ = happyFail (happyExpListPerState 130)

action_131 _ = happyReduce_103

action_132 (93) = happyShift action_139
action_132 _ = happyFail (happyExpListPerState 132)

action_133 (102) = happyShift action_138
action_133 _ = happyReduce_87

action_134 (112) = happyShift action_137
action_134 _ = happyFail (happyExpListPerState 134)

action_135 (98) = happyShift action_40
action_135 (13) = happyGoto action_38
action_135 (38) = happyGoto action_136
action_135 _ = happyReduce_82

action_136 _ = happyReduce_4

action_137 (49) = happyShift action_56
action_137 (61) = happyShift action_57
action_137 (67) = happyShift action_58
action_137 (69) = happyShift action_59
action_137 (70) = happyShift action_60
action_137 (71) = happyShift action_61
action_137 (72) = happyShift action_62
action_137 (78) = happyShift action_63
action_137 (92) = happyShift action_64
action_137 (98) = happyShift action_65
action_137 (100) = happyShift action_66
action_137 (101) = happyShift action_67
action_137 (18) = happyGoto action_44
action_137 (19) = happyGoto action_45
action_137 (20) = happyGoto action_46
action_137 (22) = happyGoto action_169
action_137 (23) = happyGoto action_48
action_137 (24) = happyGoto action_49
action_137 (25) = happyGoto action_50
action_137 (27) = happyGoto action_51
action_137 (29) = happyGoto action_52
action_137 (31) = happyGoto action_53
action_137 (37) = happyGoto action_54
action_137 (43) = happyGoto action_55
action_137 _ = happyReduce_91

action_138 (49) = happyShift action_56
action_138 (61) = happyShift action_57
action_138 (67) = happyShift action_58
action_138 (69) = happyShift action_59
action_138 (70) = happyShift action_60
action_138 (71) = happyShift action_61
action_138 (72) = happyShift action_62
action_138 (78) = happyShift action_63
action_138 (92) = happyShift action_64
action_138 (98) = happyShift action_65
action_138 (100) = happyShift action_66
action_138 (101) = happyShift action_67
action_138 (18) = happyGoto action_44
action_138 (19) = happyGoto action_45
action_138 (20) = happyGoto action_46
action_138 (22) = happyGoto action_168
action_138 (23) = happyGoto action_48
action_138 (24) = happyGoto action_49
action_138 (25) = happyGoto action_50
action_138 (27) = happyGoto action_51
action_138 (29) = happyGoto action_52
action_138 (31) = happyGoto action_53
action_138 (37) = happyGoto action_54
action_138 (43) = happyGoto action_55
action_138 _ = happyReduce_91

action_139 _ = happyReduce_86

action_140 (83) = happyShift action_167
action_140 _ = happyFail (happyExpListPerState 140)

action_141 _ = happyReduce_19

action_142 _ = happyReduce_20

action_143 _ = happyReduce_21

action_144 _ = happyReduce_22

action_145 (49) = happyShift action_56
action_145 (61) = happyShift action_57
action_145 (67) = happyShift action_58
action_145 (69) = happyShift action_59
action_145 (70) = happyShift action_60
action_145 (71) = happyShift action_61
action_145 (72) = happyShift action_62
action_145 (78) = happyShift action_63
action_145 (92) = happyShift action_64
action_145 (98) = happyShift action_65
action_145 (100) = happyShift action_66
action_145 (101) = happyShift action_67
action_145 (18) = happyGoto action_44
action_145 (19) = happyGoto action_45
action_145 (20) = happyGoto action_46
action_145 (22) = happyGoto action_166
action_145 (23) = happyGoto action_48
action_145 (24) = happyGoto action_49
action_145 (25) = happyGoto action_50
action_145 (27) = happyGoto action_51
action_145 (29) = happyGoto action_52
action_145 (31) = happyGoto action_53
action_145 (37) = happyGoto action_54
action_145 (43) = happyGoto action_55
action_145 _ = happyReduce_91

action_146 (49) = happyShift action_165
action_146 _ = happyFail (happyExpListPerState 146)

action_147 _ = happyReduce_61

action_148 (105) = happyShift action_164
action_148 _ = happyFail (happyExpListPerState 148)

action_149 (96) = happyShift action_163
action_149 _ = happyFail (happyExpListPerState 149)

action_150 _ = happyReduce_27

action_151 (49) = happyShift action_56
action_151 (61) = happyShift action_57
action_151 (67) = happyShift action_58
action_151 (69) = happyShift action_59
action_151 (70) = happyShift action_60
action_151 (71) = happyShift action_61
action_151 (72) = happyShift action_62
action_151 (78) = happyShift action_63
action_151 (92) = happyShift action_64
action_151 (98) = happyShift action_65
action_151 (100) = happyShift action_66
action_151 (101) = happyShift action_67
action_151 (18) = happyGoto action_44
action_151 (19) = happyGoto action_45
action_151 (20) = happyGoto action_46
action_151 (22) = happyGoto action_162
action_151 (23) = happyGoto action_48
action_151 (24) = happyGoto action_49
action_151 (25) = happyGoto action_50
action_151 (27) = happyGoto action_51
action_151 (29) = happyGoto action_52
action_151 (31) = happyGoto action_53
action_151 (37) = happyGoto action_54
action_151 (43) = happyGoto action_55
action_151 _ = happyReduce_91

action_152 (93) = happyShift action_161
action_152 _ = happyFail (happyExpListPerState 152)

action_153 (58) = happyShift action_160
action_153 (16) = happyGoto action_158
action_153 (39) = happyGoto action_159
action_153 _ = happyReduce_84

action_154 _ = happyReduce_26

action_155 (105) = happyShift action_157
action_155 _ = happyFail (happyExpListPerState 155)

action_156 _ = happyReduce_33

action_157 _ = happyReduce_29

action_158 _ = happyReduce_85

action_159 _ = happyReduce_35

action_160 (57) = happyShift action_180
action_160 _ = happyFail (happyExpListPerState 160)

action_161 (52) = happyShift action_34
action_161 (53) = happyShift action_35
action_161 (54) = happyShift action_36
action_161 (55) = happyShift action_37
action_161 (8) = happyGoto action_179
action_161 _ = happyFail (happyExpListPerState 161)

action_162 (105) = happyShift action_178
action_162 _ = happyFail (happyExpListPerState 162)

action_163 (49) = happyShift action_56
action_163 (61) = happyShift action_57
action_163 (67) = happyShift action_58
action_163 (69) = happyShift action_59
action_163 (70) = happyShift action_60
action_163 (71) = happyShift action_61
action_163 (72) = happyShift action_62
action_163 (78) = happyShift action_63
action_163 (92) = happyShift action_64
action_163 (98) = happyShift action_65
action_163 (100) = happyShift action_66
action_163 (101) = happyShift action_67
action_163 (18) = happyGoto action_44
action_163 (19) = happyGoto action_45
action_163 (20) = happyGoto action_46
action_163 (22) = happyGoto action_177
action_163 (23) = happyGoto action_48
action_163 (24) = happyGoto action_49
action_163 (25) = happyGoto action_50
action_163 (27) = happyGoto action_51
action_163 (29) = happyGoto action_52
action_163 (31) = happyGoto action_53
action_163 (37) = happyGoto action_54
action_163 (43) = happyGoto action_55
action_163 _ = happyReduce_91

action_164 _ = happyReduce_30

action_165 (93) = happyShift action_176
action_165 _ = happyFail (happyExpListPerState 165)

action_166 (93) = happyShift action_175
action_166 _ = happyFail (happyExpListPerState 166)

action_167 (79) = happyShift action_172
action_167 (80) = happyShift action_173
action_167 (101) = happyShift action_174
action_167 (21) = happyGoto action_171
action_167 _ = happyFail (happyExpListPerState 167)

action_168 _ = happyReduce_104

action_169 (97) = happyShift action_170
action_169 _ = happyFail (happyExpListPerState 169)

action_170 _ = happyReduce_37

action_171 (99) = happyShift action_186
action_171 _ = happyFail (happyExpListPerState 171)

action_172 (100) = happyShift action_185
action_172 _ = happyFail (happyExpListPerState 172)

action_173 (100) = happyShift action_184
action_173 _ = happyFail (happyExpListPerState 173)

action_174 _ = happyReduce_42

action_175 _ = happyReduce_51

action_176 _ = happyReduce_50

action_177 (112) = happyShift action_183
action_177 _ = happyFail (happyExpListPerState 177)

action_178 _ = happyReduce_28

action_179 (98) = happyShift action_40
action_179 (13) = happyGoto action_182
action_179 _ = happyFail (happyExpListPerState 179)

action_180 (49) = happyShift action_56
action_180 (61) = happyShift action_57
action_180 (67) = happyShift action_58
action_180 (69) = happyShift action_59
action_180 (70) = happyShift action_60
action_180 (71) = happyShift action_61
action_180 (72) = happyShift action_62
action_180 (78) = happyShift action_63
action_180 (92) = happyShift action_64
action_180 (98) = happyShift action_65
action_180 (100) = happyShift action_66
action_180 (101) = happyShift action_67
action_180 (18) = happyGoto action_44
action_180 (19) = happyGoto action_45
action_180 (20) = happyGoto action_46
action_180 (22) = happyGoto action_181
action_180 (23) = happyGoto action_48
action_180 (24) = happyGoto action_49
action_180 (25) = happyGoto action_50
action_180 (27) = happyGoto action_51
action_180 (29) = happyGoto action_52
action_180 (31) = happyGoto action_53
action_180 (37) = happyGoto action_54
action_180 (43) = happyGoto action_55
action_180 _ = happyReduce_91

action_181 _ = happyReduce_34

action_182 _ = happyReduce_31

action_183 (49) = happyShift action_56
action_183 (61) = happyShift action_57
action_183 (67) = happyShift action_58
action_183 (69) = happyShift action_59
action_183 (70) = happyShift action_60
action_183 (71) = happyShift action_61
action_183 (72) = happyShift action_62
action_183 (78) = happyShift action_63
action_183 (92) = happyShift action_64
action_183 (98) = happyShift action_65
action_183 (100) = happyShift action_66
action_183 (101) = happyShift action_67
action_183 (18) = happyGoto action_44
action_183 (19) = happyGoto action_45
action_183 (20) = happyGoto action_46
action_183 (22) = happyGoto action_189
action_183 (23) = happyGoto action_48
action_183 (24) = happyGoto action_49
action_183 (25) = happyGoto action_50
action_183 (27) = happyGoto action_51
action_183 (29) = happyGoto action_52
action_183 (31) = happyGoto action_53
action_183 (37) = happyGoto action_54
action_183 (43) = happyGoto action_55
action_183 _ = happyReduce_91

action_184 (104) = happyShift action_188
action_184 _ = happyFail (happyExpListPerState 184)

action_185 (82) = happyShift action_187
action_185 _ = happyFail (happyExpListPerState 185)

action_186 _ = happyReduce_38

action_187 (96) = happyShift action_192
action_187 _ = happyFail (happyExpListPerState 187)

action_188 (92) = happyShift action_82
action_188 (40) = happyGoto action_191
action_188 _ = happyFail (happyExpListPerState 188)

action_189 (97) = happyShift action_190
action_189 _ = happyFail (happyExpListPerState 189)

action_190 (56) = happyShift action_194
action_190 _ = happyFail (happyExpListPerState 190)

action_191 _ = happyReduce_39

action_192 (49) = happyShift action_56
action_192 (61) = happyShift action_57
action_192 (67) = happyShift action_58
action_192 (69) = happyShift action_59
action_192 (70) = happyShift action_60
action_192 (71) = happyShift action_61
action_192 (72) = happyShift action_62
action_192 (78) = happyShift action_63
action_192 (92) = happyShift action_64
action_192 (98) = happyShift action_65
action_192 (100) = happyShift action_66
action_192 (101) = happyShift action_67
action_192 (18) = happyGoto action_44
action_192 (19) = happyGoto action_45
action_192 (20) = happyGoto action_46
action_192 (22) = happyGoto action_193
action_192 (23) = happyGoto action_48
action_192 (24) = happyGoto action_49
action_192 (25) = happyGoto action_50
action_192 (27) = happyGoto action_51
action_192 (29) = happyGoto action_52
action_192 (31) = happyGoto action_53
action_192 (37) = happyGoto action_54
action_192 (43) = happyGoto action_55
action_192 _ = happyReduce_91

action_193 (112) = happyShift action_196
action_193 _ = happyFail (happyExpListPerState 193)

action_194 (100) = happyShift action_69
action_194 (17) = happyGoto action_195
action_194 (18) = happyGoto action_153
action_194 (19) = happyGoto action_45
action_194 (37) = happyGoto action_54
action_194 (43) = happyGoto action_55
action_194 _ = happyReduce_91

action_195 (7) = happyGoto action_198
action_195 (33) = happyGoto action_20
action_195 (45) = happyGoto action_21
action_195 _ = happyReduce_96

action_196 (49) = happyShift action_56
action_196 (61) = happyShift action_57
action_196 (67) = happyShift action_58
action_196 (69) = happyShift action_59
action_196 (70) = happyShift action_60
action_196 (71) = happyShift action_61
action_196 (72) = happyShift action_62
action_196 (78) = happyShift action_63
action_196 (92) = happyShift action_64
action_196 (98) = happyShift action_65
action_196 (100) = happyShift action_66
action_196 (101) = happyShift action_67
action_196 (18) = happyGoto action_44
action_196 (19) = happyGoto action_45
action_196 (20) = happyGoto action_46
action_196 (22) = happyGoto action_197
action_196 (23) = happyGoto action_48
action_196 (24) = happyGoto action_49
action_196 (25) = happyGoto action_50
action_196 (27) = happyGoto action_51
action_196 (29) = happyGoto action_52
action_196 (31) = happyGoto action_53
action_196 (37) = happyGoto action_54
action_196 (43) = happyGoto action_55
action_196 _ = happyReduce_91

action_197 (97) = happyShift action_200
action_197 _ = happyFail (happyExpListPerState 197)

action_198 (98) = happyShift action_40
action_198 (13) = happyGoto action_199
action_198 _ = happyFail (happyExpListPerState 198)

action_199 _ = happyReduce_32

action_200 (104) = happyShift action_201
action_200 _ = happyFail (happyExpListPerState 200)

action_201 (80) = happyShift action_203
action_201 (92) = happyShift action_82
action_201 (40) = happyGoto action_202
action_201 _ = happyFail (happyExpListPerState 201)

action_202 _ = happyReduce_40

action_203 (100) = happyShift action_204
action_203 _ = happyFail (happyExpListPerState 203)

action_204 (82) = happyShift action_205
action_204 _ = happyFail (happyExpListPerState 204)

action_205 (96) = happyShift action_206
action_205 _ = happyFail (happyExpListPerState 205)

action_206 (49) = happyShift action_56
action_206 (61) = happyShift action_57
action_206 (67) = happyShift action_58
action_206 (69) = happyShift action_59
action_206 (70) = happyShift action_60
action_206 (71) = happyShift action_61
action_206 (72) = happyShift action_62
action_206 (78) = happyShift action_63
action_206 (92) = happyShift action_64
action_206 (98) = happyShift action_65
action_206 (100) = happyShift action_66
action_206 (101) = happyShift action_67
action_206 (18) = happyGoto action_44
action_206 (19) = happyGoto action_45
action_206 (20) = happyGoto action_46
action_206 (22) = happyGoto action_207
action_206 (23) = happyGoto action_48
action_206 (24) = happyGoto action_49
action_206 (25) = happyGoto action_50
action_206 (27) = happyGoto action_51
action_206 (29) = happyGoto action_52
action_206 (31) = happyGoto action_53
action_206 (37) = happyGoto action_54
action_206 (43) = happyGoto action_55
action_206 _ = happyReduce_91

action_207 (112) = happyShift action_208
action_207 _ = happyFail (happyExpListPerState 207)

action_208 (49) = happyShift action_56
action_208 (61) = happyShift action_57
action_208 (67) = happyShift action_58
action_208 (69) = happyShift action_59
action_208 (70) = happyShift action_60
action_208 (71) = happyShift action_61
action_208 (72) = happyShift action_62
action_208 (78) = happyShift action_63
action_208 (92) = happyShift action_64
action_208 (98) = happyShift action_65
action_208 (100) = happyShift action_66
action_208 (101) = happyShift action_67
action_208 (18) = happyGoto action_44
action_208 (19) = happyGoto action_45
action_208 (20) = happyGoto action_46
action_208 (22) = happyGoto action_209
action_208 (23) = happyGoto action_48
action_208 (24) = happyGoto action_49
action_208 (25) = happyGoto action_50
action_208 (27) = happyGoto action_51
action_208 (29) = happyGoto action_52
action_208 (31) = happyGoto action_53
action_208 (37) = happyGoto action_54
action_208 (43) = happyGoto action_55
action_208 _ = happyReduce_91

action_209 (97) = happyShift action_210
action_209 _ = happyFail (happyExpListPerState 209)

action_210 (104) = happyShift action_211
action_210 _ = happyFail (happyExpListPerState 210)

action_211 (92) = happyShift action_82
action_211 (40) = happyGoto action_212
action_211 _ = happyFail (happyExpListPerState 211)

action_212 _ = happyReduce_41

happyReduce_1 = happySpecReduce_1  4 happyReduction_1
happyReduction_1 (HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn4
		 (happy_var_1
	)
happyReduction_1 _  = notHappyAtAll 

happyReduce_2 = happySpecReduce_1  5 happyReduction_2
happyReduction_2 (HappyAbsSyn35  happy_var_1)
	 =  HappyAbsSyn5
		 (happy_var_1
	)
happyReduction_2 _  = notHappyAtAll 

happyReduce_3 = happySpecReduce_1  6 happyReduction_3
happyReduction_3 (HappyTerminal (( _, L.TDafny happy_var_1  )))
	 =  HappyAbsSyn6
		 (inj (QDafny happy_var_1)
	)
happyReduction_3 _  = notHappyAtAll 

happyReduce_4 = happyMonadReduce 11 6 happyReduction_4
happyReduction_4 ((HappyAbsSyn38  happy_var_11) `HappyStk`
	(HappyAbsSyn7  happy_var_10) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn9  happy_var_8) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn9  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (( _, L.TId happy_var_2     ))) `HappyStk`
	_ `HappyStk`
	happyRest) tk
	 = happyThen (((  ((\(rs, es) -> inj (QMethod happy_var_2 happy_var_4 happy_var_8 rs es happy_var_11)) `fmap` (requireEnsures happy_var_10))))
	) (\r -> happyReturn (HappyAbsSyn6 r))

happyReduce_5 = happyMonadReduce 7 6 happyReduction_5
happyReduction_5 ((HappyAbsSyn38  happy_var_7) `HappyStk`
	(HappyAbsSyn7  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn9  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (( _, L.TId happy_var_2     ))) `HappyStk`
	_ `HappyStk`
	happyRest) tk
	 = happyThen (((  ((\(rs, es) -> inj (QMethod happy_var_2 happy_var_4 [] rs es happy_var_7)) `fmap` (requireEnsures happy_var_6))))
	) (\r -> happyReturn (HappyAbsSyn6 r))

happyReduce_6 = happySpecReduce_1  7 happyReduction_6
happyReduction_6 (HappyAbsSyn33  happy_var_1)
	 =  HappyAbsSyn7
		 (happy_var_1
	)
happyReduction_6 _  = notHappyAtAll 

happyReduce_7 = happySpecReduce_2  8 happyReduction_7
happyReduction_7 (HappyAbsSyn22  happy_var_2)
	_
	 =  HappyAbsSyn8
		 (Requires happy_var_2
	)
happyReduction_7 _ _  = notHappyAtAll 

happyReduce_8 = happySpecReduce_2  8 happyReduction_8
happyReduction_8 (HappyAbsSyn22  happy_var_2)
	_
	 =  HappyAbsSyn8
		 (Ensures happy_var_2
	)
happyReduction_8 _ _  = notHappyAtAll 

happyReduce_9 = happySpecReduce_2  8 happyReduction_9
happyReduction_9 (HappyAbsSyn22  happy_var_2)
	_
	 =  HappyAbsSyn8
		 (Invariants happy_var_2
	)
happyReduction_9 _ _  = notHappyAtAll 

happyReduce_10 = happySpecReduce_2  8 happyReduction_10
happyReduction_10 (HappyAbsSyn18  happy_var_2)
	_
	 =  HappyAbsSyn8
		 (Separates happy_var_2
	)
happyReduction_10 _ _  = notHappyAtAll 

happyReduce_11 = happySpecReduce_1  9 happyReduction_11
happyReduction_11 (HappyAbsSyn36  happy_var_1)
	 =  HappyAbsSyn9
		 (happy_var_1
	)
happyReduction_11 _  = notHappyAtAll 

happyReduce_12 = happySpecReduce_3  10 happyReduction_12
happyReduction_12 (HappyAbsSyn11  happy_var_3)
	_
	(HappyTerminal (( _, L.TId happy_var_1     )))
	 =  HappyAbsSyn10
		 (Binding happy_var_1 happy_var_3
	)
happyReduction_12 _ _ _  = notHappyAtAll 

happyReduce_13 = happySpecReduce_1  11 happyReduction_13
happyReduction_13 _
	 =  HappyAbsSyn11
		 (TNat
	)

happyReduce_14 = happySpecReduce_1  11 happyReduction_14
happyReduction_14 _
	 =  HappyAbsSyn11
		 (TInt
	)

happyReduce_15 = happySpecReduce_1  11 happyReduction_15
happyReduction_15 _
	 =  HappyAbsSyn11
		 (TBool
	)

happyReduce_16 = happyReduce 4 11 happyReduction_16
happyReduction_16 (_ `HappyStk`
	(HappyAbsSyn11  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn11
		 (TSeq happy_var_3
	) `HappyStk` happyRest

happyReduce_17 = happyReduce 4 11 happyReduction_17
happyReduction_17 (_ `HappyStk`
	(HappyTerminal (( _, L.TLitInt happy_var_3 ))) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn11
		 (TQReg (ANat happy_var_3)
	) `HappyStk` happyRest

happyReduce_18 = happyReduce 4 11 happyReduction_18
happyReduction_18 (_ `HappyStk`
	(HappyTerminal (( _, L.TId happy_var_3     ))) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn11
		 (TQReg (AVar happy_var_3)
	) `HappyStk` happyRest

happyReduce_19 = happySpecReduce_1  12 happyReduction_19
happyReduction_19 _
	 =  HappyAbsSyn12
		 (TNor
	)

happyReduce_20 = happySpecReduce_1  12 happyReduction_20
happyReduction_20 _
	 =  HappyAbsSyn12
		 (THad
	)

happyReduce_21 = happySpecReduce_1  12 happyReduction_21
happyReduction_21 _
	 =  HappyAbsSyn12
		 (TEN
	)

happyReduce_22 = happySpecReduce_1  12 happyReduction_22
happyReduction_22 _
	 =  HappyAbsSyn12
		 (TEN01
	)

happyReduce_23 = happySpecReduce_3  13 happyReduction_23
happyReduction_23 _
	(HappyAbsSyn14  happy_var_2)
	_
	 =  HappyAbsSyn13
		 (Block happy_var_2
	)
happyReduction_23 _ _ _  = notHappyAtAll 

happyReduce_24 = happySpecReduce_1  14 happyReduction_24
happyReduction_24 (HappyAbsSyn34  happy_var_1)
	 =  HappyAbsSyn14
		 (happy_var_1
	)
happyReduction_24 _  = notHappyAtAll 

happyReduce_25 = happySpecReduce_1  15 happyReduction_25
happyReduction_25 (HappyTerminal (( _, L.TDafny happy_var_1  )))
	 =  HappyAbsSyn15
		 (SDafny happy_var_1
	)
happyReduction_25 _  = notHappyAtAll 

happyReduce_26 = happySpecReduce_3  15 happyReduction_26
happyReduction_26 _
	(HappyAbsSyn22  happy_var_2)
	_
	 =  HappyAbsSyn15
		 (SAssert happy_var_2
	)
happyReduction_26 _ _ _  = notHappyAtAll 

happyReduce_27 = happySpecReduce_3  15 happyReduction_27
happyReduction_27 _
	(HappyAbsSyn10  happy_var_2)
	_
	 =  HappyAbsSyn15
		 (SVar happy_var_2 Nothing
	)
happyReduction_27 _ _ _  = notHappyAtAll 

happyReduce_28 = happyReduce 5 15 happyReduction_28
happyReduction_28 (_ `HappyStk`
	(HappyAbsSyn22  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn10  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn15
		 (SVar happy_var_2 (Just happy_var_4)
	) `HappyStk` happyRest

happyReduce_29 = happyReduce 4 15 happyReduction_29
happyReduction_29 (_ `HappyStk`
	(HappyAbsSyn22  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (( _, L.TId happy_var_1     ))) `HappyStk`
	happyRest)
	 = HappyAbsSyn15
		 (happy_var_1 ::=: happy_var_3
	) `HappyStk` happyRest

happyReduce_30 = happyReduce 4 15 happyReduction_30
happyReduction_30 (_ `HappyStk`
	(HappyAbsSyn22  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn18  happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn15
		 (happy_var_1 :*=: happy_var_3
	) `HappyStk` happyRest

happyReduce_31 = happyMonadReduce 6 15 happyReduction_31
happyReduction_31 ((HappyAbsSyn13  happy_var_6) `HappyStk`
	(HappyAbsSyn8  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn17  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest) tk
	 = happyThen ((( do sep <- separatesOnly happy_var_5; return $ SIf happy_var_3 sep happy_var_6))
	) (\r -> happyReturn (HappyAbsSyn15 r))

happyReduce_32 = happyMonadReduce 12 15 happyReduction_32
happyReduction_32 ((HappyAbsSyn13  happy_var_12) `HappyStk`
	(HappyAbsSyn7  happy_var_11) `HappyStk`
	(HappyAbsSyn17  happy_var_10) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn22  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn22  happy_var_5) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyTerminal (( _, L.TId happy_var_2     ))) `HappyStk`
	_ `HappyStk`
	happyRest) tk
	 = happyThen ((( do (invs, sep) <- invariantSeperates happy_var_11; return $ SFor happy_var_2 happy_var_5 happy_var_7 happy_var_10 invs sep happy_var_12))
	) (\r -> happyReturn (HappyAbsSyn15 r))

happyReduce_33 = happySpecReduce_3  15 happyReduction_33
happyReduction_33 _
	(HappyAbsSyn40  happy_var_2)
	(HappyTerminal (( _, L.TId happy_var_1     )))
	 =  HappyAbsSyn15
		 (SCall happy_var_1 happy_var_2
	)
happyReduction_33 _ _ _  = notHappyAtAll 

happyReduce_34 = happySpecReduce_3  16 happyReduction_34
happyReduction_34 (HappyAbsSyn22  happy_var_3)
	_
	_
	 =  HappyAbsSyn16
		 (happy_var_3
	)
happyReduction_34 _ _ _  = notHappyAtAll 

happyReduce_35 = happySpecReduce_2  17 happyReduction_35
happyReduction_35 (HappyAbsSyn39  happy_var_2)
	(HappyAbsSyn18  happy_var_1)
	 =  HappyAbsSyn17
		 (GEPartition happy_var_1 happy_var_2
	)
happyReduction_35 _ _  = notHappyAtAll 

happyReduce_36 = happySpecReduce_1  18 happyReduction_36
happyReduction_36 (HappyAbsSyn37  happy_var_1)
	 =  HappyAbsSyn18
		 (Partition $ happy_var_1
	)
happyReduction_36 _  = notHappyAtAll 

happyReduce_37 = happyReduce 6 19 happyReduction_37
happyReduction_37 (_ `HappyStk`
	(HappyAbsSyn22  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn22  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (( _, L.TId happy_var_1     ))) `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 (Range happy_var_1 happy_var_3 happy_var_5
	) `HappyStk` happyRest

happyReduce_38 = happyReduce 7 20 happyReduction_38
happyReduction_38 (_ `HappyStk`
	(HappyAbsSyn21  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn12  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn18  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn16
		 (ESpec happy_var_2 happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_39 = happyReduce 4 21 happyReduction_39
happyReduction_39 ((HappyAbsSyn40  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (( _, L.TId happy_var_2     ))) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn21
		 (SESpecNor happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_40 = happyReduce 10 21 happyReduction_40
happyReduction_40 ((HappyAbsSyn40  happy_var_10) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn22  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn22  happy_var_5) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyTerminal (( _, L.TId happy_var_2     ))) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn21
		 (SESpecEN happy_var_2 (Intv happy_var_5 happy_var_7) happy_var_10
	) `HappyStk` happyRest

happyReduce_41 = happyReduce 19 21 happyReduction_41
happyReduction_41 ((HappyAbsSyn40  happy_var_19) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn22  happy_var_16) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn22  happy_var_14) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyTerminal (( _, L.TId happy_var_11     ))) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn22  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn22  happy_var_5) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyTerminal (( _, L.TId happy_var_2     ))) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn21
		 (SESpecEN01 happy_var_2 (Intv happy_var_5 happy_var_7) happy_var_11 (Intv happy_var_14 happy_var_16) happy_var_19
	) `HappyStk` happyRest

happyReduce_42 = happySpecReduce_1  21 happyReduction_42
happyReduction_42 _
	 =  HappyAbsSyn21
		 (SEWildcard
	)

happyReduce_43 = happySpecReduce_1  22 happyReduction_43
happyReduction_43 (HappyAbsSyn31  happy_var_1)
	 =  HappyAbsSyn22
		 (happy_var_1
	)
happyReduction_43 _  = notHappyAtAll 

happyReduce_44 = happySpecReduce_1  22 happyReduction_44
happyReduction_44 _
	 =  HappyAbsSyn22
		 (EWildcard
	)

happyReduce_45 = happySpecReduce_1  22 happyReduction_45
happyReduction_45 (HappyAbsSyn16  happy_var_1)
	 =  HappyAbsSyn22
		 (happy_var_1
	)
happyReduction_45 _  = notHappyAtAll 

happyReduce_46 = happySpecReduce_1  22 happyReduction_46
happyReduction_46 (HappyAbsSyn18  happy_var_1)
	 =  HappyAbsSyn22
		 (EPartition happy_var_1
	)
happyReduction_46 _  = notHappyAtAll 

happyReduce_47 = happySpecReduce_1  22 happyReduction_47
happyReduction_47 (HappyAbsSyn23  happy_var_1)
	 =  HappyAbsSyn22
		 (happy_var_1
	)
happyReduction_47 _  = notHappyAtAll 

happyReduce_48 = happySpecReduce_2  22 happyReduction_48
happyReduction_48 (HappyTerminal (( _, L.TId happy_var_2     )))
	_
	 =  HappyAbsSyn22
		 (EMea happy_var_2
	)
happyReduction_48 _ _  = notHappyAtAll 

happyReduce_49 = happySpecReduce_2  22 happyReduction_49
happyReduction_49 (HappyAbsSyn31  happy_var_2)
	_
	 =  HappyAbsSyn22
		 (EOp1 ONot happy_var_2
	)
happyReduction_49 _ _  = notHappyAtAll 

happyReduce_50 = happyReduce 6 22 happyReduction_50
happyReduction_50 (_ `HappyStk`
	(HappyTerminal (( _, L.TLitInt happy_var_5 ))) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn31  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn22
		 (EOp2 ONor happy_var_3 (ENum happy_var_5)
	) `HappyStk` happyRest

happyReduce_51 = happyReduce 6 22 happyReduction_51
happyReduction_51 (_ `HappyStk`
	(HappyAbsSyn22  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (( _, L.TId happy_var_3     ))) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn22
		 (EEmit $ ELambda happy_var_3 happy_var_5
	) `HappyStk` happyRest

happyReduce_52 = happySpecReduce_2  22 happyReduction_52
happyReduction_52 (HappyAbsSyn40  happy_var_2)
	(HappyTerminal (( _, L.TId happy_var_1     )))
	 =  HappyAbsSyn22
		 (EApp happy_var_1 happy_var_2
	)
happyReduction_52 _ _  = notHappyAtAll 

happyReduce_53 = happySpecReduce_1  22 happyReduction_53
happyReduction_53 (HappyAbsSyn16  happy_var_1)
	 =  HappyAbsSyn22
		 (happy_var_1
	)
happyReduction_53 _  = notHappyAtAll 

happyReduce_54 = happySpecReduce_1  23 happyReduction_54
happyReduction_54 _
	 =  HappyAbsSyn23
		 (EHad
	)

happyReduce_55 = happySpecReduce_1  23 happyReduction_55
happyReduction_55 _
	 =  HappyAbsSyn23
		 (EQFT
	)

happyReduce_56 = happySpecReduce_1  23 happyReduction_56
happyReduction_56 _
	 =  HappyAbsSyn23
		 (ERQFT
	)

happyReduce_57 = happySpecReduce_3  24 happyReduction_57
happyReduction_57 (HappyAbsSyn16  happy_var_3)
	_
	(HappyAbsSyn16  happy_var_1)
	 =  HappyAbsSyn16
		 (EOp2 OOr happy_var_1 happy_var_3
	)
happyReduction_57 _ _ _  = notHappyAtAll 

happyReduce_58 = happySpecReduce_1  24 happyReduction_58
happyReduction_58 (HappyAbsSyn16  happy_var_1)
	 =  HappyAbsSyn16
		 (happy_var_1
	)
happyReduction_58 _  = notHappyAtAll 

happyReduce_59 = happySpecReduce_3  25 happyReduction_59
happyReduction_59 (HappyAbsSyn16  happy_var_3)
	_
	(HappyAbsSyn16  happy_var_1)
	 =  HappyAbsSyn16
		 (EOp2 OAnd happy_var_1 happy_var_3
	)
happyReduction_59 _ _ _  = notHappyAtAll 

happyReduce_60 = happySpecReduce_1  25 happyReduction_60
happyReduction_60 (HappyAbsSyn16  happy_var_1)
	 =  HappyAbsSyn16
		 (happy_var_1
	)
happyReduction_60 _  = notHappyAtAll 

happyReduce_61 = happySpecReduce_2  26 happyReduction_61
happyReduction_61 (HappyAbsSyn16  happy_var_2)
	(HappyAbsSyn28  happy_var_1)
	 =  HappyAbsSyn26
		 ((happy_var_1, happy_var_2)
	)
happyReduction_61 _ _  = notHappyAtAll 

happyReduce_62 = happySpecReduce_2  27 happyReduction_62
happyReduction_62 (HappyAbsSyn32  happy_var_2)
	(HappyAbsSyn16  happy_var_1)
	 =  HappyAbsSyn16
		 (unchainExps happy_var_1 happy_var_2
	)
happyReduction_62 _ _  = notHappyAtAll 

happyReduce_63 = happySpecReduce_1  28 happyReduction_63
happyReduction_63 _
	 =  HappyAbsSyn28
		 (OGt
	)

happyReduce_64 = happySpecReduce_1  28 happyReduction_64
happyReduction_64 _
	 =  HappyAbsSyn28
		 (OLt
	)

happyReduce_65 = happySpecReduce_1  28 happyReduction_65
happyReduction_65 _
	 =  HappyAbsSyn28
		 (OGe
	)

happyReduce_66 = happySpecReduce_1  28 happyReduction_66
happyReduction_66 _
	 =  HappyAbsSyn28
		 (OLe
	)

happyReduce_67 = happySpecReduce_3  29 happyReduction_67
happyReduction_67 (HappyAbsSyn16  happy_var_3)
	(HappyAbsSyn28  happy_var_2)
	(HappyAbsSyn31  happy_var_1)
	 =  HappyAbsSyn16
		 (EOp2 happy_var_2 happy_var_1 happy_var_3
	)
happyReduction_67 _ _ _  = notHappyAtAll 

happyReduce_68 = happySpecReduce_1  29 happyReduction_68
happyReduction_68 (HappyAbsSyn31  happy_var_1)
	 =  HappyAbsSyn16
		 (happy_var_1
	)
happyReduction_68 _  = notHappyAtAll 

happyReduce_69 = happySpecReduce_1  30 happyReduction_69
happyReduction_69 _
	 =  HappyAbsSyn28
		 (OAdd
	)

happyReduce_70 = happySpecReduce_1  30 happyReduction_70
happyReduction_70 _
	 =  HappyAbsSyn28
		 (OSub
	)

happyReduce_71 = happySpecReduce_1  30 happyReduction_71
happyReduction_71 _
	 =  HappyAbsSyn28
		 (OMul
	)

happyReduce_72 = happySpecReduce_1  30 happyReduction_72
happyReduction_72 _
	 =  HappyAbsSyn28
		 (OMod
	)

happyReduce_73 = happySpecReduce_1  31 happyReduction_73
happyReduction_73 (HappyTerminal (( _, L.TLitInt happy_var_1 )))
	 =  HappyAbsSyn31
		 (ENum happy_var_1
	)
happyReduction_73 _  = notHappyAtAll 

happyReduce_74 = happySpecReduce_1  31 happyReduction_74
happyReduction_74 (HappyTerminal (( _, L.TId happy_var_1     )))
	 =  HappyAbsSyn31
		 (EVar happy_var_1
	)
happyReduction_74 _  = notHappyAtAll 

happyReduce_75 = happySpecReduce_3  31 happyReduction_75
happyReduction_75 _
	(HappyAbsSyn22  happy_var_2)
	_
	 =  HappyAbsSyn31
		 (happy_var_2
	)
happyReduction_75 _ _ _  = notHappyAtAll 

happyReduce_76 = happySpecReduce_1  32 happyReduction_76
happyReduction_76 (HappyAbsSyn44  happy_var_1)
	 =  HappyAbsSyn32
		 (reverse happy_var_1
	)
happyReduction_76 _  = notHappyAtAll 

happyReduce_77 = happySpecReduce_1  33 happyReduction_77
happyReduction_77 (HappyAbsSyn45  happy_var_1)
	 =  HappyAbsSyn33
		 (reverse happy_var_1
	)
happyReduction_77 _  = notHappyAtAll 

happyReduce_78 = happySpecReduce_1  34 happyReduction_78
happyReduction_78 (HappyAbsSyn46  happy_var_1)
	 =  HappyAbsSyn34
		 (reverse happy_var_1
	)
happyReduction_78 _  = notHappyAtAll 

happyReduce_79 = happySpecReduce_1  35 happyReduction_79
happyReduction_79 (HappyAbsSyn47  happy_var_1)
	 =  HappyAbsSyn35
		 (reverse happy_var_1
	)
happyReduction_79 _  = notHappyAtAll 

happyReduce_80 = happySpecReduce_1  36 happyReduction_80
happyReduction_80 (HappyAbsSyn42  happy_var_1)
	 =  HappyAbsSyn36
		 (reverse happy_var_1
	)
happyReduction_80 _  = notHappyAtAll 

happyReduce_81 = happySpecReduce_1  37 happyReduction_81
happyReduction_81 (HappyAbsSyn43  happy_var_1)
	 =  HappyAbsSyn37
		 (reverse happy_var_1
	)
happyReduction_81 _  = notHappyAtAll 

happyReduce_82 = happySpecReduce_0  38 happyReduction_82
happyReduction_82  =  HappyAbsSyn38
		 (Nothing
	)

happyReduce_83 = happySpecReduce_1  38 happyReduction_83
happyReduction_83 (HappyAbsSyn13  happy_var_1)
	 =  HappyAbsSyn38
		 (Just happy_var_1
	)
happyReduction_83 _  = notHappyAtAll 

happyReduce_84 = happySpecReduce_0  39 happyReduction_84
happyReduction_84  =  HappyAbsSyn39
		 (Nothing
	)

happyReduce_85 = happySpecReduce_1  39 happyReduction_85
happyReduction_85 (HappyAbsSyn16  happy_var_1)
	 =  HappyAbsSyn39
		 (Just happy_var_1
	)
happyReduction_85 _  = notHappyAtAll 

happyReduce_86 = happySpecReduce_3  40 happyReduction_86
happyReduction_86 _
	(HappyAbsSyn41  happy_var_2)
	_
	 =  HappyAbsSyn40
		 (happy_var_2
	)
happyReduction_86 _ _ _  = notHappyAtAll 

happyReduce_87 = happySpecReduce_1  41 happyReduction_87
happyReduction_87 (HappyAbsSyn48  happy_var_1)
	 =  HappyAbsSyn41
		 (reverse happy_var_1
	)
happyReduction_87 _  = notHappyAtAll 

happyReduce_88 = happySpecReduce_0  42 happyReduction_88
happyReduction_88  =  HappyAbsSyn42
		 ([]
	)

happyReduce_89 = happySpecReduce_1  42 happyReduction_89
happyReduction_89 (HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn42
		 ([happy_var_1]
	)
happyReduction_89 _  = notHappyAtAll 

happyReduce_90 = happySpecReduce_3  42 happyReduction_90
happyReduction_90 (HappyAbsSyn10  happy_var_3)
	_
	(HappyAbsSyn42  happy_var_1)
	 =  HappyAbsSyn42
		 (happy_var_3 : happy_var_1
	)
happyReduction_90 _ _ _  = notHappyAtAll 

happyReduce_91 = happySpecReduce_0  43 happyReduction_91
happyReduction_91  =  HappyAbsSyn43
		 ([]
	)

happyReduce_92 = happySpecReduce_1  43 happyReduction_92
happyReduction_92 (HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn43
		 ([happy_var_1]
	)
happyReduction_92 _  = notHappyAtAll 

happyReduce_93 = happySpecReduce_3  43 happyReduction_93
happyReduction_93 (HappyAbsSyn19  happy_var_3)
	_
	(HappyAbsSyn43  happy_var_1)
	 =  HappyAbsSyn43
		 (happy_var_3 : happy_var_1
	)
happyReduction_93 _ _ _  = notHappyAtAll 

happyReduce_94 = happySpecReduce_0  44 happyReduction_94
happyReduction_94  =  HappyAbsSyn44
		 ([]
	)

happyReduce_95 = happySpecReduce_2  44 happyReduction_95
happyReduction_95 (HappyAbsSyn26  happy_var_2)
	(HappyAbsSyn44  happy_var_1)
	 =  HappyAbsSyn44
		 (happy_var_2 : happy_var_1
	)
happyReduction_95 _ _  = notHappyAtAll 

happyReduce_96 = happySpecReduce_0  45 happyReduction_96
happyReduction_96  =  HappyAbsSyn45
		 ([]
	)

happyReduce_97 = happySpecReduce_2  45 happyReduction_97
happyReduction_97 (HappyAbsSyn8  happy_var_2)
	(HappyAbsSyn45  happy_var_1)
	 =  HappyAbsSyn45
		 (happy_var_2 : happy_var_1
	)
happyReduction_97 _ _  = notHappyAtAll 

happyReduce_98 = happySpecReduce_0  46 happyReduction_98
happyReduction_98  =  HappyAbsSyn46
		 ([]
	)

happyReduce_99 = happySpecReduce_2  46 happyReduction_99
happyReduction_99 (HappyAbsSyn15  happy_var_2)
	(HappyAbsSyn46  happy_var_1)
	 =  HappyAbsSyn46
		 (happy_var_2 : happy_var_1
	)
happyReduction_99 _ _  = notHappyAtAll 

happyReduce_100 = happySpecReduce_0  47 happyReduction_100
happyReduction_100  =  HappyAbsSyn47
		 ([]
	)

happyReduce_101 = happySpecReduce_2  47 happyReduction_101
happyReduction_101 (HappyAbsSyn6  happy_var_2)
	(HappyAbsSyn47  happy_var_1)
	 =  HappyAbsSyn47
		 (happy_var_2 : happy_var_1
	)
happyReduction_101 _ _  = notHappyAtAll 

happyReduce_102 = happySpecReduce_0  48 happyReduction_102
happyReduction_102  =  HappyAbsSyn48
		 ([]
	)

happyReduce_103 = happySpecReduce_1  48 happyReduction_103
happyReduction_103 (HappyAbsSyn22  happy_var_1)
	 =  HappyAbsSyn48
		 ([happy_var_1]
	)
happyReduction_103 _  = notHappyAtAll 

happyReduce_104 = happySpecReduce_3  48 happyReduction_104
happyReduction_104 (HappyAbsSyn22  happy_var_3)
	_
	(HappyAbsSyn48  happy_var_1)
	 =  HappyAbsSyn48
		 (happy_var_3 : happy_var_1
	)
happyReduction_104 _ _ _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 113 113 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	( _, L.TLitInt happy_dollar_dollar ) -> cont 49;
	( _, L.TDafny happy_dollar_dollar  ) -> cont 50;
	( _, L.TMethod    ) -> cont 51;
	( _, L.TEnsures   ) -> cont 52;
	( _, L.TRequires  ) -> cont 53;
	( _, L.TSeparates ) -> cont 54;
	( _, L.TInv       ) -> cont 55;
	( _, L.TWith      ) -> cont 56;
	( _, L.TAt      ) -> cont 57;
	( _, L.TSplit      ) -> cont 58;
	( _, L.TFor       ) -> cont 59;
	( _, L.TReturns   ) -> cont 60;
	( _, L.TNot       ) -> cont 61;
	( _, L.TNat       ) -> cont 62;
	( _, L.TInt       ) -> cont 63;
	( _, L.TIn        ) -> cont 64;
	( _, L.TBool      ) -> cont 65;
	( _, L.TSeq       ) -> cont 66;
	( _, L.TNor       ) -> cont 67;
	( _, L.THad       ) -> cont 68;
	( _, L.THApp      ) -> cont 69;
	( _, L.TQFT       ) -> cont 70;
	( _, L.TRQFT      ) -> cont 71;
	( _, L.TMea       ) -> cont 72;
	( _, L.TEN        ) -> cont 73;
	( _, L.TQReg      ) -> cont 74;
	( _, L.TEN01      ) -> cont 75;
	( _, L.TVar       ) -> cont 76;
	( _, L.TIf        ) -> cont 77;
	( _, L.TCl        ) -> cont 78;
	( _, L.TUnicodeSum    ) -> cont 79;
	( _, L.TUnicodeTensor ) -> cont 80;
	( _, L.TUnicodeTensor ) -> cont 81;
	( _, L.TUnicodeIn     ) -> cont 82;
	( _, L.TUnicodeMap    ) -> cont 83;
	( _, L.TAssert    ) -> cont 84;
	( _, L.TOr        ) -> cont 85;
	( _, L.TAnd       ) -> cont 86;
	( _, L.TAdd       ) -> cont 87;
	( _, L.TSub       ) -> cont 88;
	( _, L.TMul       ) -> cont 89;
	( _, L.TMod       ) -> cont 90;
	( _, L.TBar       ) -> cont 91;
	( _, L.TLPar      ) -> cont 92;
	( _, L.TRPar      ) -> cont 93;
	( _, L.TLAng      ) -> cont 94;
	( _, L.TRAng      ) -> cont 95;
	( _, L.TLBracket  ) -> cont 96;
	( _, L.TRBracket  ) -> cont 97;
	( _, L.TLBrace    ) -> cont 98;
	( _, L.TRBrace    ) -> cont 99;
	( _, L.TId happy_dollar_dollar     ) -> cont 100;
	( _, L.TWildcard  ) -> cont 101;
	( _, L.TComma     ) -> cont 102;
	( _, L.TColon     ) -> cont 103;
	( _, L.TDot       ) -> cont 104;
	( _, L.TSemi      ) -> cont 105;
	( _, L.TEq        ) -> cont 106;
	( _, L.TArrow     ) -> cont 107;
	( _, L.TGe        ) -> cont 108;
	( _, L.TLe        ) -> cont 109;
	( _, L.TAssign    ) -> cont 110;
	( _, L.TApply     ) -> cont 111;
	( _, L.TDots      ) -> cont 112;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 113 tk tks = happyError' (tks, explist)
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
