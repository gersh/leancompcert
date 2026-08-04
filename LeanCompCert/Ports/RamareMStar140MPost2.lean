import LeanCompCert.Ports.RamareMStar140MCore

/-!
# The post-load stage of the `m★` body, part two

`gateBlock`, `ladderBlock`, `productBlock`, `badBlock`, `updateBlock`: the
hundred and seven instructions that run the dyadic check, advance the RS62 log
ladder, compare `5·star·logUp` against `2⁹⁸` through the half-limb product
circuit, count the violations, and carry the block state forward.

Every value is written in `MA`/`MS`/`MMul`/`bitOf`, which are the machine's
`denoteOp` on the nose, so the statements carry the `% 2⁶⁴` truncations rather
than a proof that they do not happen — the same vocabulary `msRef` is written
in.  The instruction names, prefix lists and split equations are a `rfl`
regrouping of the very same lists, so the emitted C is unchanged.
-/

namespace LeanCompCert.Ports.RamareMStar140M

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.BlockDefined
open LeanCompCert.Verified.RegFrame
open LeanCompCert.Ports.RS62
open LeanCompCert.Verified.InstrBlock (srun sval sdest SDefined SAllDefined NoDivI)

/-! ### `gateBlock` -/

private def Bgati0 : Instr := .binop rT1 .gt (.reg rSt) (.reg rMax)
private def Bgati1 : Instr := .binop rT2 .sub (.lit 1) (.reg rT1)
private def Bgati2 : Instr := .binop rT3 .mul (.reg rT1) (.reg rSt)
private def Bgati3 : Instr := .binop rT2 .mul (.reg rT2) (.reg rMax)
private def Bgati4 : Instr := .binop rMx .add (.reg rT3) (.reg rT2)
private def Bgati5 : Instr := .binop rT1 .lt (.reg rN) (.lit 64)
private def Bgati6 : Instr := .binop rT2 .sub (.lit 1) (.reg rT1)
private def Bgati7 : Instr := .binop rT3 .mul (.reg rT1) (.reg rSt)
private def Bgati8 : Instr := .binop rG .mul (.reg rT2) (.reg rMx)
private def Bgati9 : Instr := .binop rCv .add (.reg rT3) (.reg rG)
private def Bgati10 (c : Cfg) : Instr := .binop rT2 .eq (.reg rN) (.lit c.limit)
private def Bgati11 : Instr := .binop rT3 .mul (.lit 2) (.reg rBs)
private def Bgati12 : Instr := .binop rG .add (.lit 1) (.reg rN)
private def Bgati13 : Instr := .binop rG .eq (.reg rG) (.reg rT3)
private def Bgati14 : Instr := .binop rFire .bor (.reg rT1) (.reg rT2)
private def Bgati15 : Instr := .binop rFire .bor (.reg rFire) (.reg rG)

private def Bgatp0 (c : Cfg) : List Instr := []
private def Bgatp1 (c : Cfg) : List Instr := [Bgati0]
private def Bgatp2 (c : Cfg) : List Instr := [Bgati0, Bgati1]
private def Bgatp3 (c : Cfg) : List Instr := [Bgati0, Bgati1, Bgati2]
private def Bgatp4 (c : Cfg) : List Instr := [Bgati0, Bgati1, Bgati2, Bgati3]
private def Bgatp5 (c : Cfg) : List Instr := [Bgati0, Bgati1, Bgati2, Bgati3, Bgati4]
private def Bgatp6 (c : Cfg) : List Instr := [Bgati0, Bgati1, Bgati2, Bgati3, Bgati4, Bgati5]
private def Bgatp7 (c : Cfg) : List Instr := [Bgati0, Bgati1, Bgati2, Bgati3, Bgati4, Bgati5, Bgati6]
private def Bgatp8 (c : Cfg) : List Instr := [Bgati0, Bgati1, Bgati2, Bgati3, Bgati4, Bgati5, Bgati6, Bgati7]
private def Bgatp9 (c : Cfg) : List Instr := [Bgati0, Bgati1, Bgati2, Bgati3, Bgati4, Bgati5, Bgati6, Bgati7, Bgati8]
private def Bgatp10 (c : Cfg) : List Instr := [Bgati0, Bgati1, Bgati2, Bgati3, Bgati4, Bgati5, Bgati6, Bgati7, Bgati8, Bgati9]
private def Bgatp11 (c : Cfg) : List Instr := [Bgati0, Bgati1, Bgati2, Bgati3, Bgati4, Bgati5, Bgati6, Bgati7, Bgati8, Bgati9, Bgati10 c]
private def Bgatp12 (c : Cfg) : List Instr := [Bgati0, Bgati1, Bgati2, Bgati3, Bgati4, Bgati5, Bgati6, Bgati7, Bgati8, Bgati9, Bgati10 c, Bgati11]
private def Bgatp13 (c : Cfg) : List Instr := [Bgati0, Bgati1, Bgati2, Bgati3, Bgati4, Bgati5, Bgati6, Bgati7, Bgati8, Bgati9, Bgati10 c, Bgati11, Bgati12]
private def Bgatp14 (c : Cfg) : List Instr := [Bgati0, Bgati1, Bgati2, Bgati3, Bgati4, Bgati5, Bgati6, Bgati7, Bgati8, Bgati9, Bgati10 c, Bgati11, Bgati12, Bgati13]
private def Bgatp15 (c : Cfg) : List Instr := [Bgati0, Bgati1, Bgati2, Bgati3, Bgati4, Bgati5, Bgati6, Bgati7, Bgati8, Bgati9, Bgati10 c, Bgati11, Bgati12, Bgati13, Bgati14]
private def Bgatp16 (c : Cfg) : List Instr := [Bgati0, Bgati1, Bgati2, Bgati3, Bgati4, Bgati5, Bgati6, Bgati7, Bgati8, Bgati9, Bgati10 c, Bgati11, Bgati12, Bgati13, Bgati14, Bgati15]

private theorem Bgats0 (c : Cfg) : Bgatp1 c = Bgatp0 c ++ [Bgati0] := rfl
private theorem Bgats1 (c : Cfg) : Bgatp2 c = Bgatp1 c ++ [Bgati1] := rfl
private theorem Bgats2 (c : Cfg) : Bgatp3 c = Bgatp2 c ++ [Bgati2] := rfl
private theorem Bgats3 (c : Cfg) : Bgatp4 c = Bgatp3 c ++ [Bgati3] := rfl
private theorem Bgats4 (c : Cfg) : Bgatp5 c = Bgatp4 c ++ [Bgati4] := rfl
private theorem Bgats5 (c : Cfg) : Bgatp6 c = Bgatp5 c ++ [Bgati5] := rfl
private theorem Bgats6 (c : Cfg) : Bgatp7 c = Bgatp6 c ++ [Bgati6] := rfl
private theorem Bgats7 (c : Cfg) : Bgatp8 c = Bgatp7 c ++ [Bgati7] := rfl
private theorem Bgats8 (c : Cfg) : Bgatp9 c = Bgatp8 c ++ [Bgati8] := rfl
private theorem Bgats9 (c : Cfg) : Bgatp10 c = Bgatp9 c ++ [Bgati9] := rfl
private theorem Bgats10 (c : Cfg) : Bgatp11 c = Bgatp10 c ++ [Bgati10 c] := rfl
private theorem Bgats11 (c : Cfg) : Bgatp12 c = Bgatp11 c ++ [Bgati11] := rfl
private theorem Bgats12 (c : Cfg) : Bgatp13 c = Bgatp12 c ++ [Bgati12] := rfl
private theorem Bgats13 (c : Cfg) : Bgatp14 c = Bgatp13 c ++ [Bgati13] := rfl
private theorem Bgats14 (c : Cfg) : Bgatp15 c = Bgatp14 c ++ [Bgati14] := rfl
private theorem Bgats15 (c : Cfg) : Bgatp16 c = Bgatp15 c ++ [Bgati15] := rfl

private theorem Bgatfull (c : Cfg) : gateBlock c = Bgatp16 c := rfl

private theorem Bgatg0_2 (c : Cfg) : Bgatp2 c = Bgatp0 c ++ [Bgati0, Bgati1] := rfl
private theorem Bgatg0_3 (c : Cfg) : Bgatp3 c = Bgatp0 c ++ [Bgati0, Bgati1, Bgati2] := rfl
private theorem Bgatg0_5 (c : Cfg) : Bgatp5 c = Bgatp0 c ++ [Bgati0, Bgati1, Bgati2, Bgati3, Bgati4] := rfl
private theorem Bgatg0_7 (c : Cfg) : Bgatp7 c = Bgatp0 c ++ [Bgati0, Bgati1, Bgati2, Bgati3, Bgati4, Bgati5, Bgati6] := rfl
private theorem Bgatg0_10 (c : Cfg) : Bgatp10 c = Bgatp0 c ++ [Bgati0, Bgati1, Bgati2, Bgati3, Bgati4, Bgati5, Bgati6, Bgati7, Bgati8, Bgati9] := rfl
private theorem Bgatg0_11 (c : Cfg) : Bgatp11 c = Bgatp0 c ++ [Bgati0, Bgati1, Bgati2, Bgati3, Bgati4, Bgati5, Bgati6, Bgati7, Bgati8, Bgati9, Bgati10 c] := rfl
private theorem Bgatg0_12 (c : Cfg) : Bgatp12 c = Bgatp0 c ++ [Bgati0, Bgati1, Bgati2, Bgati3, Bgati4, Bgati5, Bgati6, Bgati7, Bgati8, Bgati9, Bgati10 c, Bgati11] := rfl
private theorem Bgatg1_2 (c : Cfg) : Bgatp2 c = Bgatp1 c ++ [Bgati1] := rfl
private theorem Bgatg2_3 (c : Cfg) : Bgatp3 c = Bgatp2 c ++ [Bgati2] := rfl
private theorem Bgatg3_4 (c : Cfg) : Bgatp4 c = Bgatp3 c ++ [Bgati3] := rfl
private theorem Bgatg5_8 (c : Cfg) : Bgatp8 c = Bgatp5 c ++ [Bgati5, Bgati6, Bgati7] := rfl
private theorem Bgatg5_16 (c : Cfg) : Bgatp16 c = Bgatp5 c ++ [Bgati5, Bgati6, Bgati7, Bgati8, Bgati9, Bgati10 c, Bgati11, Bgati12, Bgati13, Bgati14, Bgati15] := rfl
private theorem Bgatg6_7 (c : Cfg) : Bgatp7 c = Bgatp6 c ++ [Bgati6] := rfl
private theorem Bgatg6_14 (c : Cfg) : Bgatp14 c = Bgatp6 c ++ [Bgati6, Bgati7, Bgati8, Bgati9, Bgati10 c, Bgati11, Bgati12, Bgati13] := rfl
private theorem Bgatg6_16 (c : Cfg) : Bgatp16 c = Bgatp6 c ++ [Bgati6, Bgati7, Bgati8, Bgati9, Bgati10 c, Bgati11, Bgati12, Bgati13, Bgati14, Bgati15] := rfl
private theorem Bgatg7_8 (c : Cfg) : Bgatp8 c = Bgatp7 c ++ [Bgati7] := rfl
private theorem Bgatg8_9 (c : Cfg) : Bgatp9 c = Bgatp8 c ++ [Bgati8] := rfl
private theorem Bgatg10_16 (c : Cfg) : Bgatp16 c = Bgatp10 c ++ [Bgati10 c, Bgati11, Bgati12, Bgati13, Bgati14, Bgati15] := rfl
private theorem Bgatg11_14 (c : Cfg) : Bgatp14 c = Bgatp11 c ++ [Bgati11, Bgati12, Bgati13] := rfl
private theorem Bgatg11_16 (c : Cfg) : Bgatp16 c = Bgatp11 c ++ [Bgati11, Bgati12, Bgati13, Bgati14, Bgati15] := rfl
private theorem Bgatg12_13 (c : Cfg) : Bgatp13 c = Bgatp12 c ++ [Bgati12] := rfl
private theorem Bgatg12_16 (c : Cfg) : Bgatp16 c = Bgatp12 c ++ [Bgati12, Bgati13, Bgati14, Bgati15] := rfl
private theorem Bgatg14_15 (c : Cfg) : Bgatp15 c = Bgatp14 c ++ [Bgati14] := rfl
private theorem Bgatg14_16 (c : Cfg) : Bgatp16 c = Bgatp14 c ++ [Bgati14, Bgati15] := rfl

/-! ### `ladderBlock` -/

private def Bladi0 : Instr := .binop rT1 .mul (.lit 2) (.reg rN)
private def Bladi1 : Instr := .binop rT1 .add (.lit fpD3) (.reg rT1)
private def Bladi2 : Instr := .binop rT2 .add (.lit fpD3) (.reg rN)
private def Bladi3 : Instr := .binop rT2 .sub (.reg rT2) (.lit 1)
private def Bladi4 : Instr := .binop rT2 .udiv (.reg rT2) (.reg rN)
private def Bladi5 : Instr := .binop rT1 .sub (.reg rT1) (.reg rT2)
private def Bladi6 : Instr := .binop rT2 .mul (.lit 2) (.reg rN)
private def Bladi7 : Instr := .binop rT1 .udiv (.reg rT1) (.reg rT2)
private def Bladi8 : Instr := .binop rT2 .add (.lit fpDlit) (.reg rN)
private def Bladi9 : Instr := .binop rT2 .sub (.reg rT2) (.lit 1)
private def Bladi10 : Instr := .binop rT1 .sub (.reg rT2) (.reg rT1)
private def Bladi11 : Instr := .binop rT2 .sub (.reg rN) (.lit 1)
private def Bladi12 : Instr := .binop rIU .udiv (.reg rT1) (.reg rT2)
private def Bladi13 (c : Cfg) : Instr := .binop rT1 .ge (.reg rN) (.lit c.handoff)
private def Bladi14 : Instr := .binop rT1 .mul (.reg rT1) (.reg rC)
private def Bladi15 : Instr := .binop rT1 .mul (.reg rT1) (.reg rIU)
private def Bladi16 : Instr := .binop rLam .add (.reg rLam) (.reg rT1)
private def Bladi17 (c : Cfg) : Instr := .binop rT1 .lt (.reg rN) (.lit c.handoff)
private def Bladi18 : Instr := .binop rT2 .sub (.lit 1) (.reg rT1)
private def Bladi19 : Instr := .binop rT3 .mul (.reg rT1) (.reg rV)
private def Bladi20 : Instr := .binop rG .mul (.reg rT2) (.reg rLam)
private def Bladi21 : Instr := .binop rLU .add (.reg rT3) (.reg rG)

private def Bladp0 (c : Cfg) : List Instr := []
private def Bladp1 (c : Cfg) : List Instr := [Bladi0]
private def Bladp2 (c : Cfg) : List Instr := [Bladi0, Bladi1]
private def Bladp3 (c : Cfg) : List Instr := [Bladi0, Bladi1, Bladi2]
private def Bladp4 (c : Cfg) : List Instr := [Bladi0, Bladi1, Bladi2, Bladi3]
private def Bladp5 (c : Cfg) : List Instr := [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4]
private def Bladp6 (c : Cfg) : List Instr := [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5]
private def Bladp7 (c : Cfg) : List Instr := [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6]
private def Bladp8 (c : Cfg) : List Instr := [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6, Bladi7]
private def Bladp9 (c : Cfg) : List Instr := [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6, Bladi7, Bladi8]
private def Bladp10 (c : Cfg) : List Instr := [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6, Bladi7, Bladi8, Bladi9]
private def Bladp11 (c : Cfg) : List Instr := [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6, Bladi7, Bladi8, Bladi9, Bladi10]
private def Bladp12 (c : Cfg) : List Instr := [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6, Bladi7, Bladi8, Bladi9, Bladi10, Bladi11]
private def Bladp13 (c : Cfg) : List Instr := [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6, Bladi7, Bladi8, Bladi9, Bladi10, Bladi11, Bladi12]
private def Bladp14 (c : Cfg) : List Instr := [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6, Bladi7, Bladi8, Bladi9, Bladi10, Bladi11, Bladi12, Bladi13 c]
private def Bladp15 (c : Cfg) : List Instr := [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6, Bladi7, Bladi8, Bladi9, Bladi10, Bladi11, Bladi12, Bladi13 c, Bladi14]
private def Bladp16 (c : Cfg) : List Instr := [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6, Bladi7, Bladi8, Bladi9, Bladi10, Bladi11, Bladi12, Bladi13 c, Bladi14, Bladi15]
private def Bladp17 (c : Cfg) : List Instr := [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6, Bladi7, Bladi8, Bladi9, Bladi10, Bladi11, Bladi12, Bladi13 c, Bladi14, Bladi15, Bladi16]
private def Bladp18 (c : Cfg) : List Instr := [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6, Bladi7, Bladi8, Bladi9, Bladi10, Bladi11, Bladi12, Bladi13 c, Bladi14, Bladi15, Bladi16, Bladi17 c]
private def Bladp19 (c : Cfg) : List Instr := [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6, Bladi7, Bladi8, Bladi9, Bladi10, Bladi11, Bladi12, Bladi13 c, Bladi14, Bladi15, Bladi16, Bladi17 c, Bladi18]
private def Bladp20 (c : Cfg) : List Instr := [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6, Bladi7, Bladi8, Bladi9, Bladi10, Bladi11, Bladi12, Bladi13 c, Bladi14, Bladi15, Bladi16, Bladi17 c, Bladi18, Bladi19]
private def Bladp21 (c : Cfg) : List Instr := [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6, Bladi7, Bladi8, Bladi9, Bladi10, Bladi11, Bladi12, Bladi13 c, Bladi14, Bladi15, Bladi16, Bladi17 c, Bladi18, Bladi19, Bladi20]
private def Bladp22 (c : Cfg) : List Instr := [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6, Bladi7, Bladi8, Bladi9, Bladi10, Bladi11, Bladi12, Bladi13 c, Bladi14, Bladi15, Bladi16, Bladi17 c, Bladi18, Bladi19, Bladi20, Bladi21]

private theorem Blads0 (c : Cfg) : Bladp1 c = Bladp0 c ++ [Bladi0] := rfl
private theorem Blads1 (c : Cfg) : Bladp2 c = Bladp1 c ++ [Bladi1] := rfl
private theorem Blads2 (c : Cfg) : Bladp3 c = Bladp2 c ++ [Bladi2] := rfl
private theorem Blads3 (c : Cfg) : Bladp4 c = Bladp3 c ++ [Bladi3] := rfl
private theorem Blads4 (c : Cfg) : Bladp5 c = Bladp4 c ++ [Bladi4] := rfl
private theorem Blads5 (c : Cfg) : Bladp6 c = Bladp5 c ++ [Bladi5] := rfl
private theorem Blads6 (c : Cfg) : Bladp7 c = Bladp6 c ++ [Bladi6] := rfl
private theorem Blads7 (c : Cfg) : Bladp8 c = Bladp7 c ++ [Bladi7] := rfl
private theorem Blads8 (c : Cfg) : Bladp9 c = Bladp8 c ++ [Bladi8] := rfl
private theorem Blads9 (c : Cfg) : Bladp10 c = Bladp9 c ++ [Bladi9] := rfl
private theorem Blads10 (c : Cfg) : Bladp11 c = Bladp10 c ++ [Bladi10] := rfl
private theorem Blads11 (c : Cfg) : Bladp12 c = Bladp11 c ++ [Bladi11] := rfl
private theorem Blads12 (c : Cfg) : Bladp13 c = Bladp12 c ++ [Bladi12] := rfl
private theorem Blads13 (c : Cfg) : Bladp14 c = Bladp13 c ++ [Bladi13 c] := rfl
private theorem Blads14 (c : Cfg) : Bladp15 c = Bladp14 c ++ [Bladi14] := rfl
private theorem Blads15 (c : Cfg) : Bladp16 c = Bladp15 c ++ [Bladi15] := rfl
private theorem Blads16 (c : Cfg) : Bladp17 c = Bladp16 c ++ [Bladi16] := rfl
private theorem Blads17 (c : Cfg) : Bladp18 c = Bladp17 c ++ [Bladi17 c] := rfl
private theorem Blads18 (c : Cfg) : Bladp19 c = Bladp18 c ++ [Bladi18] := rfl
private theorem Blads19 (c : Cfg) : Bladp20 c = Bladp19 c ++ [Bladi19] := rfl
private theorem Blads20 (c : Cfg) : Bladp21 c = Bladp20 c ++ [Bladi20] := rfl
private theorem Blads21 (c : Cfg) : Bladp22 c = Bladp21 c ++ [Bladi21] := rfl

private theorem Bladfull (c : Cfg) : ladderBlock c = Bladp22 c := rfl

private theorem Bladg0_2 (c : Cfg) : Bladp2 c = Bladp0 c ++ [Bladi0, Bladi1] := rfl
private theorem Bladg0_4 (c : Cfg) : Bladp4 c = Bladp0 c ++ [Bladi0, Bladi1, Bladi2, Bladi3] := rfl
private theorem Bladg0_6 (c : Cfg) : Bladp6 c = Bladp0 c ++ [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5] := rfl
private theorem Bladg0_8 (c : Cfg) : Bladp8 c = Bladp0 c ++ [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6, Bladi7] := rfl
private theorem Bladg0_11 (c : Cfg) : Bladp11 c = Bladp0 c ++ [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6, Bladi7, Bladi8, Bladi9, Bladi10] := rfl
private theorem Bladg0_13 (c : Cfg) : Bladp13 c = Bladp0 c ++ [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6, Bladi7, Bladi8, Bladi9, Bladi10, Bladi11, Bladi12] := rfl
private theorem Bladg0_14 (c : Cfg) : Bladp14 c = Bladp0 c ++ [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6, Bladi7, Bladi8, Bladi9, Bladi10, Bladi11, Bladi12, Bladi13 c] := rfl
private theorem Bladg0_16 (c : Cfg) : Bladp16 c = Bladp0 c ++ [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6, Bladi7, Bladi8, Bladi9, Bladi10, Bladi11, Bladi12, Bladi13 c, Bladi14, Bladi15] := rfl
private theorem Bladg0_17 (c : Cfg) : Bladp17 c = Bladp0 c ++ [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6, Bladi7, Bladi8, Bladi9, Bladi10, Bladi11, Bladi12, Bladi13 c, Bladi14, Bladi15, Bladi16] := rfl
private theorem Bladg0_19 (c : Cfg) : Bladp19 c = Bladp0 c ++ [Bladi0, Bladi1, Bladi2, Bladi3, Bladi4, Bladi5, Bladi6, Bladi7, Bladi8, Bladi9, Bladi10, Bladi11, Bladi12, Bladi13 c, Bladi14, Bladi15, Bladi16, Bladi17 c, Bladi18] := rfl
private theorem Bladg2_5 (c : Cfg) : Bladp5 c = Bladp2 c ++ [Bladi2, Bladi3, Bladi4] := rfl
private theorem Bladg6_7 (c : Cfg) : Bladp7 c = Bladp6 c ++ [Bladi6] := rfl
private theorem Bladg8_10 (c : Cfg) : Bladp10 c = Bladp8 c ++ [Bladi8, Bladi9] := rfl
private theorem Bladg11_12 (c : Cfg) : Bladp12 c = Bladp11 c ++ [Bladi11] := rfl
private theorem Bladg13_15 (c : Cfg) : Bladp15 c = Bladp13 c ++ [Bladi13 c, Bladi14] := rfl
private theorem Bladg13_22 (c : Cfg) : Bladp22 c = Bladp13 c ++ [Bladi13 c, Bladi14, Bladi15, Bladi16, Bladi17 c, Bladi18, Bladi19, Bladi20, Bladi21] := rfl
private theorem Bladg17_20 (c : Cfg) : Bladp20 c = Bladp17 c ++ [Bladi17 c, Bladi18, Bladi19] := rfl
private theorem Bladg17_22 (c : Cfg) : Bladp22 c = Bladp17 c ++ [Bladi17 c, Bladi18, Bladi19, Bladi20, Bladi21] := rfl
private theorem Bladg18_19 (c : Cfg) : Bladp19 c = Bladp18 c ++ [Bladi18] := rfl
private theorem Bladg18_22 (c : Cfg) : Bladp22 c = Bladp18 c ++ [Bladi18, Bladi19, Bladi20, Bladi21] := rfl
private theorem Bladg19_20 (c : Cfg) : Bladp20 c = Bladp19 c ++ [Bladi19] := rfl
private theorem Bladg19_22 (c : Cfg) : Bladp22 c = Bladp19 c ++ [Bladi19, Bladi20, Bladi21] := rfl
private theorem Bladg20_21 (c : Cfg) : Bladp21 c = Bladp20 c ++ [Bladi20] := rfl
private theorem Bladg20_22 (c : Cfg) : Bladp22 c = Bladp20 c ++ [Bladi20, Bladi21] := rfl
private theorem Bladg21_22 (c : Cfg) : Bladp22 c = Bladp21 c ++ [Bladi21] := rfl

/-! ### `productBlock` -/

private def Bprdi0 : Instr := .binop rT1 .mul (.lit 5) (.reg rCv)
private def Bprdi1 : Instr := .binop rT2 .urem (.reg rT1) (.lit b32)
private def Bprdi2 : Instr := .binop rT3 .udiv (.reg rT1) (.lit b32)
private def Bprdi3 : Instr := .binop rG .urem (.reg rLU) (.lit b32)
private def Bprdi4 : Instr := .binop rH .udiv (.reg rLU) (.lit b32)
private def Bprdi5 : Instr := .binop rP00 .mul (.reg rT2) (.reg rG)
private def Bprdi6 : Instr := .binop rP01 .mul (.reg rT2) (.reg rH)
private def Bprdi7 : Instr := .binop rP10 .mul (.reg rT3) (.reg rG)
private def Bprdi8 : Instr := .binop rP11 .mul (.reg rT3) (.reg rH)
private def Bprdi9 : Instr := .binop rMid .add (.reg rP01) (.reg rP10)
private def Bprdi10 : Instr := .binop rCM .lt (.reg rMid) (.reg rP01)
private def Bprdi11 : Instr := .binop rT2 .mul (.lit b32) (.reg rMid)
private def Bprdi12 : Instr := .binop rLo .add (.reg rP00) (.reg rT2)
private def Bprdi13 : Instr := .binop rCL .lt (.reg rLo) (.reg rP00)
private def Bprdi14 : Instr := .binop rHi .udiv (.reg rMid) (.lit b32)
private def Bprdi15 : Instr := .binop rHi .add (.reg rHi) (.reg rP11)
private def Bprdi16 : Instr := .binop rT2 .mul (.lit b32) (.reg rCM)
private def Bprdi17 : Instr := .binop rHi .add (.reg rHi) (.reg rT2)
private def Bprdi18 : Instr := .binop rHi .add (.reg rHi) (.reg rCL)
private def Bprdi19 : Instr := .binop rT1 .lt (.reg rHi) (.lit rhsHi)
private def Bprdi20 : Instr := .binop rT2 .eq (.reg rHi) (.lit rhsHi)
private def Bprdi21 : Instr := .binop rT3 .eq (.reg rLo) (.lit 0)
private def Bprdi22 : Instr := .binop rT2 .mul (.reg rT2) (.reg rT3)
private def Bprdi23 : Instr := .binop rOk .bor (.reg rT1) (.reg rT2)

private def Bprdp0 : List Instr := []
private def Bprdp1 : List Instr := [Bprdi0]
private def Bprdp2 : List Instr := [Bprdi0, Bprdi1]
private def Bprdp3 : List Instr := [Bprdi0, Bprdi1, Bprdi2]
private def Bprdp4 : List Instr := [Bprdi0, Bprdi1, Bprdi2, Bprdi3]
private def Bprdp5 : List Instr := [Bprdi0, Bprdi1, Bprdi2, Bprdi3, Bprdi4]
private def Bprdp6 : List Instr := [Bprdi0, Bprdi1, Bprdi2, Bprdi3, Bprdi4, Bprdi5]
private def Bprdp7 : List Instr := [Bprdi0, Bprdi1, Bprdi2, Bprdi3, Bprdi4, Bprdi5, Bprdi6]
private def Bprdp8 : List Instr := [Bprdi0, Bprdi1, Bprdi2, Bprdi3, Bprdi4, Bprdi5, Bprdi6, Bprdi7]
private def Bprdp9 : List Instr := [Bprdi0, Bprdi1, Bprdi2, Bprdi3, Bprdi4, Bprdi5, Bprdi6, Bprdi7, Bprdi8]
private def Bprdp10 : List Instr := [Bprdi0, Bprdi1, Bprdi2, Bprdi3, Bprdi4, Bprdi5, Bprdi6, Bprdi7, Bprdi8, Bprdi9]
private def Bprdp11 : List Instr := [Bprdi0, Bprdi1, Bprdi2, Bprdi3, Bprdi4, Bprdi5, Bprdi6, Bprdi7, Bprdi8, Bprdi9, Bprdi10]
private def Bprdp12 : List Instr := [Bprdi0, Bprdi1, Bprdi2, Bprdi3, Bprdi4, Bprdi5, Bprdi6, Bprdi7, Bprdi8, Bprdi9, Bprdi10, Bprdi11]
private def Bprdp13 : List Instr := [Bprdi0, Bprdi1, Bprdi2, Bprdi3, Bprdi4, Bprdi5, Bprdi6, Bprdi7, Bprdi8, Bprdi9, Bprdi10, Bprdi11, Bprdi12]
private def Bprdp14 : List Instr := [Bprdi0, Bprdi1, Bprdi2, Bprdi3, Bprdi4, Bprdi5, Bprdi6, Bprdi7, Bprdi8, Bprdi9, Bprdi10, Bprdi11, Bprdi12, Bprdi13]
private def Bprdp15 : List Instr := [Bprdi0, Bprdi1, Bprdi2, Bprdi3, Bprdi4, Bprdi5, Bprdi6, Bprdi7, Bprdi8, Bprdi9, Bprdi10, Bprdi11, Bprdi12, Bprdi13, Bprdi14]
private def Bprdp16 : List Instr := [Bprdi0, Bprdi1, Bprdi2, Bprdi3, Bprdi4, Bprdi5, Bprdi6, Bprdi7, Bprdi8, Bprdi9, Bprdi10, Bprdi11, Bprdi12, Bprdi13, Bprdi14, Bprdi15]
private def Bprdp17 : List Instr := [Bprdi0, Bprdi1, Bprdi2, Bprdi3, Bprdi4, Bprdi5, Bprdi6, Bprdi7, Bprdi8, Bprdi9, Bprdi10, Bprdi11, Bprdi12, Bprdi13, Bprdi14, Bprdi15, Bprdi16]
private def Bprdp18 : List Instr := [Bprdi0, Bprdi1, Bprdi2, Bprdi3, Bprdi4, Bprdi5, Bprdi6, Bprdi7, Bprdi8, Bprdi9, Bprdi10, Bprdi11, Bprdi12, Bprdi13, Bprdi14, Bprdi15, Bprdi16, Bprdi17]
private def Bprdp19 : List Instr := [Bprdi0, Bprdi1, Bprdi2, Bprdi3, Bprdi4, Bprdi5, Bprdi6, Bprdi7, Bprdi8, Bprdi9, Bprdi10, Bprdi11, Bprdi12, Bprdi13, Bprdi14, Bprdi15, Bprdi16, Bprdi17, Bprdi18]
private def Bprdp20 : List Instr := [Bprdi0, Bprdi1, Bprdi2, Bprdi3, Bprdi4, Bprdi5, Bprdi6, Bprdi7, Bprdi8, Bprdi9, Bprdi10, Bprdi11, Bprdi12, Bprdi13, Bprdi14, Bprdi15, Bprdi16, Bprdi17, Bprdi18, Bprdi19]
private def Bprdp21 : List Instr := [Bprdi0, Bprdi1, Bprdi2, Bprdi3, Bprdi4, Bprdi5, Bprdi6, Bprdi7, Bprdi8, Bprdi9, Bprdi10, Bprdi11, Bprdi12, Bprdi13, Bprdi14, Bprdi15, Bprdi16, Bprdi17, Bprdi18, Bprdi19, Bprdi20]
private def Bprdp22 : List Instr := [Bprdi0, Bprdi1, Bprdi2, Bprdi3, Bprdi4, Bprdi5, Bprdi6, Bprdi7, Bprdi8, Bprdi9, Bprdi10, Bprdi11, Bprdi12, Bprdi13, Bprdi14, Bprdi15, Bprdi16, Bprdi17, Bprdi18, Bprdi19, Bprdi20, Bprdi21]
private def Bprdp23 : List Instr := [Bprdi0, Bprdi1, Bprdi2, Bprdi3, Bprdi4, Bprdi5, Bprdi6, Bprdi7, Bprdi8, Bprdi9, Bprdi10, Bprdi11, Bprdi12, Bprdi13, Bprdi14, Bprdi15, Bprdi16, Bprdi17, Bprdi18, Bprdi19, Bprdi20, Bprdi21, Bprdi22]
private def Bprdp24 : List Instr := [Bprdi0, Bprdi1, Bprdi2, Bprdi3, Bprdi4, Bprdi5, Bprdi6, Bprdi7, Bprdi8, Bprdi9, Bprdi10, Bprdi11, Bprdi12, Bprdi13, Bprdi14, Bprdi15, Bprdi16, Bprdi17, Bprdi18, Bprdi19, Bprdi20, Bprdi21, Bprdi22, Bprdi23]

private theorem Bprds0 : Bprdp1 = Bprdp0 ++ [Bprdi0] := rfl
private theorem Bprds1 : Bprdp2 = Bprdp1 ++ [Bprdi1] := rfl
private theorem Bprds2 : Bprdp3 = Bprdp2 ++ [Bprdi2] := rfl
private theorem Bprds3 : Bprdp4 = Bprdp3 ++ [Bprdi3] := rfl
private theorem Bprds4 : Bprdp5 = Bprdp4 ++ [Bprdi4] := rfl
private theorem Bprds5 : Bprdp6 = Bprdp5 ++ [Bprdi5] := rfl
private theorem Bprds6 : Bprdp7 = Bprdp6 ++ [Bprdi6] := rfl
private theorem Bprds7 : Bprdp8 = Bprdp7 ++ [Bprdi7] := rfl
private theorem Bprds8 : Bprdp9 = Bprdp8 ++ [Bprdi8] := rfl
private theorem Bprds9 : Bprdp10 = Bprdp9 ++ [Bprdi9] := rfl
private theorem Bprds10 : Bprdp11 = Bprdp10 ++ [Bprdi10] := rfl
private theorem Bprds11 : Bprdp12 = Bprdp11 ++ [Bprdi11] := rfl
private theorem Bprds12 : Bprdp13 = Bprdp12 ++ [Bprdi12] := rfl
private theorem Bprds13 : Bprdp14 = Bprdp13 ++ [Bprdi13] := rfl
private theorem Bprds14 : Bprdp15 = Bprdp14 ++ [Bprdi14] := rfl
private theorem Bprds15 : Bprdp16 = Bprdp15 ++ [Bprdi15] := rfl
private theorem Bprds16 : Bprdp17 = Bprdp16 ++ [Bprdi16] := rfl
private theorem Bprds17 : Bprdp18 = Bprdp17 ++ [Bprdi17] := rfl
private theorem Bprds18 : Bprdp19 = Bprdp18 ++ [Bprdi18] := rfl
private theorem Bprds19 : Bprdp20 = Bprdp19 ++ [Bprdi19] := rfl
private theorem Bprds20 : Bprdp21 = Bprdp20 ++ [Bprdi20] := rfl
private theorem Bprds21 : Bprdp22 = Bprdp21 ++ [Bprdi21] := rfl
private theorem Bprds22 : Bprdp23 = Bprdp22 ++ [Bprdi22] := rfl
private theorem Bprds23 : Bprdp24 = Bprdp23 ++ [Bprdi23] := rfl

private theorem Bprdfull : productBlock = Bprdp24 := rfl

private theorem Bprdg0_3 : Bprdp3 = Bprdp0 ++ [Bprdi0, Bprdi1, Bprdi2] := rfl
private theorem Bprdg0_4 : Bprdp4 = Bprdp0 ++ [Bprdi0, Bprdi1, Bprdi2, Bprdi3] := rfl
private theorem Bprdg1_2 : Bprdp2 = Bprdp1 ++ [Bprdi1] := rfl
private theorem Bprdg2_5 : Bprdp5 = Bprdp2 ++ [Bprdi2, Bprdi3, Bprdi4] := rfl
private theorem Bprdg2_6 : Bprdp6 = Bprdp2 ++ [Bprdi2, Bprdi3, Bprdi4, Bprdi5] := rfl
private theorem Bprdg3_7 : Bprdp7 = Bprdp3 ++ [Bprdi3, Bprdi4, Bprdi5, Bprdi6] := rfl
private theorem Bprdg3_8 : Bprdp8 = Bprdp3 ++ [Bprdi3, Bprdi4, Bprdi5, Bprdi6, Bprdi7] := rfl
private theorem Bprdg4_5 : Bprdp5 = Bprdp4 ++ [Bprdi4] := rfl
private theorem Bprdg4_7 : Bprdp7 = Bprdp4 ++ [Bprdi4, Bprdi5, Bprdi6] := rfl
private theorem Bprdg4_24 : Bprdp24 = Bprdp4 ++ [Bprdi4, Bprdi5, Bprdi6, Bprdi7, Bprdi8, Bprdi9, Bprdi10, Bprdi11, Bprdi12, Bprdi13, Bprdi14, Bprdi15, Bprdi16, Bprdi17, Bprdi18, Bprdi19, Bprdi20, Bprdi21, Bprdi22, Bprdi23] := rfl
private theorem Bprdg5_6 : Bprdp6 = Bprdp5 ++ [Bprdi5] := rfl
private theorem Bprdg5_8 : Bprdp8 = Bprdp5 ++ [Bprdi5, Bprdi6, Bprdi7] := rfl
private theorem Bprdg5_24 : Bprdp24 = Bprdp5 ++ [Bprdi5, Bprdi6, Bprdi7, Bprdi8, Bprdi9, Bprdi10, Bprdi11, Bprdi12, Bprdi13, Bprdi14, Bprdi15, Bprdi16, Bprdi17, Bprdi18, Bprdi19, Bprdi20, Bprdi21, Bprdi22, Bprdi23] := rfl
private theorem Bprdg6_12 : Bprdp12 = Bprdp6 ++ [Bprdi6, Bprdi7, Bprdi8, Bprdi9, Bprdi10, Bprdi11] := rfl
private theorem Bprdg6_13 : Bprdp13 = Bprdp6 ++ [Bprdi6, Bprdi7, Bprdi8, Bprdi9, Bprdi10, Bprdi11, Bprdi12] := rfl
private theorem Bprdg6_24 : Bprdp24 = Bprdp6 ++ [Bprdi6, Bprdi7, Bprdi8, Bprdi9, Bprdi10, Bprdi11, Bprdi12, Bprdi13, Bprdi14, Bprdi15, Bprdi16, Bprdi17, Bprdi18, Bprdi19, Bprdi20, Bprdi21, Bprdi22, Bprdi23] := rfl
private theorem Bprdg7_9 : Bprdp9 = Bprdp7 ++ [Bprdi7, Bprdi8] := rfl
private theorem Bprdg7_10 : Bprdp10 = Bprdp7 ++ [Bprdi7, Bprdi8, Bprdi9] := rfl
private theorem Bprdg7_24 : Bprdp24 = Bprdp7 ++ [Bprdi7, Bprdi8, Bprdi9, Bprdi10, Bprdi11, Bprdi12, Bprdi13, Bprdi14, Bprdi15, Bprdi16, Bprdi17, Bprdi18, Bprdi19, Bprdi20, Bprdi21, Bprdi22, Bprdi23] := rfl
private theorem Bprdg8_9 : Bprdp9 = Bprdp8 ++ [Bprdi8] := rfl
private theorem Bprdg8_24 : Bprdp24 = Bprdp8 ++ [Bprdi8, Bprdi9, Bprdi10, Bprdi11, Bprdi12, Bprdi13, Bprdi14, Bprdi15, Bprdi16, Bprdi17, Bprdi18, Bprdi19, Bprdi20, Bprdi21, Bprdi22, Bprdi23] := rfl
private theorem Bprdg9_15 : Bprdp15 = Bprdp9 ++ [Bprdi9, Bprdi10, Bprdi11, Bprdi12, Bprdi13, Bprdi14] := rfl
private theorem Bprdg9_24 : Bprdp24 = Bprdp9 ++ [Bprdi9, Bprdi10, Bprdi11, Bprdi12, Bprdi13, Bprdi14, Bprdi15, Bprdi16, Bprdi17, Bprdi18, Bprdi19, Bprdi20, Bprdi21, Bprdi22, Bprdi23] := rfl
private theorem Bprdg10_11 : Bprdp11 = Bprdp10 ++ [Bprdi10] := rfl
private theorem Bprdg10_14 : Bprdp14 = Bprdp10 ++ [Bprdi10, Bprdi11, Bprdi12, Bprdi13] := rfl
private theorem Bprdg10_24 : Bprdp24 = Bprdp10 ++ [Bprdi10, Bprdi11, Bprdi12, Bprdi13, Bprdi14, Bprdi15, Bprdi16, Bprdi17, Bprdi18, Bprdi19, Bprdi20, Bprdi21, Bprdi22, Bprdi23] := rfl
private theorem Bprdg11_16 : Bprdp16 = Bprdp11 ++ [Bprdi11, Bprdi12, Bprdi13, Bprdi14, Bprdi15] := rfl
private theorem Bprdg11_24 : Bprdp24 = Bprdp11 ++ [Bprdi11, Bprdi12, Bprdi13, Bprdi14, Bprdi15, Bprdi16, Bprdi17, Bprdi18, Bprdi19, Bprdi20, Bprdi21, Bprdi22, Bprdi23] := rfl
private theorem Bprdg13_21 : Bprdp21 = Bprdp13 ++ [Bprdi13, Bprdi14, Bprdi15, Bprdi16, Bprdi17, Bprdi18, Bprdi19, Bprdi20] := rfl
private theorem Bprdg13_24 : Bprdp24 = Bprdp13 ++ [Bprdi13, Bprdi14, Bprdi15, Bprdi16, Bprdi17, Bprdi18, Bprdi19, Bprdi20, Bprdi21, Bprdi22, Bprdi23] := rfl
private theorem Bprdg14_18 : Bprdp18 = Bprdp14 ++ [Bprdi14, Bprdi15, Bprdi16, Bprdi17] := rfl
private theorem Bprdg14_24 : Bprdp24 = Bprdp14 ++ [Bprdi14, Bprdi15, Bprdi16, Bprdi17, Bprdi18, Bprdi19, Bprdi20, Bprdi21, Bprdi22, Bprdi23] := rfl
private theorem Bprdg16_17 : Bprdp17 = Bprdp16 ++ [Bprdi16] := rfl
private theorem Bprdg19_20 : Bprdp20 = Bprdp19 ++ [Bprdi19] := rfl
private theorem Bprdg19_24 : Bprdp24 = Bprdp19 ++ [Bprdi19, Bprdi20, Bprdi21, Bprdi22, Bprdi23] := rfl
private theorem Bprdg20_23 : Bprdp23 = Bprdp20 ++ [Bprdi20, Bprdi21, Bprdi22] := rfl
private theorem Bprdg20_24 : Bprdp24 = Bprdp20 ++ [Bprdi20, Bprdi21, Bprdi22, Bprdi23] := rfl
private theorem Bprdg21_22 : Bprdp22 = Bprdp21 ++ [Bprdi21] := rfl
private theorem Bprdg22_24 : Bprdp24 = Bprdp22 ++ [Bprdi22, Bprdi23] := rfl
private theorem Bprdg23_24 : Bprdp24 = Bprdp23 ++ [Bprdi23] := rfl

/-! ### `badBlock` -/

private def Bbadi0 : Instr := .binop rT1 .sub (.lit 1) (.reg rOk)
private def Bbadi1 : Instr := .binop rT1 .mul (.reg rT1) (.reg rFire)
private def Bbadi2 : Instr := .binop rT1 .mul (.reg rT1) (.reg rC)
private def Bbadi3 : Instr := .binop rBad .add (.reg rBad) (.reg rT1)
private def Bbadi4 (c : Cfg) : Instr := .binop rT2 .gt (.reg rAcc) (.lit c.capS)
private def Bbadi5 (c : Cfg) : Instr := .binop rT3 .gt (.reg rAbs) (.lit c.capL)
private def Bbadi6 : Instr := .binop rT2 .bor (.reg rT2) (.reg rT3)
private def Bbadi7 : Instr := .binop rT2 .mul (.reg rT2) (.reg rW)
private def Bbadi8 : Instr := .binop rBad .add (.reg rBad) (.reg rT2)
private def Bbadi9 (c : Cfg) : Instr := .binop rT2 .gt (.reg rSt) (.lit c.capS)
private def Bbadi10 (c : Cfg) : Instr := .binop rT3 .gt (.reg rAbsN) (.lit c.capL)
private def Bbadi11 : Instr := .binop rT2 .bor (.reg rT2) (.reg rT3)
private def Bbadi12 (c : Cfg) : Instr := .binop rT3 .gt (.reg rLam) (.lit c.capLog)
private def Bbadi13 : Instr := .binop rT2 .bor (.reg rT2) (.reg rT3)
private def Bbadi14 : Instr := .binop rT2 .mul (.reg rT2) (.reg rC)
private def Bbadi15 : Instr := .binop rBad .add (.reg rBad) (.reg rT2)

private def Bbadp0 (c : Cfg) : List Instr := []
private def Bbadp1 (c : Cfg) : List Instr := [Bbadi0]
private def Bbadp2 (c : Cfg) : List Instr := [Bbadi0, Bbadi1]
private def Bbadp3 (c : Cfg) : List Instr := [Bbadi0, Bbadi1, Bbadi2]
private def Bbadp4 (c : Cfg) : List Instr := [Bbadi0, Bbadi1, Bbadi2, Bbadi3]
private def Bbadp5 (c : Cfg) : List Instr := [Bbadi0, Bbadi1, Bbadi2, Bbadi3, Bbadi4 c]
private def Bbadp6 (c : Cfg) : List Instr := [Bbadi0, Bbadi1, Bbadi2, Bbadi3, Bbadi4 c, Bbadi5 c]
private def Bbadp7 (c : Cfg) : List Instr := [Bbadi0, Bbadi1, Bbadi2, Bbadi3, Bbadi4 c, Bbadi5 c, Bbadi6]
private def Bbadp8 (c : Cfg) : List Instr := [Bbadi0, Bbadi1, Bbadi2, Bbadi3, Bbadi4 c, Bbadi5 c, Bbadi6, Bbadi7]
private def Bbadp9 (c : Cfg) : List Instr := [Bbadi0, Bbadi1, Bbadi2, Bbadi3, Bbadi4 c, Bbadi5 c, Bbadi6, Bbadi7, Bbadi8]
private def Bbadp10 (c : Cfg) : List Instr := [Bbadi0, Bbadi1, Bbadi2, Bbadi3, Bbadi4 c, Bbadi5 c, Bbadi6, Bbadi7, Bbadi8, Bbadi9 c]
private def Bbadp11 (c : Cfg) : List Instr := [Bbadi0, Bbadi1, Bbadi2, Bbadi3, Bbadi4 c, Bbadi5 c, Bbadi6, Bbadi7, Bbadi8, Bbadi9 c, Bbadi10 c]
private def Bbadp12 (c : Cfg) : List Instr := [Bbadi0, Bbadi1, Bbadi2, Bbadi3, Bbadi4 c, Bbadi5 c, Bbadi6, Bbadi7, Bbadi8, Bbadi9 c, Bbadi10 c, Bbadi11]
private def Bbadp13 (c : Cfg) : List Instr := [Bbadi0, Bbadi1, Bbadi2, Bbadi3, Bbadi4 c, Bbadi5 c, Bbadi6, Bbadi7, Bbadi8, Bbadi9 c, Bbadi10 c, Bbadi11, Bbadi12 c]
private def Bbadp14 (c : Cfg) : List Instr := [Bbadi0, Bbadi1, Bbadi2, Bbadi3, Bbadi4 c, Bbadi5 c, Bbadi6, Bbadi7, Bbadi8, Bbadi9 c, Bbadi10 c, Bbadi11, Bbadi12 c, Bbadi13]
private def Bbadp15 (c : Cfg) : List Instr := [Bbadi0, Bbadi1, Bbadi2, Bbadi3, Bbadi4 c, Bbadi5 c, Bbadi6, Bbadi7, Bbadi8, Bbadi9 c, Bbadi10 c, Bbadi11, Bbadi12 c, Bbadi13, Bbadi14]
private def Bbadp16 (c : Cfg) : List Instr := [Bbadi0, Bbadi1, Bbadi2, Bbadi3, Bbadi4 c, Bbadi5 c, Bbadi6, Bbadi7, Bbadi8, Bbadi9 c, Bbadi10 c, Bbadi11, Bbadi12 c, Bbadi13, Bbadi14, Bbadi15]

private theorem Bbads0 (c : Cfg) : Bbadp1 c = Bbadp0 c ++ [Bbadi0] := rfl
private theorem Bbads1 (c : Cfg) : Bbadp2 c = Bbadp1 c ++ [Bbadi1] := rfl
private theorem Bbads2 (c : Cfg) : Bbadp3 c = Bbadp2 c ++ [Bbadi2] := rfl
private theorem Bbads3 (c : Cfg) : Bbadp4 c = Bbadp3 c ++ [Bbadi3] := rfl
private theorem Bbads4 (c : Cfg) : Bbadp5 c = Bbadp4 c ++ [Bbadi4 c] := rfl
private theorem Bbads5 (c : Cfg) : Bbadp6 c = Bbadp5 c ++ [Bbadi5 c] := rfl
private theorem Bbads6 (c : Cfg) : Bbadp7 c = Bbadp6 c ++ [Bbadi6] := rfl
private theorem Bbads7 (c : Cfg) : Bbadp8 c = Bbadp7 c ++ [Bbadi7] := rfl
private theorem Bbads8 (c : Cfg) : Bbadp9 c = Bbadp8 c ++ [Bbadi8] := rfl
private theorem Bbads9 (c : Cfg) : Bbadp10 c = Bbadp9 c ++ [Bbadi9 c] := rfl
private theorem Bbads10 (c : Cfg) : Bbadp11 c = Bbadp10 c ++ [Bbadi10 c] := rfl
private theorem Bbads11 (c : Cfg) : Bbadp12 c = Bbadp11 c ++ [Bbadi11] := rfl
private theorem Bbads12 (c : Cfg) : Bbadp13 c = Bbadp12 c ++ [Bbadi12 c] := rfl
private theorem Bbads13 (c : Cfg) : Bbadp14 c = Bbadp13 c ++ [Bbadi13] := rfl
private theorem Bbads14 (c : Cfg) : Bbadp15 c = Bbadp14 c ++ [Bbadi14] := rfl
private theorem Bbads15 (c : Cfg) : Bbadp16 c = Bbadp15 c ++ [Bbadi15] := rfl

private theorem Bbadfull (c : Cfg) : badBlock c = Bbadp16 c := rfl

private theorem Bbadg0_1 (c : Cfg) : Bbadp1 c = Bbadp0 c ++ [Bbadi0] := rfl
private theorem Bbadg0_2 (c : Cfg) : Bbadp2 c = Bbadp0 c ++ [Bbadi0, Bbadi1] := rfl
private theorem Bbadg0_3 (c : Cfg) : Bbadp3 c = Bbadp0 c ++ [Bbadi0, Bbadi1, Bbadi2] := rfl
private theorem Bbadg0_4 (c : Cfg) : Bbadp4 c = Bbadp0 c ++ [Bbadi0, Bbadi1, Bbadi2, Bbadi3] := rfl
private theorem Bbadg0_5 (c : Cfg) : Bbadp5 c = Bbadp0 c ++ [Bbadi0, Bbadi1, Bbadi2, Bbadi3, Bbadi4 c] := rfl
private theorem Bbadg0_7 (c : Cfg) : Bbadp7 c = Bbadp0 c ++ [Bbadi0, Bbadi1, Bbadi2, Bbadi3, Bbadi4 c, Bbadi5 c, Bbadi6] := rfl
private theorem Bbadg0_9 (c : Cfg) : Bbadp9 c = Bbadp0 c ++ [Bbadi0, Bbadi1, Bbadi2, Bbadi3, Bbadi4 c, Bbadi5 c, Bbadi6, Bbadi7, Bbadi8] := rfl
private theorem Bbadg0_10 (c : Cfg) : Bbadp10 c = Bbadp0 c ++ [Bbadi0, Bbadi1, Bbadi2, Bbadi3, Bbadi4 c, Bbadi5 c, Bbadi6, Bbadi7, Bbadi8, Bbadi9 c] := rfl
private theorem Bbadg0_12 (c : Cfg) : Bbadp12 c = Bbadp0 c ++ [Bbadi0, Bbadi1, Bbadi2, Bbadi3, Bbadi4 c, Bbadi5 c, Bbadi6, Bbadi7, Bbadi8, Bbadi9 c, Bbadi10 c, Bbadi11] := rfl
private theorem Bbadg0_14 (c : Cfg) : Bbadp14 c = Bbadp0 c ++ [Bbadi0, Bbadi1, Bbadi2, Bbadi3, Bbadi4 c, Bbadi5 c, Bbadi6, Bbadi7, Bbadi8, Bbadi9 c, Bbadi10 c, Bbadi11, Bbadi12 c, Bbadi13] := rfl
private theorem Bbadg3_16 (c : Cfg) : Bbadp16 c = Bbadp3 c ++ [Bbadi3, Bbadi4 c, Bbadi5 c, Bbadi6, Bbadi7, Bbadi8, Bbadi9 c, Bbadi10 c, Bbadi11, Bbadi12 c, Bbadi13, Bbadi14, Bbadi15] := rfl
private theorem Bbadg4_8 (c : Cfg) : Bbadp8 c = Bbadp4 c ++ [Bbadi4 c, Bbadi5 c, Bbadi6, Bbadi7] := rfl
private theorem Bbadg5_6 (c : Cfg) : Bbadp6 c = Bbadp5 c ++ [Bbadi5 c] := rfl
private theorem Bbadg9_15 (c : Cfg) : Bbadp15 c = Bbadp9 c ++ [Bbadi9 c, Bbadi10 c, Bbadi11, Bbadi12 c, Bbadi13, Bbadi14] := rfl
private theorem Bbadg10_11 (c : Cfg) : Bbadp11 c = Bbadp10 c ++ [Bbadi10 c] := rfl
private theorem Bbadg12_13 (c : Cfg) : Bbadp13 c = Bbadp12 c ++ [Bbadi12 c] := rfl
private theorem Bbadg13_16 (c : Cfg) : Bbadp16 c = Bbadp13 c ++ [Bbadi13, Bbadi14, Bbadi15] := rfl
private theorem Bbadg15_16 (c : Cfg) : Bbadp16 c = Bbadp15 c ++ [Bbadi15] := rfl

/-! ### `updateBlock` -/

private def Bupdi0 : Instr := .binop rT1 .mul (.lit pack) (.reg rMun)
private def Bupdi1 : Instr := .binop rT1 .add (.reg rT1) (.reg rAbsN)
private def Bupdi2 : Instr := .binop rT1 .mul (.reg rT1) (.reg rC)
private def Bupdi3 : Instr := .binop rT2 .sub (.lit 1) (.reg rC)
private def Bupdi4 : Instr := .binop rT2 .mul (.reg rT2) (.reg rCell)
private def Bupdi5 : Instr := .binop rCell .add (.reg rT1) (.reg rT2)
private def Bupdi6 : Instr := .binop rT1 .sub (.lit 1) (.reg rFire)
private def Bupdi7 : Instr := .binop rT1 .mul (.reg rT1) (.reg rMx)
private def Bupdi8 : Instr := .binop rT1 .mul (.reg rT1) (.reg rC)
private def Bupdi9 : Instr := .binop rT2 .sub (.lit 1) (.reg rC)
private def Bupdi10 : Instr := .binop rT2 .mul (.reg rT2) (.reg rMax)
private def Bupdi11 : Instr := .binop rMax .add (.reg rT1) (.reg rT2)
private def Bupdi12 : Instr := .binop rT1 .lt (.reg rN) (.lit 64)
private def Bupdi13 : Instr := .binop rT2 .mul (.lit 64) (.reg rT1)
private def Bupdi14 : Instr := .binop rT3 .sub (.lit 1) (.reg rT1)
private def Bupdi15 : Instr := .binop rG .add (.lit 1) (.reg rN)
private def Bupdi16 : Instr := .binop rG .mul (.reg rG) (.reg rFire)
private def Bupdi17 : Instr := .binop rH .sub (.lit 1) (.reg rFire)
private def Bupdi18 : Instr := .binop rH .mul (.reg rH) (.reg rBs)
private def Bupdi19 : Instr := .binop rG .add (.reg rG) (.reg rH)
private def Bupdi20 : Instr := .binop rG .mul (.reg rG) (.reg rT3)
private def Bupdi21 : Instr := .binop rT2 .add (.reg rT2) (.reg rG)
private def Bupdi22 : Instr := .binop rT2 .mul (.reg rT2) (.reg rC)
private def Bupdi23 : Instr := .binop rT3 .sub (.lit 1) (.reg rC)
private def Bupdi24 : Instr := .binop rT3 .mul (.reg rT3) (.reg rBs)
private def Bupdi25 : Instr := .binop rBs .add (.reg rT2) (.reg rT3)
private def Bupdi26 : Instr := .binop rT1 .mul (.reg rC) (.reg rFire)
private def Bupdi27 : Instr := .binop rIdx .add (.reg rIdx) (.reg rT1)
private def Bupdi28 (c : Cfg) : Instr := .binop rIdx .urem (.reg rIdx) (.lit c.tab)

private def Bupdp0 (c : Cfg) : List Instr := []
private def Bupdp1 (c : Cfg) : List Instr := [Bupdi0]
private def Bupdp2 (c : Cfg) : List Instr := [Bupdi0, Bupdi1]
private def Bupdp3 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2]
private def Bupdp4 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3]
private def Bupdp5 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4]
private def Bupdp6 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5]
private def Bupdp7 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6]
private def Bupdp8 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7]
private def Bupdp9 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8]
private def Bupdp10 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9]
private def Bupdp11 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10]
private def Bupdp12 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11]
private def Bupdp13 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12]
private def Bupdp14 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13]
private def Bupdp15 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14]
private def Bupdp16 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15]
private def Bupdp17 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15, Bupdi16]
private def Bupdp18 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15, Bupdi16, Bupdi17]
private def Bupdp19 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15, Bupdi16, Bupdi17, Bupdi18]
private def Bupdp20 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15, Bupdi16, Bupdi17, Bupdi18, Bupdi19]
private def Bupdp21 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15, Bupdi16, Bupdi17, Bupdi18, Bupdi19, Bupdi20]
private def Bupdp22 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15, Bupdi16, Bupdi17, Bupdi18, Bupdi19, Bupdi20, Bupdi21]
private def Bupdp23 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15, Bupdi16, Bupdi17, Bupdi18, Bupdi19, Bupdi20, Bupdi21, Bupdi22]
private def Bupdp24 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15, Bupdi16, Bupdi17, Bupdi18, Bupdi19, Bupdi20, Bupdi21, Bupdi22, Bupdi23]
private def Bupdp25 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15, Bupdi16, Bupdi17, Bupdi18, Bupdi19, Bupdi20, Bupdi21, Bupdi22, Bupdi23, Bupdi24]
private def Bupdp26 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15, Bupdi16, Bupdi17, Bupdi18, Bupdi19, Bupdi20, Bupdi21, Bupdi22, Bupdi23, Bupdi24, Bupdi25]
private def Bupdp27 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15, Bupdi16, Bupdi17, Bupdi18, Bupdi19, Bupdi20, Bupdi21, Bupdi22, Bupdi23, Bupdi24, Bupdi25, Bupdi26]
private def Bupdp28 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15, Bupdi16, Bupdi17, Bupdi18, Bupdi19, Bupdi20, Bupdi21, Bupdi22, Bupdi23, Bupdi24, Bupdi25, Bupdi26, Bupdi27]
private def Bupdp29 (c : Cfg) : List Instr := [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15, Bupdi16, Bupdi17, Bupdi18, Bupdi19, Bupdi20, Bupdi21, Bupdi22, Bupdi23, Bupdi24, Bupdi25, Bupdi26, Bupdi27, Bupdi28 c]

private theorem Bupds0 (c : Cfg) : Bupdp1 c = Bupdp0 c ++ [Bupdi0] := rfl
private theorem Bupds1 (c : Cfg) : Bupdp2 c = Bupdp1 c ++ [Bupdi1] := rfl
private theorem Bupds2 (c : Cfg) : Bupdp3 c = Bupdp2 c ++ [Bupdi2] := rfl
private theorem Bupds3 (c : Cfg) : Bupdp4 c = Bupdp3 c ++ [Bupdi3] := rfl
private theorem Bupds4 (c : Cfg) : Bupdp5 c = Bupdp4 c ++ [Bupdi4] := rfl
private theorem Bupds5 (c : Cfg) : Bupdp6 c = Bupdp5 c ++ [Bupdi5] := rfl
private theorem Bupds6 (c : Cfg) : Bupdp7 c = Bupdp6 c ++ [Bupdi6] := rfl
private theorem Bupds7 (c : Cfg) : Bupdp8 c = Bupdp7 c ++ [Bupdi7] := rfl
private theorem Bupds8 (c : Cfg) : Bupdp9 c = Bupdp8 c ++ [Bupdi8] := rfl
private theorem Bupds9 (c : Cfg) : Bupdp10 c = Bupdp9 c ++ [Bupdi9] := rfl
private theorem Bupds10 (c : Cfg) : Bupdp11 c = Bupdp10 c ++ [Bupdi10] := rfl
private theorem Bupds11 (c : Cfg) : Bupdp12 c = Bupdp11 c ++ [Bupdi11] := rfl
private theorem Bupds12 (c : Cfg) : Bupdp13 c = Bupdp12 c ++ [Bupdi12] := rfl
private theorem Bupds13 (c : Cfg) : Bupdp14 c = Bupdp13 c ++ [Bupdi13] := rfl
private theorem Bupds14 (c : Cfg) : Bupdp15 c = Bupdp14 c ++ [Bupdi14] := rfl
private theorem Bupds15 (c : Cfg) : Bupdp16 c = Bupdp15 c ++ [Bupdi15] := rfl
private theorem Bupds16 (c : Cfg) : Bupdp17 c = Bupdp16 c ++ [Bupdi16] := rfl
private theorem Bupds17 (c : Cfg) : Bupdp18 c = Bupdp17 c ++ [Bupdi17] := rfl
private theorem Bupds18 (c : Cfg) : Bupdp19 c = Bupdp18 c ++ [Bupdi18] := rfl
private theorem Bupds19 (c : Cfg) : Bupdp20 c = Bupdp19 c ++ [Bupdi19] := rfl
private theorem Bupds20 (c : Cfg) : Bupdp21 c = Bupdp20 c ++ [Bupdi20] := rfl
private theorem Bupds21 (c : Cfg) : Bupdp22 c = Bupdp21 c ++ [Bupdi21] := rfl
private theorem Bupds22 (c : Cfg) : Bupdp23 c = Bupdp22 c ++ [Bupdi22] := rfl
private theorem Bupds23 (c : Cfg) : Bupdp24 c = Bupdp23 c ++ [Bupdi23] := rfl
private theorem Bupds24 (c : Cfg) : Bupdp25 c = Bupdp24 c ++ [Bupdi24] := rfl
private theorem Bupds25 (c : Cfg) : Bupdp26 c = Bupdp25 c ++ [Bupdi25] := rfl
private theorem Bupds26 (c : Cfg) : Bupdp27 c = Bupdp26 c ++ [Bupdi26] := rfl
private theorem Bupds27 (c : Cfg) : Bupdp28 c = Bupdp27 c ++ [Bupdi27] := rfl
private theorem Bupds28 (c : Cfg) : Bupdp29 c = Bupdp28 c ++ [Bupdi28 c] := rfl

private theorem Bupdfull (c : Cfg) : updateBlock c = Bupdp29 c := rfl

private theorem Bupdg0_1 (c : Cfg) : Bupdp1 c = Bupdp0 c ++ [Bupdi0] := rfl
private theorem Bupdg0_2 (c : Cfg) : Bupdp2 c = Bupdp0 c ++ [Bupdi0, Bupdi1] := rfl
private theorem Bupdg0_3 (c : Cfg) : Bupdp3 c = Bupdp0 c ++ [Bupdi0, Bupdi1, Bupdi2] := rfl
private theorem Bupdg0_4 (c : Cfg) : Bupdp4 c = Bupdp0 c ++ [Bupdi0, Bupdi1, Bupdi2, Bupdi3] := rfl
private theorem Bupdg0_6 (c : Cfg) : Bupdp6 c = Bupdp0 c ++ [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5] := rfl
private theorem Bupdg0_7 (c : Cfg) : Bupdp7 c = Bupdp0 c ++ [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6] := rfl
private theorem Bupdg0_8 (c : Cfg) : Bupdp8 c = Bupdp0 c ++ [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7] := rfl
private theorem Bupdg0_9 (c : Cfg) : Bupdp9 c = Bupdp0 c ++ [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8] := rfl
private theorem Bupdg0_10 (c : Cfg) : Bupdp10 c = Bupdp0 c ++ [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9] := rfl
private theorem Bupdg0_12 (c : Cfg) : Bupdp12 c = Bupdp0 c ++ [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11] := rfl
private theorem Bupdg0_15 (c : Cfg) : Bupdp15 c = Bupdp0 c ++ [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14] := rfl
private theorem Bupdg0_16 (c : Cfg) : Bupdp16 c = Bupdp0 c ++ [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15] := rfl
private theorem Bupdg0_17 (c : Cfg) : Bupdp17 c = Bupdp0 c ++ [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15, Bupdi16] := rfl
private theorem Bupdg0_18 (c : Cfg) : Bupdp18 c = Bupdp0 c ++ [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15, Bupdi16, Bupdi17] := rfl
private theorem Bupdg0_22 (c : Cfg) : Bupdp22 c = Bupdp0 c ++ [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15, Bupdi16, Bupdi17, Bupdi18, Bupdi19, Bupdi20, Bupdi21] := rfl
private theorem Bupdg0_23 (c : Cfg) : Bupdp23 c = Bupdp0 c ++ [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15, Bupdi16, Bupdi17, Bupdi18, Bupdi19, Bupdi20, Bupdi21, Bupdi22] := rfl
private theorem Bupdg0_24 (c : Cfg) : Bupdp24 c = Bupdp0 c ++ [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15, Bupdi16, Bupdi17, Bupdi18, Bupdi19, Bupdi20, Bupdi21, Bupdi22, Bupdi23] := rfl
private theorem Bupdg0_26 (c : Cfg) : Bupdp26 c = Bupdp0 c ++ [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15, Bupdi16, Bupdi17, Bupdi18, Bupdi19, Bupdi20, Bupdi21, Bupdi22, Bupdi23, Bupdi24, Bupdi25] := rfl
private theorem Bupdg0_27 (c : Cfg) : Bupdp27 c = Bupdp0 c ++ [Bupdi0, Bupdi1, Bupdi2, Bupdi3, Bupdi4, Bupdi5, Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15, Bupdi16, Bupdi17, Bupdi18, Bupdi19, Bupdi20, Bupdi21, Bupdi22, Bupdi23, Bupdi24, Bupdi25, Bupdi26] := rfl
private theorem Bupdg3_5 (c : Cfg) : Bupdp5 c = Bupdp3 c ++ [Bupdi3, Bupdi4] := rfl
private theorem Bupdg6_29 (c : Cfg) : Bupdp29 c = Bupdp6 c ++ [Bupdi6, Bupdi7, Bupdi8, Bupdi9, Bupdi10, Bupdi11, Bupdi12, Bupdi13, Bupdi14, Bupdi15, Bupdi16, Bupdi17, Bupdi18, Bupdi19, Bupdi20, Bupdi21, Bupdi22, Bupdi23, Bupdi24, Bupdi25, Bupdi26, Bupdi27, Bupdi28 c] := rfl
private theorem Bupdg9_11 (c : Cfg) : Bupdp11 c = Bupdp9 c ++ [Bupdi9, Bupdi10] := rfl
private theorem Bupdg12_29 (c : Cfg) : Bupdp29 c = Bupdp12 c ++ [Bupdi12, Bupdi13, Bupdi14, Bupdi15, Bupdi16, Bupdi17, Bupdi18, Bupdi19, Bupdi20, Bupdi21, Bupdi22, Bupdi23, Bupdi24, Bupdi25, Bupdi26, Bupdi27, Bupdi28 c] := rfl
private theorem Bupdg13_14 (c : Cfg) : Bupdp14 c = Bupdp13 c ++ [Bupdi13] := rfl
private theorem Bupdg14_21 (c : Cfg) : Bupdp21 c = Bupdp14 c ++ [Bupdi14, Bupdi15, Bupdi16, Bupdi17, Bupdi18, Bupdi19, Bupdi20] := rfl
private theorem Bupdg15_20 (c : Cfg) : Bupdp20 c = Bupdp15 c ++ [Bupdi15, Bupdi16, Bupdi17, Bupdi18, Bupdi19] := rfl
private theorem Bupdg17_19 (c : Cfg) : Bupdp19 c = Bupdp17 c ++ [Bupdi17, Bupdi18] := rfl
private theorem Bupdg19_29 (c : Cfg) : Bupdp29 c = Bupdp19 c ++ [Bupdi19, Bupdi20, Bupdi21, Bupdi22, Bupdi23, Bupdi24, Bupdi25, Bupdi26, Bupdi27, Bupdi28 c] := rfl
private theorem Bupdg21_29 (c : Cfg) : Bupdp29 c = Bupdp21 c ++ [Bupdi21, Bupdi22, Bupdi23, Bupdi24, Bupdi25, Bupdi26, Bupdi27, Bupdi28 c] := rfl
private theorem Bupdg23_25 (c : Cfg) : Bupdp25 c = Bupdp23 c ++ [Bupdi23, Bupdi24] := rfl
private theorem Bupdg23_29 (c : Cfg) : Bupdp29 c = Bupdp23 c ++ [Bupdi23, Bupdi24, Bupdi25, Bupdi26, Bupdi27, Bupdi28 c] := rfl
private theorem Bupdg25_29 (c : Cfg) : Bupdp29 c = Bupdp25 c ++ [Bupdi25, Bupdi26, Bupdi27, Bupdi28 c] := rfl
private theorem Bupdg26_29 (c : Cfg) : Bupdp29 c = Bupdp26 c ++ [Bupdi26, Bupdi27, Bupdi28 c] := rfl
private theorem Bupdg27_29 (c : Cfg) : Bupdp29 c = Bupdp27 c ++ [Bupdi27, Bupdi28 c] := rfl


/-! ## The named outputs -/

/-- The block-maximum test. -/
def semGt (mx star : Nat) : Nat := bitOf (mx < star)
/-- The new block maximum. -/
def semMx (mx star : Nat) : Nat :=
  MA (MMul (semGt mx star) star) (MMul (MS 1 (semGt mx star)) mx)
/-- The individually-checked prefix `n < 64`. -/
def semSmall (n : Nat) : Nat := bitOf (n < 64)
/-- The value the row test compares. -/
def semCv (n star mx : Nat) : Nat :=
  MA (MMul (semSmall n) star) (MMul (MS 1 (semSmall n)) (semMx mx star))
/-- The check gate. -/
def semFire (n lim bs : Nat) : Nat :=
  bitOf ((n < 64 ∨ n = lim) ∨ MA 1 n = MMul 2 bs)
/-- The advanced ladder. -/
def semLam (lam ho n cc : Nat) : Nat :=
  MA lam (MMul (MMul (bitOf (ho ≤ n)) cc) (incUWord n))
/-- Below the handoff the logarithm comes from the table. -/
def semLo (n ho : Nat) : Nat := bitOf (n < ho)
/-- The logarithm the check uses. -/
def semLU (n ho v lam1 : Nat) : Nat :=
  MA (MMul (semLo n ho) v) (MMul (MS 1 (semLo n ho)) lam1)
/-- The row verdict: a 128-bit comparison against `4·2⁴⁸·2⁴⁸ = 2⁹⁸`. -/
def semOk (a b : Nat) : Nat :=
  bitOf ((MulWide.hl a b).2 < rhsHi ∨
    ((MulWide.hl a b).2 = rhsHi ∧ (MulWide.hl a b).1 = 0))
/-- A failed row, charged at the commit. -/
def semBadRow (bad ok fire cc : Nat) : Nat := MA bad (MMul (MMul (MS 1 ok) fire) cc)
/-- A work round's cap violations. -/
def semBadW (b acc ab capS capL w : Nat) : Nat :=
  MA b (MMul (bitOf (capS < acc ∨ capL < ab)) w)
/-- A commit round's cap violations. -/
def semBadC (b st absN lam capS capL capLog cc : Nat) : Nat :=
  MA b (MMul (bitOf ((capS < st ∨ capL < absN) ∨ capLog < lam)) cc)
/-- The packed cell to store. -/
def semCell (mun absN cc cell : Nat) : Nat :=
  MA (MMul (MA (MMul pack mun) absN) cc) (MMul (MS 1 cc) cell)
/-- The carried block maximum. -/
def semMax (fire mx cc mx0 : Nat) : Nat :=
  MA (MMul (MMul (MS 1 fire) mx) cc) (MMul (MS 1 cc) mx0)
/-- The dyadic block start, before the `n < 64` override. -/
def semBsIn (n fire bs : Nat) : Nat :=
  MA (MMul (MA 1 n) fire) (MMul (MS 1 fire) bs)
/-- The carried dyadic block start. -/
def semBs (n fire bs cc : Nat) : Nat :=
  MA (MMul (MA (MMul 64 (semSmall n)) (MMul (semBsIn n fire bs) (MS 1 (semSmall n)))) cc)
    (MMul (MS 1 cc) bs)
/-- The carried log-constant slot. -/
def semIdx (idx cc fire tab : Nat) : Nat := (MA idx (MMul cc fire)) % tab

/-! ## The value theorems -/

variable {c : Cfg}

/-! ### Arithmetic the two nontrivial blocks need

Every fact below is stated about a plain variable and proved once, so that no
`2⁴⁸`-scale numeral ever enters a goal with a long local context. -/

/-- A product of two flags is the flag of their conjunction, at `denoteOp`. -/
private theorem dop_mul_bit (p q : Prop) [Decidable p] [Decidable q] :
    denoteOp .mul (bitOf p) (bitOf q) = some (bitOf (p ∧ q)) :=
  (dop_mul _ _).trans (congrArg some (MMul_bit p q))

private theorem b32_lt_M : b32 < M := by decide

private theorem b32_ne_zero : b32 ≠ 0 := by decide

/-- A flag scaled by the half-limb base is still a word. -/
private theorem b32_bit_lt (p : Prop) [Decidable p] : b32 * bitOf p < M := by
  unfold bitOf
  split
  · decide
  · decide

/-- Every prefix of a sum that fits in a word fits in a word. -/
private theorem four_bounds {X Y Z T : Nat} (h : X + Y + Z = T) (hT : T < M) :
    X < M ∧ X + Y < M ∧ X + Y + Z < M := by
  omega

/-- The machine builds the high word in the order `mid/2³² + p₁₁ + 2³²·cm + cl`;
`Verified/MulWide.lean` writes it `p₁₁ + mid/2³² + cm·2³² + cl`. -/
private theorem hi_swap (x y z w : Nat) :
    x + y + z * b32 + w = y + x + b32 * z + w := by
  rw [Nat.add_comm x y, Nat.mul_comm z b32]

/-- The low word of `MulWide.hl`, in the machine's operand order. -/
private theorem hl_fst (a b : Nat) :
    (MulWide.hl a b).1
      = MA (a % b32 * (b % b32))
          (MMul b32 (MA (a % b32 * (b / b32)) (a / b32 * (b % b32)))) :=
  congrArg (MA (a % b32 * (b % b32)))
    (MMul_comm (MA (a % b32 * (b / b32)) (a / b32 * (b % b32))) b32)

/-- The high word of `MulWide.hl`, in the machine's accumulation order. -/
private theorem hl_snd (a b : Nat) :
    (MulWide.hl a b).2
      = MA (a % b32 * (b / b32)) (a / b32 * (b % b32)) / b32 + a / b32 * (b / b32)
          + b32 * bitOf (MA (a % b32 * (b / b32)) (a / b32 * (b % b32))
              < a % b32 * (b / b32))
          + bitOf ((MulWide.hl a b).1 < a % b32 * (b % b32)) :=
  (show (MulWide.hl a b).2
      = a / b32 * (b / b32) + MA (a % b32 * (b / b32)) (a / b32 * (b % b32)) / b32
          + bitOf (MA (a % b32 * (b / b32)) (a / b32 * (b % b32))
              < a % b32 * (b / b32)) * b32
          + bitOf ((MulWide.hl a b).1 < a % b32 * (b % b32)) from rfl).trans
    (hi_swap _ _ _ _)

/-- Shrinking the denominator can only grow the quotient. -/
private theorem ladder_div_mono {a p q : Nat} (h : p ≤ q) (hp : 0 < p) :
    a / q ≤ a / p := by
  rw [Nat.le_div_iff_mul_le hp]
  exact Nat.le_trans (Nat.mul_le_mul_left _ h) (Nat.div_mul_le_self a q)

private theorem ladder_sub_le (N : Nat) : fpD3 + N - 1 ≤ fpD3 + 2 * N := by omega

/-- Two truncated subtractions cannot leave the word range. -/
private theorem sub_sub_lt {X Y Z : Nat} (h : X < M) : X - Y - Z < M :=
  Nat.lt_of_le_of_lt (Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)) h

/-- Every intermediate of the ladder is a word, for `2 ≤ n ≤ 2³²`. -/
private theorem ladder_bounds {N : Nat} (hn : N ≤ 2 ^ 32) :
    N < M ∧ 2 * N < M ∧ fpD3 + 2 * N < M ∧ fpD3 + N < M ∧ fpDlit + N < M := by
  have h2 : 2 * N ≤ 2 * 2 ^ 32 := Nat.mul_le_mul (Nat.le_refl 2) hn
  exact ⟨Nat.lt_of_le_of_lt hn (by decide),
    Nat.lt_of_le_of_lt h2 (by decide),
    Nat.lt_of_le_of_lt (Nat.add_le_add_left h2 fpD3) (by decide),
    Nat.lt_of_le_of_lt (Nat.add_le_add_left hn fpD3) (by decide),
    Nat.lt_of_le_of_lt (Nat.add_le_add_left hn fpDlit) (by decide)⟩

/-- **The one genuinely arithmetic side condition of the ladder**: the
correction term never exceeds the quantity it is subtracted from.  Everything
runs through `3·2⁴⁸/(2n) + 1 ≤ 3·2⁴⁸/4 + 1 ≤ 2⁴⁸ − 1`, so no numeral larger
than `fpD3` ever reaches `omega`. -/
private theorem ladder_q_le (N : Nat) (h2 : 2 ≤ N) :
    (fpD3 + 2 * N - (fpD3 + N - 1) / N) / (2 * N) ≤ fpDlit + N - 1 := by
  have hpos : 0 < 2 * N := by omega
  have s1 : (fpD3 + 2 * N - (fpD3 + N - 1) / N) / (2 * N)
      ≤ (fpD3 + 2 * N) / (2 * N) := Nat.div_le_div_right (Nat.sub_le _ _)
  have s2 : (fpD3 + 2 * N) / (2 * N) = fpD3 / (2 * N) + 1 :=
    Nat.add_div_right _ hpos
  have s3 : fpD3 / (2 * N) ≤ fpD3 / 4 := ladder_div_mono (by omega) (by omega)
  have s4 : fpD3 / 4 + 1 ≤ fpDlit - 1 := by decide
  have s5 : 1 ≤ fpDlit := by decide
  omega

/-- The machine's ladder expression is `incUWord` on the nose: the constants
`fpD3` and `fpDlit` are `3·2⁴⁸` and `2⁴⁸`, and the operands are already in the
order `Ports/RS62Increments.lean` writes them. -/
private theorem ladder_iu_eq (N : Nat) :
    (fpDlit + N - 1 - (fpD3 + 2 * N - (fpD3 + N - 1) / N) / (2 * N)) / (N - 1)
      = incUWord N := by
  unfold incUWord
  rw [fpD3_eq, fpDlit_eq]

/-- The ladder walk, up to the increment: the three divisors it needs to be
nonzero, and the increment itself. -/
private theorem ladder_walk (k : Nat) (u : RegState) (h2 : 2 ≤ u rN)
    (hn : u rN ≤ 2 ^ 32) :
    srun k u (Bladp4 c) rN = u rN ∧
      srun k u (Bladp7 c) rT2 = 2 * u rN ∧
      srun k u (Bladp12 c) rT2 = u rN - 1 ∧
      srun k u (Bladp13 c) rIU = incUWord (u rN) := by
  obtain ⟨hNM, h2N, hb2, hb3, hb4⟩ := ladder_bounds hn
  have hN0 : u rN ≠ 0 := by omega
  have h2N0 : 2 * u rN ≠ 0 := by omega
  have hN10 : u rN - 1 ≠ 0 := by omega
  have hn0 : srun k u (Bladp0 c) rN = u rN := rfl
  have e0 : srun k u (Bladp1 c) rT1 = 2 * u rN :=
    step_write (Blads0 c) (denoteOperand_lit_of_lt k _ (by decide)) hn0
      (denoteOp_mul_of_lt h2N)
  have e1 : srun k u (Bladp2 c) rT1 = fpD3 + 2 * u rN :=
    step_write (Blads1 c) (denoteOperand_lit_of_lt k _ (by decide)) e0
      (denoteOp_add_of_lt hb2)
  have hn2 : srun k u (Bladp2 c) rN = u rN := run_frame (Bladg0_2 c) (by rfl) hn0
  have e2 : srun k u (Bladp3 c) rT2 = fpD3 + u rN :=
    step_write (Blads2 c) (denoteOperand_lit_of_lt k _ (by decide)) hn2
      (denoteOp_add_of_lt hb3)
  have e3 : srun k u (Bladp4 c) rT2 = fpD3 + u rN - 1 :=
    step_write (Blads3 c) e2 (denoteOperand_lit_of_lt k _ one_lt_M)
      (denoteOp_sub_of_le
        (Nat.le_trans (by decide : (1:Nat) ≤ fpD3) (Nat.le_add_right fpD3 (u rN)))
        hb3)
  have hn4 : srun k u (Bladp4 c) rN = u rN := run_frame (Bladg0_4 c) (by rfl) hn0
  have e4 : srun k u (Bladp5 c) rT2 = (fpD3 + u rN - 1) / u rN :=
    step_write (Blads4 c) e3 hn4
      (dop_udiv hN0 (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hb3))
  have hT1_5 : srun k u (Bladp5 c) rT1 = fpD3 + 2 * u rN :=
    run_frame (Bladg2_5 c) (by rfl) e1
  have e5 : srun k u (Bladp6 c) rT1
      = fpD3 + 2 * u rN - (fpD3 + u rN - 1) / u rN :=
    step_write (Blads5 c) hT1_5 e4
      (denoteOp_sub_of_le
        (Nat.le_trans (Nat.div_le_self _ _) (ladder_sub_le (u rN))) hb2)
  have hn6 : srun k u (Bladp6 c) rN = u rN := run_frame (Bladg0_6 c) (by rfl) hn0
  have e6 : srun k u (Bladp7 c) rT2 = 2 * u rN :=
    step_write (Blads6 c) (denoteOperand_lit_of_lt k _ (by decide)) hn6
      (denoteOp_mul_of_lt h2N)
  have hT1_7 : srun k u (Bladp7 c) rT1
      = fpD3 + 2 * u rN - (fpD3 + u rN - 1) / u rN :=
    run_frame (Bladg6_7 c) (by rfl) e5
  have e7 : srun k u (Bladp8 c) rT1
      = (fpD3 + 2 * u rN - (fpD3 + u rN - 1) / u rN) / (2 * u rN) :=
    step_write (Blads7 c) hT1_7 e6
      (dop_udiv h2N0 (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hb2))
  have hn8 : srun k u (Bladp8 c) rN = u rN := run_frame (Bladg0_8 c) (by rfl) hn0
  have e8 : srun k u (Bladp9 c) rT2 = fpDlit + u rN :=
    step_write (Blads8 c) (denoteOperand_lit_of_lt k _ (by decide)) hn8
      (denoteOp_add_of_lt hb4)
  have e9 : srun k u (Bladp10 c) rT2 = fpDlit + u rN - 1 :=
    step_write (Blads9 c) e8 (denoteOperand_lit_of_lt k _ one_lt_M)
      (denoteOp_sub_of_le
        (Nat.le_trans (by decide : (1:Nat) ≤ fpDlit)
          (Nat.le_add_right fpDlit (u rN)))
        hb4)
  have hT1_10 : srun k u (Bladp10 c) rT1
      = (fpD3 + 2 * u rN - (fpD3 + u rN - 1) / u rN) / (2 * u rN) :=
    run_frame (Bladg8_10 c) (by rfl) e7
  have e10 : srun k u (Bladp11 c) rT1
      = fpDlit + u rN - 1
          - (fpD3 + 2 * u rN - (fpD3 + u rN - 1) / u rN) / (2 * u rN) :=
    step_write (Blads10 c) e9 hT1_10
      (denoteOp_sub_of_le (ladder_q_le (u rN) h2)
        (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hb4))
  have hn11 : srun k u (Bladp11 c) rN = u rN :=
    run_frame (Bladg0_11 c) (by rfl) hn0
  have e11 : srun k u (Bladp12 c) rT2 = u rN - 1 :=
    step_write (Blads11 c) hn11 (denoteOperand_lit_of_lt k _ one_lt_M)
      (denoteOp_sub_of_le (by omega) hNM)
  have hT1_12 : srun k u (Bladp12 c) rT1
      = fpDlit + u rN - 1
          - (fpD3 + 2 * u rN - (fpD3 + u rN - 1) / u rN) / (2 * u rN) :=
    run_frame (Bladg11_12 c) (by rfl) e10
  have hdvd : fpDlit + u rN - 1
      - (fpD3 + 2 * u rN - (fpD3 + u rN - 1) / u rN) / (2 * u rN) < M :=
    sub_sub_lt hb4
  have e12a : srun k u (Bladp13 c) rIU
      = (fpDlit + u rN - 1
          - (fpD3 + 2 * u rN - (fpD3 + u rN - 1) / u rN) / (2 * u rN))
        / (u rN - 1) :=
    step_write (Blads12 c) hT1_12 e11 (dop_udiv hN10 hdvd)
  exact ⟨hn4, e6, e11, e12a.trans (ladder_iu_eq (u rN))⟩

/-- **`gateBlock`**: the block maximum, the compared value and the check gate. -/
theorem gateBlock_vals (k : Nat) (u : RegState) (hlim : c.limit < M) :
    srun k u (gateBlock c) rMx = semMx (u rMax) (u rSt) ∧
      srun k u (gateBlock c) rCv = semCv (u rN) (u rSt) (u rMax) ∧
      srun k u (gateBlock c) rFire = semFire (u rN) c.limit (u rBs) := by
  have hSt0 : srun k u (Bgatp0 c) rSt = u rSt := rfl
  have hMax0 : srun k u (Bgatp0 c) rMax = u rMax := rfl
  have hN0 : srun k u (Bgatp0 c) rN = u rN := rfl
  have hBs0 : srun k u (Bgatp0 c) rBs = u rBs := rfl
  have h1 : srun k u (Bgatp1 c) rT1 = bitOf (u rMax < u rSt) :=
    step_write (Bgats0 c) hSt0 hMax0 (dop_gt _ _)
  have h2 : srun k u (Bgatp2 c) rT2 = MS 1 (bitOf (u rMax < u rSt)) :=
    step_write (Bgats1 c) (denoteOperand_lit_of_lt k _ one_lt_M) h1 (dop_sub _ _)
  have hT1_2 : srun k u (Bgatp2 c) rT1 = bitOf (u rMax < u rSt) :=
    run_frame (Bgatg1_2 c) (by rfl) h1
  have hSt2 : srun k u (Bgatp2 c) rSt = u rSt := run_frame (Bgatg0_2 c) (by rfl) hSt0
  have h3 : srun k u (Bgatp3 c) rT3 = MMul (bitOf (u rMax < u rSt)) (u rSt) :=
    step_write (Bgats2 c) hT1_2 hSt2 (dop_mul _ _)
  have hT2_3 : srun k u (Bgatp3 c) rT2 = MS 1 (bitOf (u rMax < u rSt)) :=
    run_frame (Bgatg2_3 c) (by rfl) h2
  have hMax3 : srun k u (Bgatp3 c) rMax = u rMax :=
    run_frame (Bgatg0_3 c) (by rfl) hMax0
  have h4 : srun k u (Bgatp4 c) rT2
      = MMul (MS 1 (bitOf (u rMax < u rSt))) (u rMax) :=
    step_write (Bgats3 c) hT2_3 hMax3 (dop_mul _ _)
  have hT3_4 : srun k u (Bgatp4 c) rT3 = MMul (bitOf (u rMax < u rSt)) (u rSt) :=
    run_frame (Bgatg3_4 c) (by rfl) h3
  have h5 : srun k u (Bgatp5 c) rMx = semMx (u rMax) (u rSt) :=
    step_write (Bgats4 c) hT3_4 h4 (dop_add _ _)
  have hN5 : srun k u (Bgatp5 c) rN = u rN := run_frame (Bgatg0_5 c) (by rfl) hN0
  have h6 : srun k u (Bgatp6 c) rT1 = bitOf (u rN < 64) :=
    step_write (Bgats5 c) hN5 (denoteOperand_lit_of_lt k _ (by decide)) (dop_lt _ _)
  have h7 : srun k u (Bgatp7 c) rT2 = MS 1 (bitOf (u rN < 64)) :=
    step_write (Bgats6 c) (denoteOperand_lit_of_lt k _ one_lt_M) h6 (dop_sub _ _)
  have hT1_7 : srun k u (Bgatp7 c) rT1 = bitOf (u rN < 64) :=
    run_frame (Bgatg6_7 c) (by rfl) h6
  have hSt7 : srun k u (Bgatp7 c) rSt = u rSt := run_frame (Bgatg0_7 c) (by rfl) hSt0
  have h8 : srun k u (Bgatp8 c) rT3 = MMul (bitOf (u rN < 64)) (u rSt) :=
    step_write (Bgats7 c) hT1_7 hSt7 (dop_mul _ _)
  have hT2_8 : srun k u (Bgatp8 c) rT2 = MS 1 (bitOf (u rN < 64)) :=
    run_frame (Bgatg7_8 c) (by rfl) h7
  have hMx8 : srun k u (Bgatp8 c) rMx = semMx (u rMax) (u rSt) :=
    run_frame (Bgatg5_8 c) (by rfl) h5
  have h9 : srun k u (Bgatp9 c) rG
      = MMul (MS 1 (bitOf (u rN < 64))) (semMx (u rMax) (u rSt)) :=
    step_write (Bgats8 c) hT2_8 hMx8 (dop_mul _ _)
  have hT3_9 : srun k u (Bgatp9 c) rT3 = MMul (bitOf (u rN < 64)) (u rSt) :=
    run_frame (Bgatg8_9 c) (by rfl) h8
  have h10 : srun k u (Bgatp10 c) rCv = semCv (u rN) (u rSt) (u rMax) :=
    step_write (Bgats9 c) hT3_9 h9 (dop_add _ _)
  have hN10 : srun k u (Bgatp10 c) rN = u rN := run_frame (Bgatg0_10 c) (by rfl) hN0
  have h11 : srun k u (Bgatp11 c) rT2 = bitOf (u rN = c.limit) :=
    step_write (Bgats10 c) hN10 (denoteOperand_lit_of_lt k _ hlim) (dop_eq _ _)
  have hBs11 : srun k u (Bgatp11 c) rBs = u rBs :=
    run_frame (Bgatg0_11 c) (by rfl) hBs0
  have h12 : srun k u (Bgatp12 c) rT3 = MMul 2 (u rBs) :=
    step_write (Bgats11 c) (denoteOperand_lit_of_lt k _ (by decide)) hBs11
      (dop_mul _ _)
  have hN12 : srun k u (Bgatp12 c) rN = u rN := run_frame (Bgatg0_12 c) (by rfl) hN0
  have h13 : srun k u (Bgatp13 c) rG = MA 1 (u rN) :=
    step_write (Bgats12 c) (denoteOperand_lit_of_lt k _ one_lt_M) hN12 (dop_add _ _)
  have hT3_13 : srun k u (Bgatp13 c) rT3 = MMul 2 (u rBs) :=
    run_frame (Bgatg12_13 c) (by rfl) h12
  have h14 : srun k u (Bgatp14 c) rG = bitOf (MA 1 (u rN) = MMul 2 (u rBs)) :=
    step_write (Bgats13 c) h13 hT3_13 (dop_eq _ _)
  have hT1_14 : srun k u (Bgatp14 c) rT1 = bitOf (u rN < 64) :=
    run_frame (Bgatg6_14 c) (by rfl) h6
  have hT2_14 : srun k u (Bgatp14 c) rT2 = bitOf (u rN = c.limit) :=
    run_frame (Bgatg11_14 c) (by rfl) h11
  have h15 : srun k u (Bgatp15 c) rFire = bitOf (u rN < 64 ∨ u rN = c.limit) :=
    step_write (Bgats14 c) hT1_14 hT2_14 (dop_bor_bit _ _)
  have hG15 : srun k u (Bgatp15 c) rG = bitOf (MA 1 (u rN) = MMul 2 (u rBs)) :=
    run_frame (Bgatg14_15 c) (by rfl) h14
  have h16 : srun k u (Bgatp16 c) rFire = semFire (u rN) c.limit (u rBs) :=
    step_write (Bgats15 c) h15 hG15 (dop_bor_bit _ _)
  exact ⟨run_frame ((Bgatfull c).trans (Bgatg5_16 c)) (by rfl) h5,
    run_frame ((Bgatfull c).trans (Bgatg10_16 c)) (by rfl) h10,
    run_frame (Bgatfull c) (by rfl) h16⟩

theorem gateBlock_defined (k : Nat) (u : RegState) :
    SAllDefined k u (gateBlock c) := sAllDefined_of_noDiv k _ _ (by rfl)

/-- **`ladderBlock`**: `rIU` is `incUWord n` exactly. -/
theorem ladderBlock_iu (k : Nat) (u : RegState) (h2 : 2 ≤ u rN) (hn : u rN ≤ 2 ^ 32) :
    srun k u (ladderBlock c) rIU = incUWord (u rN) :=
  run_frame ((Bladfull c).trans (Bladg13_22 c)) (by rfl)
    (ladder_walk (c := c) k u h2 hn).2.2.2

/-- **`ladderBlock`**: the gated advance, and the logarithm the check uses. -/
theorem ladderBlock_vals (k : Nat) (u : RegState) (h2 : 2 ≤ u rN)
    (hn : u rN ≤ 2 ^ 32) (hho : c.handoff < M) :
    srun k u (ladderBlock c) rLam = semLam (u rLam) c.handoff (u rN) (u rC) ∧
      srun k u (ladderBlock c) rLU =
        semLU (u rN) c.handoff (u rV) (semLam (u rLam) c.handoff (u rN) (u rC)) := by
  have e12 := (ladder_walk (c := c) k u h2 hn).2.2.2
  have hn0 : srun k u (Bladp0 c) rN = u rN := rfl
  have hC0 : srun k u (Bladp0 c) rC = u rC := rfl
  have hLam0 : srun k u (Bladp0 c) rLam = u rLam := rfl
  have hV0 : srun k u (Bladp0 c) rV = u rV := rfl
  have hn13 : srun k u (Bladp13 c) rN = u rN := run_frame (Bladg0_13 c) (by rfl) hn0
  have f13 : srun k u (Bladp14 c) rT1 = bitOf (c.handoff ≤ u rN) :=
    step_write (Blads13 c) hn13 (denoteOperand_lit_of_lt k _ hho) (dop_ge _ _)
  have hC14 : srun k u (Bladp14 c) rC = u rC := run_frame (Bladg0_14 c) (by rfl) hC0
  have f14 : srun k u (Bladp15 c) rT1 = MMul (bitOf (c.handoff ≤ u rN)) (u rC) :=
    step_write (Blads14 c) f13 hC14 (dop_mul _ _)
  have hIU15 : srun k u (Bladp15 c) rIU = incUWord (u rN) :=
    run_frame (Bladg13_15 c) (by rfl) e12
  have f15 : srun k u (Bladp16 c) rT1
      = MMul (MMul (bitOf (c.handoff ≤ u rN)) (u rC)) (incUWord (u rN)) :=
    step_write (Blads15 c) f14 hIU15 (dop_mul _ _)
  have hLam16 : srun k u (Bladp16 c) rLam = u rLam :=
    run_frame (Bladg0_16 c) (by rfl) hLam0
  have f16 : srun k u (Bladp17 c) rLam = semLam (u rLam) c.handoff (u rN) (u rC) :=
    step_write (Blads16 c) hLam16 f15 (dop_add _ _)
  have hn17 : srun k u (Bladp17 c) rN = u rN := run_frame (Bladg0_17 c) (by rfl) hn0
  have f17 : srun k u (Bladp18 c) rT1 = bitOf (u rN < c.handoff) :=
    step_write (Blads17 c) hn17 (denoteOperand_lit_of_lt k _ hho) (dop_lt _ _)
  have f18 : srun k u (Bladp19 c) rT2 = MS 1 (bitOf (u rN < c.handoff)) :=
    step_write (Blads18 c) (denoteOperand_lit_of_lt k _ one_lt_M) f17 (dop_sub _ _)
  have hT1_19 : srun k u (Bladp19 c) rT1 = bitOf (u rN < c.handoff) :=
    run_frame (Bladg18_19 c) (by rfl) f17
  have hV19 : srun k u (Bladp19 c) rV = u rV := run_frame (Bladg0_19 c) (by rfl) hV0
  have f19 : srun k u (Bladp20 c) rT3 = MMul (bitOf (u rN < c.handoff)) (u rV) :=
    step_write (Blads19 c) hT1_19 hV19 (dop_mul _ _)
  have hT2_20 : srun k u (Bladp20 c) rT2 = MS 1 (bitOf (u rN < c.handoff)) :=
    run_frame (Bladg19_20 c) (by rfl) f18
  have hLam20 : srun k u (Bladp20 c) rLam = semLam (u rLam) c.handoff (u rN) (u rC) :=
    run_frame (Bladg17_20 c) (by rfl) f16
  have f20 : srun k u (Bladp21 c) rG
      = MMul (MS 1 (bitOf (u rN < c.handoff)))
          (semLam (u rLam) c.handoff (u rN) (u rC)) :=
    step_write (Blads20 c) hT2_20 hLam20 (dop_mul _ _)
  have hT3_21 : srun k u (Bladp21 c) rT3 = MMul (bitOf (u rN < c.handoff)) (u rV) :=
    run_frame (Bladg20_21 c) (by rfl) f19
  have f21 : srun k u (Bladp22 c) rLU
      = semLU (u rN) c.handoff (u rV) (semLam (u rLam) c.handoff (u rN) (u rC)) :=
    step_write (Blads21 c) hT3_21 f20 (dop_add _ _)
  exact ⟨run_frame ((Bladfull c).trans (Bladg17_22 c)) (by rfl) f16,
    run_frame (Bladfull c) (by rfl) f21⟩

theorem ladderBlock_defined (k : Nat) (u : RegState) (h2 : 2 ≤ u rN)
    (hn : u rN ≤ 2 ^ 32) : SAllDefined k u (ladderBlock c) := by
  obtain ⟨w4, w7, w12, -⟩ := ladder_walk (c := c) k u h2 hn
  show SAllDefined k u (Bladp4 c ++ Bladi4 ::
    ([Bladi5, Bladi6] ++ Bladi7 ::
      ([Bladi8, Bladi9, Bladi10, Bladi11] ++ Bladi12 ::
        [Bladi13 c, Bladi14, Bladi15, Bladi16, Bladi17 c, Bladi18, Bladi19,
          Bladi20, Bladi21])))
  refine sAllDefined_stage (by rfl) (sDefined_udiv ?_) ?_
  · show srun k u (Bladp4 c) rN ≠ 0
    rw [w4]; omega
  refine sAllDefined_stage (by rfl) (sDefined_udiv ?_) ?_
  · show srun k u (Bladp7 c) rT2 ≠ 0
    rw [w7]; omega
  refine sAllDefined_stage (by rfl) (sDefined_udiv ?_) ?_
  · show srun k u (Bladp12 c) rT2 ≠ 0
    rw [w12]; omega
  exact sAllDefined_of_noDiv k _ _ (by rfl)

/-- **`productBlock`**: the half-limb circuit, and the row verdict. -/
theorem productBlock_vals (k : Nat) (u : RegState) (hLU : u rLU < M) :
    srun k u productBlock rLo = (MulWide.hl (MMul 5 (u rCv)) (u rLU)).1 ∧
      srun k u productBlock rHi = (MulWide.hl (MMul 5 (u rCv)) (u rLU)).2 ∧
      srun k u productBlock rOk = semOk (MMul 5 (u rCv)) (u rLU) := by
  -- the four half-limb partial products are exact, because each factor is `< 2³²`
  have hA : MMul 5 (u rCv) < M := MMul_lt _ _
  have ha0 : MMul 5 (u rCv) % b32 < b32 := Nat.mod_lt _ (by decide)
  have ha1 : MMul 5 (u rCv) / b32 < b32 := (Nat.div_lt_iff_lt_mul (by decide)).mpr hA
  have hb0 : u rLU % b32 < b32 := Nat.mod_lt _ (by decide)
  have hb1 : u rLU / b32 < b32 := (Nat.div_lt_iff_lt_mul (by decide)).mpr hLU
  have h00 : MMul 5 (u rCv) % b32 * (u rLU % b32) < M :=
    MulWide.mul_lt_mul_of_lt_of_lt ha0 hb0
  have h01 : MMul 5 (u rCv) % b32 * (u rLU / b32) < M :=
    MulWide.mul_lt_mul_of_lt_of_lt ha0 hb1
  have h10 : MMul 5 (u rCv) / b32 * (u rLU % b32) < M :=
    MulWide.mul_lt_mul_of_lt_of_lt ha1 hb0
  have h11 : MMul 5 (u rCv) / b32 * (u rLU / b32) < M :=
    MulWide.mul_lt_mul_of_lt_of_lt ha1 hb1
  -- and every partial sum of the high word is below the high word, which is a word
  have hlt : (MulWide.hl (MMul 5 (u rCv)) (u rLU)).2 < M :=
    MulWide.hl_hi_lt _ _ hA hLU
  obtain ⟨bd1, bd2, bd3⟩ :=
    four_bounds (hl_snd (MMul 5 (u rCv)) (u rLU)).symm hlt
  have hCv0 : srun k u Bprdp0 rCv = u rCv := rfl
  have hLU0 : srun k u Bprdp0 rLU = u rLU := rfl
  have q0 : srun k u Bprdp1 rT1 = MMul 5 (u rCv) :=
    step_write Bprds0 (denoteOperand_lit_of_lt k _ (by decide)) hCv0 (dop_mul _ _)
  have q1 : srun k u Bprdp2 rT2 = MMul 5 (u rCv) % b32 :=
    step_write Bprds1 q0 (denoteOperand_lit_of_lt k _ b32_lt_M)
      (dop_urem b32_ne_zero hA)
  have hT1_2 : srun k u Bprdp2 rT1 = MMul 5 (u rCv) :=
    run_frame Bprdg1_2 (by rfl) q0
  have q2 : srun k u Bprdp3 rT3 = MMul 5 (u rCv) / b32 :=
    step_write Bprds2 hT1_2 (denoteOperand_lit_of_lt k _ b32_lt_M)
      (dop_udiv b32_ne_zero hA)
  have hLU3 : srun k u Bprdp3 rLU = u rLU := run_frame Bprdg0_3 (by rfl) hLU0
  have q3 : srun k u Bprdp4 rG = u rLU % b32 :=
    step_write Bprds3 hLU3 (denoteOperand_lit_of_lt k _ b32_lt_M)
      (dop_urem b32_ne_zero hLU)
  have hLU4 : srun k u Bprdp4 rLU = u rLU := run_frame Bprdg0_4 (by rfl) hLU0
  have q4 : srun k u Bprdp5 rH = u rLU / b32 :=
    step_write Bprds4 hLU4 (denoteOperand_lit_of_lt k _ b32_lt_M)
      (dop_udiv b32_ne_zero hLU)
  have hT2_5 : srun k u Bprdp5 rT2 = MMul 5 (u rCv) % b32 :=
    run_frame Bprdg2_5 (by rfl) q1
  have hG5 : srun k u Bprdp5 rG = u rLU % b32 := run_frame Bprdg4_5 (by rfl) q3
  have q5 : srun k u Bprdp6 rP00 = MMul 5 (u rCv) % b32 * (u rLU % b32) :=
    step_write Bprds5 hT2_5 hG5 (denoteOp_mul_of_lt h00)
  have hT2_6 : srun k u Bprdp6 rT2 = MMul 5 (u rCv) % b32 :=
    run_frame Bprdg2_6 (by rfl) q1
  have hH6 : srun k u Bprdp6 rH = u rLU / b32 := run_frame Bprdg5_6 (by rfl) q4
  have q6 : srun k u Bprdp7 rP01 = MMul 5 (u rCv) % b32 * (u rLU / b32) :=
    step_write Bprds6 hT2_6 hH6 (denoteOp_mul_of_lt h01)
  have hT3_7 : srun k u Bprdp7 rT3 = MMul 5 (u rCv) / b32 :=
    run_frame Bprdg3_7 (by rfl) q2
  have hG7 : srun k u Bprdp7 rG = u rLU % b32 := run_frame Bprdg4_7 (by rfl) q3
  have q7 : srun k u Bprdp8 rP10 = MMul 5 (u rCv) / b32 * (u rLU % b32) :=
    step_write Bprds7 hT3_7 hG7 (denoteOp_mul_of_lt h10)
  have hT3_8 : srun k u Bprdp8 rT3 = MMul 5 (u rCv) / b32 :=
    run_frame Bprdg3_8 (by rfl) q2
  have hH8 : srun k u Bprdp8 rH = u rLU / b32 := run_frame Bprdg5_8 (by rfl) q4
  have q8 : srun k u Bprdp9 rP11 = MMul 5 (u rCv) / b32 * (u rLU / b32) :=
    step_write Bprds8 hT3_8 hH8 (denoteOp_mul_of_lt h11)
  have hP01_9 : srun k u Bprdp9 rP01 = MMul 5 (u rCv) % b32 * (u rLU / b32) :=
    run_frame Bprdg7_9 (by rfl) q6
  have hP10_9 : srun k u Bprdp9 rP10 = MMul 5 (u rCv) / b32 * (u rLU % b32) :=
    run_frame Bprdg8_9 (by rfl) q7
  have q9 : srun k u Bprdp10 rMid
      = MA (MMul 5 (u rCv) % b32 * (u rLU / b32))
          (MMul 5 (u rCv) / b32 * (u rLU % b32)) :=
    step_write Bprds9 hP01_9 hP10_9 (dop_add _ _)
  have hP01_10 : srun k u Bprdp10 rP01 = MMul 5 (u rCv) % b32 * (u rLU / b32) :=
    run_frame Bprdg7_10 (by rfl) q6
  have q10 : srun k u Bprdp11 rCM
      = bitOf (MA (MMul 5 (u rCv) % b32 * (u rLU / b32))
          (MMul 5 (u rCv) / b32 * (u rLU % b32))
        < MMul 5 (u rCv) % b32 * (u rLU / b32)) :=
    step_write Bprds10 q9 hP01_10 (dop_lt _ _)
  have hMid_11 : srun k u Bprdp11 rMid
      = MA (MMul 5 (u rCv) % b32 * (u rLU / b32))
          (MMul 5 (u rCv) / b32 * (u rLU % b32)) :=
    run_frame Bprdg10_11 (by rfl) q9
  have q11 : srun k u Bprdp12 rT2
      = MMul b32 (MA (MMul 5 (u rCv) % b32 * (u rLU / b32))
          (MMul 5 (u rCv) / b32 * (u rLU % b32))) :=
    step_write Bprds11 (denoteOperand_lit_of_lt k _ b32_lt_M) hMid_11 (dop_mul _ _)
  have hP00_12 : srun k u Bprdp12 rP00 = MMul 5 (u rCv) % b32 * (u rLU % b32) :=
    run_frame Bprdg6_12 (by rfl) q5
  have q12 : srun k u Bprdp13 rLo = (MulWide.hl (MMul 5 (u rCv)) (u rLU)).1 :=
    (step_write Bprds12 hP00_12 q11 (dop_add _ _)).trans
      (hl_fst (MMul 5 (u rCv)) (u rLU)).symm
  have hP00_13 : srun k u Bprdp13 rP00 = MMul 5 (u rCv) % b32 * (u rLU % b32) :=
    run_frame Bprdg6_13 (by rfl) q5
  have q13 : srun k u Bprdp14 rCL
      = bitOf ((MulWide.hl (MMul 5 (u rCv)) (u rLU)).1
        < MMul 5 (u rCv) % b32 * (u rLU % b32)) :=
    step_write Bprds13 q12 hP00_13 (dop_lt _ _)
  have hMid_14 : srun k u Bprdp14 rMid
      = MA (MMul 5 (u rCv) % b32 * (u rLU / b32))
          (MMul 5 (u rCv) / b32 * (u rLU % b32)) :=
    run_frame Bprdg10_14 (by rfl) q9
  have q14 : srun k u Bprdp15 rHi
      = MA (MMul 5 (u rCv) % b32 * (u rLU / b32))
          (MMul 5 (u rCv) / b32 * (u rLU % b32)) / b32 :=
    step_write Bprds14 hMid_14 (denoteOperand_lit_of_lt k _ b32_lt_M)
      (dop_udiv b32_ne_zero (MA_lt _ _))
  have hP11_15 : srun k u Bprdp15 rP11 = MMul 5 (u rCv) / b32 * (u rLU / b32) :=
    run_frame Bprdg9_15 (by rfl) q8
  have q15 : srun k u Bprdp16 rHi
      = MA (MMul 5 (u rCv) % b32 * (u rLU / b32))
            (MMul 5 (u rCv) / b32 * (u rLU % b32)) / b32
          + MMul 5 (u rCv) / b32 * (u rLU / b32) :=
    step_write Bprds15 q14 hP11_15 (denoteOp_add_of_lt bd1)
  have hCM_16 : srun k u Bprdp16 rCM
      = bitOf (MA (MMul 5 (u rCv) % b32 * (u rLU / b32))
          (MMul 5 (u rCv) / b32 * (u rLU % b32))
        < MMul 5 (u rCv) % b32 * (u rLU / b32)) :=
    run_frame Bprdg11_16 (by rfl) q10
  have q16 : srun k u Bprdp17 rT2
      = b32 * bitOf (MA (MMul 5 (u rCv) % b32 * (u rLU / b32))
          (MMul 5 (u rCv) / b32 * (u rLU % b32))
        < MMul 5 (u rCv) % b32 * (u rLU / b32)) :=
    step_write Bprds16 (denoteOperand_lit_of_lt k _ b32_lt_M) hCM_16
      (denoteOp_mul_of_lt (b32_bit_lt _))
  have hHi_17 : srun k u Bprdp17 rHi
      = MA (MMul 5 (u rCv) % b32 * (u rLU / b32))
            (MMul 5 (u rCv) / b32 * (u rLU % b32)) / b32
          + MMul 5 (u rCv) / b32 * (u rLU / b32) :=
    run_frame Bprdg16_17 (by rfl) q15
  have q17 : srun k u Bprdp18 rHi
      = MA (MMul 5 (u rCv) % b32 * (u rLU / b32))
            (MMul 5 (u rCv) / b32 * (u rLU % b32)) / b32
          + MMul 5 (u rCv) / b32 * (u rLU / b32)
          + b32 * bitOf (MA (MMul 5 (u rCv) % b32 * (u rLU / b32))
              (MMul 5 (u rCv) / b32 * (u rLU % b32))
            < MMul 5 (u rCv) % b32 * (u rLU / b32)) :=
    step_write Bprds17 hHi_17 q16 (denoteOp_add_of_lt bd2)
  have hCL_18 : srun k u Bprdp18 rCL
      = bitOf ((MulWide.hl (MMul 5 (u rCv)) (u rLU)).1
        < MMul 5 (u rCv) % b32 * (u rLU % b32)) :=
    run_frame Bprdg14_18 (by rfl) q13
  have q18 : srun k u Bprdp19 rHi = (MulWide.hl (MMul 5 (u rCv)) (u rLU)).2 :=
    (step_write Bprds18 q17 hCL_18 (denoteOp_add_of_lt bd3)).trans
      (hl_snd (MMul 5 (u rCv)) (u rLU)).symm
  have q19 : srun k u Bprdp20 rT1
      = bitOf ((MulWide.hl (MMul 5 (u rCv)) (u rLU)).2 < rhsHi) :=
    step_write Bprds19 q18 (denoteOperand_lit_of_lt k _ (by decide)) (dop_lt _ _)
  have hHi_20 : srun k u Bprdp20 rHi = (MulWide.hl (MMul 5 (u rCv)) (u rLU)).2 :=
    run_frame Bprdg19_20 (by rfl) q18
  have q20 : srun k u Bprdp21 rT2
      = bitOf ((MulWide.hl (MMul 5 (u rCv)) (u rLU)).2 = rhsHi) :=
    step_write Bprds20 hHi_20 (denoteOperand_lit_of_lt k _ (by decide)) (dop_eq _ _)
  have hLo_21 : srun k u Bprdp21 rLo = (MulWide.hl (MMul 5 (u rCv)) (u rLU)).1 :=
    run_frame Bprdg13_21 (by rfl) q12
  have q21 : srun k u Bprdp22 rT3
      = bitOf ((MulWide.hl (MMul 5 (u rCv)) (u rLU)).1 = 0) :=
    step_write Bprds21 hLo_21 (denoteOperand_lit_of_lt k _ M_pos) (dop_eq _ _)
  have hT2_22 : srun k u Bprdp22 rT2
      = bitOf ((MulWide.hl (MMul 5 (u rCv)) (u rLU)).2 = rhsHi) :=
    run_frame Bprdg21_22 (by rfl) q20
  have q22 : srun k u Bprdp23 rT2
      = bitOf ((MulWide.hl (MMul 5 (u rCv)) (u rLU)).2 = rhsHi
        ∧ (MulWide.hl (MMul 5 (u rCv)) (u rLU)).1 = 0) :=
    step_write Bprds22 hT2_22 q21 (dop_mul_bit _ _)
  have hT1_23 : srun k u Bprdp23 rT1
      = bitOf ((MulWide.hl (MMul 5 (u rCv)) (u rLU)).2 < rhsHi) :=
    run_frame Bprdg20_23 (by rfl) q19
  have q23 : srun k u Bprdp24 rOk = semOk (MMul 5 (u rCv)) (u rLU) :=
    step_write Bprds23 hT1_23 q22 (dop_bor_bit _ _)
  exact ⟨run_frame (Bprdfull.trans Bprdg13_24) (by rfl) q12,
    run_frame (Bprdfull.trans Bprdg19_24) (by rfl) q18,
    run_frame Bprdfull (by rfl) q23⟩

theorem productBlock_defined (k : Nat) (u : RegState) :
    SAllDefined k u productBlock := by
  show SAllDefined k u (Bprdi0 :: Bprdi1 :: Bprdi2 :: Bprdi3 :: Bprdi4 ::
    ([Bprdi5, Bprdi6, Bprdi7, Bprdi8, Bprdi9, Bprdi10, Bprdi11, Bprdi12, Bprdi13]
      ++ Bprdi14 :: [Bprdi15, Bprdi16, Bprdi17, Bprdi18, Bprdi19, Bprdi20,
        Bprdi21, Bprdi22, Bprdi23]))
  refine sAllDefined_cons (sDefined_of_noDiv (by rfl)) ?_
  refine sAllDefined_cons (sDefined_urem (by rw [denoteOperand_lit]; decide)) ?_
  refine sAllDefined_cons (sDefined_udiv (by rw [denoteOperand_lit]; decide)) ?_
  refine sAllDefined_cons (sDefined_urem (by rw [denoteOperand_lit]; decide)) ?_
  refine sAllDefined_cons (sDefined_udiv (by rw [denoteOperand_lit]; decide)) ?_
  refine sAllDefined_stage (by rfl)
    (sDefined_udiv (by rw [denoteOperand_lit]; decide)) ?_
  exact sAllDefined_of_noDiv k _ _ (by rfl)

/-- **`badBlock`**: one violation per failed row and per cap that is left. -/
theorem badBlock_vals (k : Nat) (u : RegState) (hS : c.capS < M) (hL : c.capL < M)
    (hLog : c.capLog < M) :
    srun k u (badBlock c) rBad =
      semBadC (semBadW (semBadRow (u rBad) (u rOk) (u rFire) (u rC))
          (u rAcc) (u rAbs) c.capS c.capL (u rW))
        (u rSt) (u rAbsN) (u rLam) c.capS c.capL c.capLog (u rC) := by
  have hOk0 : srun k u (Bbadp0 c) rOk = u rOk := rfl
  have hFire0 : srun k u (Bbadp0 c) rFire = u rFire := rfl
  have hC0 : srun k u (Bbadp0 c) rC = u rC := rfl
  have hBad0 : srun k u (Bbadp0 c) rBad = u rBad := rfl
  have hAcc0 : srun k u (Bbadp0 c) rAcc = u rAcc := rfl
  have hAbs0 : srun k u (Bbadp0 c) rAbs = u rAbs := rfl
  have hW0 : srun k u (Bbadp0 c) rW = u rW := rfl
  have hSt0 : srun k u (Bbadp0 c) rSt = u rSt := rfl
  have hAbsN0 : srun k u (Bbadp0 c) rAbsN = u rAbsN := rfl
  have hLam0 : srun k u (Bbadp0 c) rLam = u rLam := rfl
  have h1 : srun k u (Bbadp1 c) rT1 = MS 1 (u rOk) :=
    step_write (Bbads0 c) (denoteOperand_lit_of_lt k _ one_lt_M) hOk0 (dop_sub _ _)
  have hFire1 : srun k u (Bbadp1 c) rFire = u rFire :=
    run_frame (Bbadg0_1 c) (by rfl) hFire0
  have h2 : srun k u (Bbadp2 c) rT1 = MMul (MS 1 (u rOk)) (u rFire) :=
    step_write (Bbads1 c) h1 hFire1 (dop_mul _ _)
  have hC2 : srun k u (Bbadp2 c) rC = u rC := run_frame (Bbadg0_2 c) (by rfl) hC0
  have h3 : srun k u (Bbadp3 c) rT1
      = MMul (MMul (MS 1 (u rOk)) (u rFire)) (u rC) :=
    step_write (Bbads2 c) h2 hC2 (dop_mul _ _)
  have hBad3 : srun k u (Bbadp3 c) rBad = u rBad :=
    run_frame (Bbadg0_3 c) (by rfl) hBad0
  have h4 : srun k u (Bbadp4 c) rBad
      = semBadRow (u rBad) (u rOk) (u rFire) (u rC) :=
    step_write (Bbads3 c) hBad3 h3 (dop_add _ _)
  have hAcc4 : srun k u (Bbadp4 c) rAcc = u rAcc :=
    run_frame (Bbadg0_4 c) (by rfl) hAcc0
  have h5 : srun k u (Bbadp5 c) rT2 = bitOf (c.capS < u rAcc) :=
    step_write (Bbads4 c) hAcc4 (denoteOperand_lit_of_lt k _ hS) (dop_gt _ _)
  have hAbs5 : srun k u (Bbadp5 c) rAbs = u rAbs :=
    run_frame (Bbadg0_5 c) (by rfl) hAbs0
  have h6 : srun k u (Bbadp6 c) rT3 = bitOf (c.capL < u rAbs) :=
    step_write (Bbads5 c) hAbs5 (denoteOperand_lit_of_lt k _ hL) (dop_gt _ _)
  have hT2_6 : srun k u (Bbadp6 c) rT2 = bitOf (c.capS < u rAcc) :=
    run_frame (Bbadg5_6 c) (by rfl) h5
  have h7 : srun k u (Bbadp7 c) rT2
      = bitOf (c.capS < u rAcc ∨ c.capL < u rAbs) :=
    step_write (Bbads6 c) hT2_6 h6 (dop_bor_bit _ _)
  have hW7 : srun k u (Bbadp7 c) rW = u rW := run_frame (Bbadg0_7 c) (by rfl) hW0
  have h8 : srun k u (Bbadp8 c) rT2
      = MMul (bitOf (c.capS < u rAcc ∨ c.capL < u rAbs)) (u rW) :=
    step_write (Bbads7 c) h7 hW7 (dop_mul _ _)
  have hBad8 : srun k u (Bbadp8 c) rBad
      = semBadRow (u rBad) (u rOk) (u rFire) (u rC) :=
    run_frame (Bbadg4_8 c) (by rfl) h4
  have h9 : srun k u (Bbadp9 c) rBad
      = semBadW (semBadRow (u rBad) (u rOk) (u rFire) (u rC))
          (u rAcc) (u rAbs) c.capS c.capL (u rW) :=
    step_write (Bbads8 c) hBad8 h8 (dop_add _ _)
  have hSt9 : srun k u (Bbadp9 c) rSt = u rSt := run_frame (Bbadg0_9 c) (by rfl) hSt0
  have h10 : srun k u (Bbadp10 c) rT2 = bitOf (c.capS < u rSt) :=
    step_write (Bbads9 c) hSt9 (denoteOperand_lit_of_lt k _ hS) (dop_gt _ _)
  have hAbsN10 : srun k u (Bbadp10 c) rAbsN = u rAbsN :=
    run_frame (Bbadg0_10 c) (by rfl) hAbsN0
  have h11 : srun k u (Bbadp11 c) rT3 = bitOf (c.capL < u rAbsN) :=
    step_write (Bbads10 c) hAbsN10 (denoteOperand_lit_of_lt k _ hL) (dop_gt _ _)
  have hT2_11 : srun k u (Bbadp11 c) rT2 = bitOf (c.capS < u rSt) :=
    run_frame (Bbadg10_11 c) (by rfl) h10
  have h12 : srun k u (Bbadp12 c) rT2
      = bitOf (c.capS < u rSt ∨ c.capL < u rAbsN) :=
    step_write (Bbads11 c) hT2_11 h11 (dop_bor_bit _ _)
  have hLam12 : srun k u (Bbadp12 c) rLam = u rLam :=
    run_frame (Bbadg0_12 c) (by rfl) hLam0
  have h13 : srun k u (Bbadp13 c) rT3 = bitOf (c.capLog < u rLam) :=
    step_write (Bbads12 c) hLam12 (denoteOperand_lit_of_lt k _ hLog) (dop_gt _ _)
  have hT2_13 : srun k u (Bbadp13 c) rT2
      = bitOf (c.capS < u rSt ∨ c.capL < u rAbsN) :=
    run_frame (Bbadg12_13 c) (by rfl) h12
  have h14 : srun k u (Bbadp14 c) rT2
      = bitOf ((c.capS < u rSt ∨ c.capL < u rAbsN) ∨ c.capLog < u rLam) :=
    step_write (Bbads13 c) hT2_13 h13 (dop_bor_bit _ _)
  have hC14 : srun k u (Bbadp14 c) rC = u rC := run_frame (Bbadg0_14 c) (by rfl) hC0
  have h15 : srun k u (Bbadp15 c) rT2
      = MMul (bitOf ((c.capS < u rSt ∨ c.capL < u rAbsN) ∨ c.capLog < u rLam))
          (u rC) :=
    step_write (Bbads14 c) h14 hC14 (dop_mul _ _)
  have hBad15 : srun k u (Bbadp15 c) rBad
      = semBadW (semBadRow (u rBad) (u rOk) (u rFire) (u rC))
          (u rAcc) (u rAbs) c.capS c.capL (u rW) :=
    run_frame (Bbadg9_15 c) (by rfl) h9
  have h16 : srun k u (Bbadp16 c) rBad
      = semBadC (semBadW (semBadRow (u rBad) (u rOk) (u rFire) (u rC))
            (u rAcc) (u rAbs) c.capS c.capL (u rW))
          (u rSt) (u rAbsN) (u rLam) c.capS c.capL c.capLog (u rC) :=
    step_write (Bbads15 c) hBad15 h15 (dop_add _ _)
  exact run_frame (Bbadfull c) (by rfl) h16

theorem badBlock_defined (k : Nat) (u : RegState) :
    SAllDefined k u (badBlock c) := sAllDefined_of_noDiv k _ _ (by rfl)

/-- **`updateBlock`**: the four registers a candidate hands to the next one. -/
theorem updateBlock_vals (k : Nat) (u : RegState) (htab : c.tab ≠ 0)
    (htabM : c.tab < M) :
    srun k u (updateBlock c) rCell = semCell (u rMun) (u rAbsN) (u rC) (u rCell) ∧
      srun k u (updateBlock c) rMax = semMax (u rFire) (u rMx) (u rC) (u rMax) ∧
      srun k u (updateBlock c) rBs = semBs (u rN) (u rFire) (u rBs) (u rC) ∧
      srun k u (updateBlock c) rIdx = semIdx (u rIdx) (u rC) (u rFire) c.tab := by
  have hMun0 : srun k u (Bupdp0 c) rMun = u rMun := rfl
  have hAbsN0 : srun k u (Bupdp0 c) rAbsN = u rAbsN := rfl
  have hC0 : srun k u (Bupdp0 c) rC = u rC := rfl
  have hCell0 : srun k u (Bupdp0 c) rCell = u rCell := rfl
  have hFire0 : srun k u (Bupdp0 c) rFire = u rFire := rfl
  have hMx0 : srun k u (Bupdp0 c) rMx = u rMx := rfl
  have hMax0 : srun k u (Bupdp0 c) rMax = u rMax := rfl
  have hN0 : srun k u (Bupdp0 c) rN = u rN := rfl
  have hBs0 : srun k u (Bupdp0 c) rBs = u rBs := rfl
  have hIdx0 : srun k u (Bupdp0 c) rIdx = u rIdx := rfl
  have h1 : srun k u (Bupdp1 c) rT1 = MMul pack (u rMun) :=
    step_write (Bupds0 c) (denoteOperand_lit_of_lt k _ (by decide)) hMun0
      (dop_mul _ _)
  have hAbsN1 : srun k u (Bupdp1 c) rAbsN = u rAbsN :=
    run_frame (Bupdg0_1 c) (by rfl) hAbsN0
  have h2 : srun k u (Bupdp2 c) rT1 = MA (MMul pack (u rMun)) (u rAbsN) :=
    step_write (Bupds1 c) h1 hAbsN1 (dop_add _ _)
  have hC2 : srun k u (Bupdp2 c) rC = u rC := run_frame (Bupdg0_2 c) (by rfl) hC0
  have h3 : srun k u (Bupdp3 c) rT1
      = MMul (MA (MMul pack (u rMun)) (u rAbsN)) (u rC) :=
    step_write (Bupds2 c) h2 hC2 (dop_mul _ _)
  have hC3 : srun k u (Bupdp3 c) rC = u rC := run_frame (Bupdg0_3 c) (by rfl) hC0
  have h4 : srun k u (Bupdp4 c) rT2 = MS 1 (u rC) :=
    step_write (Bupds3 c) (denoteOperand_lit_of_lt k _ one_lt_M) hC3 (dop_sub _ _)
  have hCell4 : srun k u (Bupdp4 c) rCell = u rCell :=
    run_frame (Bupdg0_4 c) (by rfl) hCell0
  have h5 : srun k u (Bupdp5 c) rT2 = MMul (MS 1 (u rC)) (u rCell) :=
    step_write (Bupds4 c) h4 hCell4 (dop_mul _ _)
  have hT1_5 : srun k u (Bupdp5 c) rT1
      = MMul (MA (MMul pack (u rMun)) (u rAbsN)) (u rC) :=
    run_frame (Bupdg3_5 c) (by rfl) h3
  have h6 : srun k u (Bupdp6 c) rCell
      = semCell (u rMun) (u rAbsN) (u rC) (u rCell) :=
    step_write (Bupds5 c) hT1_5 h5 (dop_add _ _)
  have hFire6 : srun k u (Bupdp6 c) rFire = u rFire :=
    run_frame (Bupdg0_6 c) (by rfl) hFire0
  have h7 : srun k u (Bupdp7 c) rT1 = MS 1 (u rFire) :=
    step_write (Bupds6 c) (denoteOperand_lit_of_lt k _ one_lt_M) hFire6
      (dop_sub _ _)
  have hMx7 : srun k u (Bupdp7 c) rMx = u rMx := run_frame (Bupdg0_7 c) (by rfl) hMx0
  have h8 : srun k u (Bupdp8 c) rT1 = MMul (MS 1 (u rFire)) (u rMx) :=
    step_write (Bupds7 c) h7 hMx7 (dop_mul _ _)
  have hC8 : srun k u (Bupdp8 c) rC = u rC := run_frame (Bupdg0_8 c) (by rfl) hC0
  have h9 : srun k u (Bupdp9 c) rT1
      = MMul (MMul (MS 1 (u rFire)) (u rMx)) (u rC) :=
    step_write (Bupds8 c) h8 hC8 (dop_mul _ _)
  have hC9 : srun k u (Bupdp9 c) rC = u rC := run_frame (Bupdg0_9 c) (by rfl) hC0
  have h10 : srun k u (Bupdp10 c) rT2 = MS 1 (u rC) :=
    step_write (Bupds9 c) (denoteOperand_lit_of_lt k _ one_lt_M) hC9 (dop_sub _ _)
  have hMax10 : srun k u (Bupdp10 c) rMax = u rMax :=
    run_frame (Bupdg0_10 c) (by rfl) hMax0
  have h11 : srun k u (Bupdp11 c) rT2 = MMul (MS 1 (u rC)) (u rMax) :=
    step_write (Bupds10 c) h10 hMax10 (dop_mul _ _)
  have hT1_11 : srun k u (Bupdp11 c) rT1
      = MMul (MMul (MS 1 (u rFire)) (u rMx)) (u rC) :=
    run_frame (Bupdg9_11 c) (by rfl) h9
  have h12 : srun k u (Bupdp12 c) rMax
      = semMax (u rFire) (u rMx) (u rC) (u rMax) :=
    step_write (Bupds11 c) hT1_11 h11 (dop_add _ _)
  have hN12 : srun k u (Bupdp12 c) rN = u rN := run_frame (Bupdg0_12 c) (by rfl) hN0
  have h13 : srun k u (Bupdp13 c) rT1 = bitOf (u rN < 64) :=
    step_write (Bupds12 c) hN12 (denoteOperand_lit_of_lt k _ (by decide))
      (dop_lt _ _)
  have h14 : srun k u (Bupdp14 c) rT2 = MMul 64 (bitOf (u rN < 64)) :=
    step_write (Bupds13 c) (denoteOperand_lit_of_lt k _ (by decide)) h13
      (dop_mul _ _)
  have hT1_14 : srun k u (Bupdp14 c) rT1 = bitOf (u rN < 64) :=
    run_frame (Bupdg13_14 c) (by rfl) h13
  have h15 : srun k u (Bupdp15 c) rT3 = MS 1 (bitOf (u rN < 64)) :=
    step_write (Bupds14 c) (denoteOperand_lit_of_lt k _ one_lt_M) hT1_14
      (dop_sub _ _)
  have hN15 : srun k u (Bupdp15 c) rN = u rN := run_frame (Bupdg0_15 c) (by rfl) hN0
  have h16 : srun k u (Bupdp16 c) rG = MA 1 (u rN) :=
    step_write (Bupds15 c) (denoteOperand_lit_of_lt k _ one_lt_M) hN15 (dop_add _ _)
  have hFire16 : srun k u (Bupdp16 c) rFire = u rFire :=
    run_frame (Bupdg0_16 c) (by rfl) hFire0
  have h17 : srun k u (Bupdp17 c) rG = MMul (MA 1 (u rN)) (u rFire) :=
    step_write (Bupds16 c) h16 hFire16 (dop_mul _ _)
  have hFire17 : srun k u (Bupdp17 c) rFire = u rFire :=
    run_frame (Bupdg0_17 c) (by rfl) hFire0
  have h18 : srun k u (Bupdp18 c) rH = MS 1 (u rFire) :=
    step_write (Bupds17 c) (denoteOperand_lit_of_lt k _ one_lt_M) hFire17
      (dop_sub _ _)
  have hBs18 : srun k u (Bupdp18 c) rBs = u rBs :=
    run_frame (Bupdg0_18 c) (by rfl) hBs0
  have h19 : srun k u (Bupdp19 c) rH = MMul (MS 1 (u rFire)) (u rBs) :=
    step_write (Bupds18 c) h18 hBs18 (dop_mul _ _)
  have hG19 : srun k u (Bupdp19 c) rG = MMul (MA 1 (u rN)) (u rFire) :=
    run_frame (Bupdg17_19 c) (by rfl) h17
  have h20 : srun k u (Bupdp20 c) rG = semBsIn (u rN) (u rFire) (u rBs) :=
    step_write (Bupds19 c) hG19 h19 (dop_add _ _)
  have hT3_20 : srun k u (Bupdp20 c) rT3 = MS 1 (bitOf (u rN < 64)) :=
    run_frame (Bupdg15_20 c) (by rfl) h15
  have h21 : srun k u (Bupdp21 c) rG
      = MMul (semBsIn (u rN) (u rFire) (u rBs)) (MS 1 (bitOf (u rN < 64))) :=
    step_write (Bupds20 c) h20 hT3_20 (dop_mul _ _)
  have hT2_21 : srun k u (Bupdp21 c) rT2 = MMul 64 (bitOf (u rN < 64)) :=
    run_frame (Bupdg14_21 c) (by rfl) h14
  have h22 : srun k u (Bupdp22 c) rT2
      = MA (MMul 64 (bitOf (u rN < 64)))
          (MMul (semBsIn (u rN) (u rFire) (u rBs)) (MS 1 (bitOf (u rN < 64)))) :=
    step_write (Bupds21 c) hT2_21 h21 (dop_add _ _)
  have hC22 : srun k u (Bupdp22 c) rC = u rC := run_frame (Bupdg0_22 c) (by rfl) hC0
  have h23 : srun k u (Bupdp23 c) rT2
      = MMul (MA (MMul 64 (bitOf (u rN < 64)))
          (MMul (semBsIn (u rN) (u rFire) (u rBs)) (MS 1 (bitOf (u rN < 64)))))
        (u rC) :=
    step_write (Bupds22 c) h22 hC22 (dop_mul _ _)
  have hC23 : srun k u (Bupdp23 c) rC = u rC := run_frame (Bupdg0_23 c) (by rfl) hC0
  have h24 : srun k u (Bupdp24 c) rT3 = MS 1 (u rC) :=
    step_write (Bupds23 c) (denoteOperand_lit_of_lt k _ one_lt_M) hC23 (dop_sub _ _)
  have hBs24 : srun k u (Bupdp24 c) rBs = u rBs :=
    run_frame (Bupdg0_24 c) (by rfl) hBs0
  have h25 : srun k u (Bupdp25 c) rT3 = MMul (MS 1 (u rC)) (u rBs) :=
    step_write (Bupds24 c) h24 hBs24 (dop_mul _ _)
  have hT2_25 : srun k u (Bupdp25 c) rT2
      = MMul (MA (MMul 64 (bitOf (u rN < 64)))
          (MMul (semBsIn (u rN) (u rFire) (u rBs)) (MS 1 (bitOf (u rN < 64)))))
        (u rC) :=
    run_frame (Bupdg23_25 c) (by rfl) h23
  have h26 : srun k u (Bupdp26 c) rBs = semBs (u rN) (u rFire) (u rBs) (u rC) :=
    step_write (Bupds25 c) hT2_25 h25 (dop_add _ _)
  have hC26 : srun k u (Bupdp26 c) rC = u rC := run_frame (Bupdg0_26 c) (by rfl) hC0
  have hFire26 : srun k u (Bupdp26 c) rFire = u rFire :=
    run_frame (Bupdg0_26 c) (by rfl) hFire0
  have h27 : srun k u (Bupdp27 c) rT1 = MMul (u rC) (u rFire) :=
    step_write (Bupds26 c) hC26 hFire26 (dop_mul _ _)
  have hIdx27 : srun k u (Bupdp27 c) rIdx = u rIdx :=
    run_frame (Bupdg0_27 c) (by rfl) hIdx0
  have h28 : srun k u (Bupdp28 c) rIdx = MA (u rIdx) (MMul (u rC) (u rFire)) :=
    step_write (Bupds27 c) hIdx27 h27 (dop_add _ _)
  have h29 : srun k u (Bupdp29 c) rIdx
      = semIdx (u rIdx) (u rC) (u rFire) c.tab :=
    step_write (Bupds28 c) h28 (denoteOperand_lit_of_lt k _ htabM)
      (dop_urem htab (MA_lt _ _))
  exact ⟨run_frame ((Bupdfull c).trans (Bupdg6_29 c)) (by rfl) h6,
    run_frame ((Bupdfull c).trans (Bupdg12_29 c)) (by rfl) h12,
    run_frame ((Bupdfull c).trans (Bupdg26_29 c)) (by rfl) h26,
    run_frame (Bupdfull c) (by rfl) h29⟩

theorem updateBlock_defined (k : Nat) (u : RegState) (htab : c.tab ≠ 0)
    (htabM : c.tab < M) : SAllDefined k u (updateBlock c) := by
  show SAllDefined k u (Bupdp28 c ++ Bupdi28 c :: [])
  refine sAllDefined_stage (by rfl) (sDefined_urem ?_) ?_
  · rw [denoteOperand_lit, Nat.mod_eq_of_lt htabM]
    exact htab
  trivial

end LeanCompCert.Ports.RamareMStar140M
