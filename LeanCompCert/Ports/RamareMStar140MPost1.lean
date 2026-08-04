import LeanCompCert.Ports.RamareMStar140MCore

/-!
# The post-load stage of the `m★` body, part one

`unpackBlock`, `termBlock`, `latchBlock`, `muBlock`, `lbBlock`, `starBlock`:
the thirty-seven instructions that turn the loaded cell into this candidate's
`|L|`, its Möbius value and its `star`.

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
open LeanCompCert.Verified.InstrBlock (srun sval sdest SDefined SAllDefined NoDivI)

/-! ### `unpackBlock` -/

private def Bunpi0 : Instr := .binop rMu1 .lshr (.reg rV) (.lit 52)
private def Bunpi1 : Instr := .binop rT1 .shl (.reg rMu1) (.lit 52)
private def Bunpi2 : Instr := .binop rAbs .sub (.reg rV) (.reg rT1)

private def Bunpp0 : List Instr := []
private def Bunpp1 : List Instr := [Bunpi0]
private def Bunpp2 : List Instr := [Bunpi0, Bunpi1]
private def Bunpp3 : List Instr := [Bunpi0, Bunpi1, Bunpi2]

private theorem Bunps0 : Bunpp1 = Bunpp0 ++ [Bunpi0] := rfl
private theorem Bunps1 : Bunpp2 = Bunpp1 ++ [Bunpi1] := rfl
private theorem Bunps2 : Bunpp3 = Bunpp2 ++ [Bunpi2] := rfl

private theorem Bunpfull : unpackBlock = Bunpp3 := rfl

private theorem Bunpg0_2 : Bunpp2 = Bunpp0 ++ [Bunpi0, Bunpi1] := rfl
private theorem Bunpg1_3 : Bunpp3 = Bunpp1 ++ [Bunpi1, Bunpi2] := rfl
private theorem Bunpg2_3 : Bunpp3 = Bunpp2 ++ [Bunpi2] := rfl

/-! ### `termBlock` -/

private def Btrmi0 : Instr := .binop rT1 .add (.reg rAbs) (.reg rQq)
private def Btrmi1 : Instr := .binop rT1 .add (.reg rT1) (.reg rSq)
private def Btrmi2 : Instr := .binop rT1 .sub (.reg rT1) (.lit 1)
private def Btrmi3 : Instr := .binop rT1 .udiv (.reg rT1) (.reg rSq)
private def Btrmi4 : Instr := .binop rT1 .mul (.reg rT1) (.reg rW)
private def Btrmi5 : Instr := .binop rAcc .add (.reg rAcc) (.reg rT1)

private def Btrmp0 : List Instr := []
private def Btrmp1 : List Instr := [Btrmi0]
private def Btrmp2 : List Instr := [Btrmi0, Btrmi1]
private def Btrmp3 : List Instr := [Btrmi0, Btrmi1, Btrmi2]
private def Btrmp4 : List Instr := [Btrmi0, Btrmi1, Btrmi2, Btrmi3]
private def Btrmp5 : List Instr := [Btrmi0, Btrmi1, Btrmi2, Btrmi3, Btrmi4]
private def Btrmp6 : List Instr := [Btrmi0, Btrmi1, Btrmi2, Btrmi3, Btrmi4, Btrmi5]

private theorem Btrms0 : Btrmp1 = Btrmp0 ++ [Btrmi0] := rfl
private theorem Btrms1 : Btrmp2 = Btrmp1 ++ [Btrmi1] := rfl
private theorem Btrms2 : Btrmp3 = Btrmp2 ++ [Btrmi2] := rfl
private theorem Btrms3 : Btrmp4 = Btrmp3 ++ [Btrmi3] := rfl
private theorem Btrms4 : Btrmp5 = Btrmp4 ++ [Btrmi4] := rfl
private theorem Btrms5 : Btrmp6 = Btrmp5 ++ [Btrmi5] := rfl

private theorem Btrmfull : termBlock = Btrmp6 := rfl

private theorem Btrmg0_1 : Btrmp1 = Btrmp0 ++ [Btrmi0] := rfl
private theorem Btrmg0_3 : Btrmp3 = Btrmp0 ++ [Btrmi0, Btrmi1, Btrmi2] := rfl
private theorem Btrmg0_4 : Btrmp4 = Btrmp0 ++ [Btrmi0, Btrmi1, Btrmi2, Btrmi3] := rfl
private theorem Btrmg0_5 : Btrmp5 = Btrmp0 ++ [Btrmi0, Btrmi1, Btrmi2, Btrmi3, Btrmi4] := rfl
private theorem Btrmg5_6 : Btrmp6 = Btrmp5 ++ [Btrmi5] := rfl

/-! ### `latchBlock` -/

private def Blati0 : Instr := .binop rT1 .sub (.lit 1) (.reg rQg)
private def Blati1 : Instr := .binop rT1 .mul (.reg rT1) (.reg rMuQ)
private def Blati2 : Instr := .binop rT2 .mul (.reg rQg) (.reg rMu1)
private def Blati3 : Instr := .binop rMuQ .add (.reg rT1) (.reg rT2)

private def Blatp0 : List Instr := []
private def Blatp1 : List Instr := [Blati0]
private def Blatp2 : List Instr := [Blati0, Blati1]
private def Blatp3 : List Instr := [Blati0, Blati1, Blati2]
private def Blatp4 : List Instr := [Blati0, Blati1, Blati2, Blati3]

private theorem Blats0 : Blatp1 = Blatp0 ++ [Blati0] := rfl
private theorem Blats1 : Blatp2 = Blatp1 ++ [Blati1] := rfl
private theorem Blats2 : Blatp3 = Blatp2 ++ [Blati2] := rfl
private theorem Blats3 : Blatp4 = Blatp3 ++ [Blati3] := rfl

private theorem Blatfull : latchBlock = Blatp4 := rfl

private theorem Blatg0_1 : Blatp1 = Blatp0 ++ [Blati0] := rfl
private theorem Blatg0_2 : Blatp2 = Blatp0 ++ [Blati0, Blati1] := rfl
private theorem Blatg2_3 : Blatp3 = Blatp2 ++ [Blati2] := rfl
private theorem Blatg2_4 : Blatp4 = Blatp2 ++ [Blati2, Blati3] := rfl
private theorem Blatg3_4 : Blatp4 = Blatp3 ++ [Blati3] := rfl

/-! ### `muBlock` -/

private def Bmui0 : Instr := .binop rT1 .urem (.reg rQ) (.reg rP)
private def Bmui1 : Instr := .binop rT1 .eq (.reg rT1) (.lit 0)
private def Bmui2 : Instr := .binop rT2 .sub (.lit 1) (.reg rT1)
private def Bmui3 : Instr := .binop rT3 .sub (.lit 2) (.reg rMuQ)
private def Bmui4 : Instr := .binop rT3 .mul (.reg rT3) (.reg rT2)
private def Bmui5 : Instr := .binop rMun .add (.reg rT1) (.reg rT3)

private def Bmup0 : List Instr := []
private def Bmup1 : List Instr := [Bmui0]
private def Bmup2 : List Instr := [Bmui0, Bmui1]
private def Bmup3 : List Instr := [Bmui0, Bmui1, Bmui2]
private def Bmup4 : List Instr := [Bmui0, Bmui1, Bmui2, Bmui3]
private def Bmup5 : List Instr := [Bmui0, Bmui1, Bmui2, Bmui3, Bmui4]
private def Bmup6 : List Instr := [Bmui0, Bmui1, Bmui2, Bmui3, Bmui4, Bmui5]

private theorem Bmus0 : Bmup1 = Bmup0 ++ [Bmui0] := rfl
private theorem Bmus1 : Bmup2 = Bmup1 ++ [Bmui1] := rfl
private theorem Bmus2 : Bmup3 = Bmup2 ++ [Bmui2] := rfl
private theorem Bmus3 : Bmup4 = Bmup3 ++ [Bmui3] := rfl
private theorem Bmus4 : Bmup5 = Bmup4 ++ [Bmui4] := rfl
private theorem Bmus5 : Bmup6 = Bmup5 ++ [Bmui5] := rfl

private theorem Bmufull : muBlock = Bmup6 := rfl

private theorem Bmug0_3 : Bmup3 = Bmup0 ++ [Bmui0, Bmui1, Bmui2] := rfl
private theorem Bmug2_5 : Bmup5 = Bmup2 ++ [Bmui2, Bmui3, Bmui4] := rfl
private theorem Bmug2_6 : Bmup6 = Bmup2 ++ [Bmui2, Bmui3, Bmui4, Bmui5] := rfl
private theorem Bmug3_4 : Bmup4 = Bmup3 ++ [Bmui3] := rfl
private theorem Bmug3_6 : Bmup6 = Bmup3 ++ [Bmui3, Bmui4, Bmui5] := rfl
private theorem Bmug5_6 : Bmup6 = Bmup5 ++ [Bmui5] := rfl

/-! ### `lbBlock` -/

private def Blbi0 : Instr := .binop rDn .udiv (.lit fpDlit) (.reg rN)
private def Blbi1 : Instr := .binop rT1 .eq (.reg rMun) (.lit 2)
private def Blbi2 : Instr := .binop rT1 .mul (.reg rT1) (.reg rC)
private def Blbi3 : Instr := .binop rT1 .mul (.reg rT1) (.reg rDn)
private def Blbi4 : Instr := .binop rLb .add (.reg rLb) (.reg rT1)
private def Blbi5 : Instr := .binop rT2 .eq (.reg rMun) (.lit 0)
private def Blbi6 : Instr := .binop rT2 .mul (.reg rT2) (.reg rC)
private def Blbi7 : Instr := .binop rT2 .mul (.reg rT2) (.reg rDn)
private def Blbi8 : Instr := .binop rLb .sub (.reg rLb) (.reg rT2)
private def Blbi9 : Instr := .binop rT1 .ge (.reg rLb) (.lit bias)
private def Blbi10 : Instr := .binop rT2 .sub (.reg rLb) (.lit bias)
private def Blbi11 : Instr := .binop rT2 .mul (.reg rT2) (.reg rT1)
private def Blbi12 : Instr := .binop rT3 .sub (.lit bias) (.reg rLb)
private def Blbi13 : Instr := .binop rG .sub (.lit 1) (.reg rT1)
private def Blbi14 : Instr := .binop rT3 .mul (.reg rT3) (.reg rG)
private def Blbi15 : Instr := .binop rAbsN .add (.reg rT2) (.reg rT3)

private def Blbp0 : List Instr := []
private def Blbp1 : List Instr := [Blbi0]
private def Blbp2 : List Instr := [Blbi0, Blbi1]
private def Blbp3 : List Instr := [Blbi0, Blbi1, Blbi2]
private def Blbp4 : List Instr := [Blbi0, Blbi1, Blbi2, Blbi3]
private def Blbp5 : List Instr := [Blbi0, Blbi1, Blbi2, Blbi3, Blbi4]
private def Blbp6 : List Instr := [Blbi0, Blbi1, Blbi2, Blbi3, Blbi4, Blbi5]
private def Blbp7 : List Instr := [Blbi0, Blbi1, Blbi2, Blbi3, Blbi4, Blbi5, Blbi6]
private def Blbp8 : List Instr := [Blbi0, Blbi1, Blbi2, Blbi3, Blbi4, Blbi5, Blbi6, Blbi7]
private def Blbp9 : List Instr := [Blbi0, Blbi1, Blbi2, Blbi3, Blbi4, Blbi5, Blbi6, Blbi7, Blbi8]
private def Blbp10 : List Instr := [Blbi0, Blbi1, Blbi2, Blbi3, Blbi4, Blbi5, Blbi6, Blbi7, Blbi8, Blbi9]
private def Blbp11 : List Instr := [Blbi0, Blbi1, Blbi2, Blbi3, Blbi4, Blbi5, Blbi6, Blbi7, Blbi8, Blbi9, Blbi10]
private def Blbp12 : List Instr := [Blbi0, Blbi1, Blbi2, Blbi3, Blbi4, Blbi5, Blbi6, Blbi7, Blbi8, Blbi9, Blbi10, Blbi11]
private def Blbp13 : List Instr := [Blbi0, Blbi1, Blbi2, Blbi3, Blbi4, Blbi5, Blbi6, Blbi7, Blbi8, Blbi9, Blbi10, Blbi11, Blbi12]
private def Blbp14 : List Instr := [Blbi0, Blbi1, Blbi2, Blbi3, Blbi4, Blbi5, Blbi6, Blbi7, Blbi8, Blbi9, Blbi10, Blbi11, Blbi12, Blbi13]
private def Blbp15 : List Instr := [Blbi0, Blbi1, Blbi2, Blbi3, Blbi4, Blbi5, Blbi6, Blbi7, Blbi8, Blbi9, Blbi10, Blbi11, Blbi12, Blbi13, Blbi14]
private def Blbp16 : List Instr := [Blbi0, Blbi1, Blbi2, Blbi3, Blbi4, Blbi5, Blbi6, Blbi7, Blbi8, Blbi9, Blbi10, Blbi11, Blbi12, Blbi13, Blbi14, Blbi15]

private theorem Blbs0 : Blbp1 = Blbp0 ++ [Blbi0] := rfl
private theorem Blbs1 : Blbp2 = Blbp1 ++ [Blbi1] := rfl
private theorem Blbs2 : Blbp3 = Blbp2 ++ [Blbi2] := rfl
private theorem Blbs3 : Blbp4 = Blbp3 ++ [Blbi3] := rfl
private theorem Blbs4 : Blbp5 = Blbp4 ++ [Blbi4] := rfl
private theorem Blbs5 : Blbp6 = Blbp5 ++ [Blbi5] := rfl
private theorem Blbs6 : Blbp7 = Blbp6 ++ [Blbi6] := rfl
private theorem Blbs7 : Blbp8 = Blbp7 ++ [Blbi7] := rfl
private theorem Blbs8 : Blbp9 = Blbp8 ++ [Blbi8] := rfl
private theorem Blbs9 : Blbp10 = Blbp9 ++ [Blbi9] := rfl
private theorem Blbs10 : Blbp11 = Blbp10 ++ [Blbi10] := rfl
private theorem Blbs11 : Blbp12 = Blbp11 ++ [Blbi11] := rfl
private theorem Blbs12 : Blbp13 = Blbp12 ++ [Blbi12] := rfl
private theorem Blbs13 : Blbp14 = Blbp13 ++ [Blbi13] := rfl
private theorem Blbs14 : Blbp15 = Blbp14 ++ [Blbi14] := rfl
private theorem Blbs15 : Blbp16 = Blbp15 ++ [Blbi15] := rfl

private theorem Blbfull : lbBlock = Blbp16 := rfl

private theorem Blbg0_1 : Blbp1 = Blbp0 ++ [Blbi0] := rfl
private theorem Blbg0_2 : Blbp2 = Blbp0 ++ [Blbi0, Blbi1] := rfl
private theorem Blbg0_4 : Blbp4 = Blbp0 ++ [Blbi0, Blbi1, Blbi2, Blbi3] := rfl
private theorem Blbg0_5 : Blbp5 = Blbp0 ++ [Blbi0, Blbi1, Blbi2, Blbi3, Blbi4] := rfl
private theorem Blbg0_6 : Blbp6 = Blbp0 ++ [Blbi0, Blbi1, Blbi2, Blbi3, Blbi4, Blbi5] := rfl
private theorem Blbg1_3 : Blbp3 = Blbp1 ++ [Blbi1, Blbi2] := rfl
private theorem Blbg1_7 : Blbp7 = Blbp1 ++ [Blbi1, Blbi2, Blbi3, Blbi4, Blbi5, Blbi6] := rfl
private theorem Blbg1_16 : Blbp16 = Blbp1 ++ [Blbi1, Blbi2, Blbi3, Blbi4, Blbi5, Blbi6, Blbi7, Blbi8, Blbi9, Blbi10, Blbi11, Blbi12, Blbi13, Blbi14, Blbi15] := rfl
private theorem Blbg5_8 : Blbp8 = Blbp5 ++ [Blbi5, Blbi6, Blbi7] := rfl
private theorem Blbg9_10 : Blbp10 = Blbp9 ++ [Blbi9] := rfl
private theorem Blbg9_12 : Blbp12 = Blbp9 ++ [Blbi9, Blbi10, Blbi11] := rfl
private theorem Blbg9_16 : Blbp16 = Blbp9 ++ [Blbi9, Blbi10, Blbi11, Blbi12, Blbi13, Blbi14, Blbi15] := rfl
private theorem Blbg10_11 : Blbp11 = Blbp10 ++ [Blbi10] := rfl
private theorem Blbg10_13 : Blbp13 = Blbp10 ++ [Blbi10, Blbi11, Blbi12] := rfl
private theorem Blbg10_16 : Blbp16 = Blbp10 ++ [Blbi10, Blbi11, Blbi12, Blbi13, Blbi14, Blbi15] := rfl
private theorem Blbg12_15 : Blbp15 = Blbp12 ++ [Blbi12, Blbi13, Blbi14] := rfl
private theorem Blbg12_16 : Blbp16 = Blbp12 ++ [Blbi12, Blbi13, Blbi14, Blbi15] := rfl
private theorem Blbg13_14 : Blbp14 = Blbp13 ++ [Blbi13] := rfl
private theorem Blbg14_16 : Blbp16 = Blbp14 ++ [Blbi14, Blbi15] := rfl
private theorem Blbg15_16 : Blbp16 = Blbp15 ++ [Blbi15] := rfl

/-! ### `starBlock` -/

private def Bstri0 : Instr := .binop rSt .add (.reg rAcc) (.reg rAbsN)
private def Bstri1 : Instr := .binop rSt .add (.reg rSt) (.reg rN)

private def Bstrp0 : List Instr := []
private def Bstrp1 : List Instr := [Bstri0]
private def Bstrp2 : List Instr := [Bstri0, Bstri1]

private theorem Bstrs0 : Bstrp1 = Bstrp0 ++ [Bstri0] := rfl
private theorem Bstrs1 : Bstrp2 = Bstrp1 ++ [Bstri1] := rfl

private theorem Bstrfull : starBlock = Bstrp2 := rfl

private theorem Bstrg0_1 : Bstrp1 = Bstrp0 ++ [Bstri0] := rfl


/-! ## The named outputs

One definition per quantity the six blocks produce, so that no value theorem's
statement is nested more than three deep and `msRound` can be written in the
same vocabulary.
-/

/-- The Möbius half of a packed cell, biased to `{0,1,2}`. -/
def semMu1 (v : Nat) : Nat := v >>> 52
/-- The `|L|` half of a packed cell. -/
def semAbs (v : Nat) : Nat := MS v ((semMu1 v <<< 52) % M)
/-- `termBlock`'s new partial sum. -/
def semAcc (acc ab q sq w : Nat) : Nat :=
  MA acc (MMul ((MS (MA (MA ab q) sq) 1) / sq) w)
/-- `latchBlock`'s carried `μ(q) + 1`. -/
def semMuQ (qg muQ mu1 : Nat) : Nat := MA (MMul (MS 1 qg) muQ) (MMul qg mu1)
/-- The squarefulness test `p ∣ q`. -/
def semSqdiv (qn p : Nat) : Nat := bitOf (qn % p = 0)
/-- `muBlock`'s `μ(n) + 1`. -/
def semMun (qn p muQ : Nat) : Nat :=
  MA (semSqdiv qn p) (MMul (MS 2 muQ) (MS 1 (semSqdiv qn p)))
/-- `⌊2⁴⁸/n⌋`. -/
def semDn (n : Nat) : Nat := fpDlit / n
/-- `lbBlock`'s advanced biased accumulator. -/
def semLb (lb mun cc n : Nat) : Nat :=
  MS (MA lb (MMul (MMul (bitOf (mun = 2)) cc) (semDn n)))
    (MMul (MMul (bitOf (mun = 0)) cc) (semDn n))
/-- The sign test on the biased accumulator. -/
def semBge (lb1 : Nat) : Nat := bitOf (bias ≤ lb1)
/-- `|L(n)|`, read off the biased accumulator. -/
def semAbsN (lb1 : Nat) : Nat :=
  MA (MMul (MS lb1 bias) (semBge lb1)) (MMul (MS bias lb1) (MS 1 (semBge lb1)))
/-- `star(n) = acc + |L(n)| + n`. -/
def semStar (acc absN n : Nat) : Nat := MA (MA acc absN) n

/-! ## The value theorems -/

/-- **`unpackBlock`**: the packed cell, split. -/
theorem unpackBlock_vals (k : Nat) (u : RegState) (hV : u rV < M) :
    srun k u unpackBlock rMu1 = semMu1 (u rV) ∧
      srun k u unpackBlock rAbs = semAbs (u rV) := by
  have hV0 : srun k u Bunpp0 rV = u rV := rfl
  have hMu1 : srun k u Bunpp1 rMu1 = semMu1 (u rV) :=
    step_write Bunps0 hV0 (denoteOperand_lit_of_lt k _ (show (52:Nat) < M by decide))
      (dop_lshr hV)
  have hT1 : srun k u Bunpp2 rT1 = (semMu1 (u rV) <<< 52) % M :=
    step_write Bunps1 hMu1 (denoteOperand_lit_of_lt k _ (show (52:Nat) < M by decide))
      (dop_shl _ _)
  have hV2 : srun k u Bunpp2 rV = u rV := run_frame Bunpg0_2 (by rfl) hV0
  have hAbs : srun k u Bunpp3 rAbs = semAbs (u rV) :=
    step_write Bunps2 hV2 hT1 (dop_sub _ _)
  exact ⟨run_frame (Bunpfull.trans Bunpg1_3) (by rfl) hMu1,
    run_frame Bunpfull (by rfl) hAbs⟩

theorem unpackBlock_defined (k : Nat) (u : RegState) :
    SAllDefined k u unpackBlock := sAllDefined_of_noDiv k _ _ (by rfl)

/-- **`termBlock`**: one `w`-term added to the partial sum. -/
theorem termBlock_vals (k : Nat) (u : RegState) (hSq : u rSq ≠ 0) :
    srun k u termBlock rAcc =
      semAcc (u rAcc) (u rAbs) (u rQq) (u rSq) (u rW) := by
  have hAbs0 : srun k u Btrmp0 rAbs = u rAbs := rfl
  have hQq0 : srun k u Btrmp0 rQq = u rQq := rfl
  have hSq0 : srun k u Btrmp0 rSq = u rSq := rfl
  have hW0 : srun k u Btrmp0 rW = u rW := rfl
  have hAcc0 : srun k u Btrmp0 rAcc = u rAcc := rfl
  have h1 : srun k u Btrmp1 rT1 = MA (u rAbs) (u rQq) :=
    step_write Btrms0 hAbs0 hQq0 (dop_add _ _)
  have hSq1 : srun k u Btrmp1 rSq = u rSq := run_frame Btrmg0_1 (by rfl) hSq0
  have h2 : srun k u Btrmp2 rT1 = MA (MA (u rAbs) (u rQq)) (u rSq) :=
    step_write Btrms1 h1 hSq1 (dop_add _ _)
  have h3 : srun k u Btrmp3 rT1 = MS (MA (MA (u rAbs) (u rQq)) (u rSq)) 1 :=
    step_write Btrms2 h2 (denoteOperand_lit_of_lt k _ one_lt_M) (dop_sub _ _)
  have hSq3 : srun k u Btrmp3 rSq = u rSq := run_frame Btrmg0_3 (by rfl) hSq0
  have h4 : srun k u Btrmp4 rT1 =
      MS (MA (MA (u rAbs) (u rQq)) (u rSq)) 1 / u rSq :=
    step_write Btrms3 h3 hSq3 (dop_udiv hSq (MS_lt _ _))
  have hW4 : srun k u Btrmp4 rW = u rW := run_frame Btrmg0_4 (by rfl) hW0
  have h5 : srun k u Btrmp5 rT1 =
      MMul (MS (MA (MA (u rAbs) (u rQq)) (u rSq)) 1 / u rSq) (u rW) :=
    step_write Btrms4 h4 hW4 (dop_mul _ _)
  have hAcc5 : srun k u Btrmp5 rAcc = u rAcc := run_frame Btrmg0_5 (by rfl) hAcc0
  have h6 : srun k u Btrmp6 rAcc =
      semAcc (u rAcc) (u rAbs) (u rQq) (u rSq) (u rW) :=
    step_write Btrms5 hAcc5 h5 (dop_add _ _)
  exact run_frame Btrmfull (by rfl) h6

theorem termBlock_defined (k : Nat) (u : RegState) (hSq : u rSq ≠ 0) :
    SAllDefined k u termBlock := by
  have hSq3 : srun k u Btrmp3 rSq = u rSq :=
    run_frame Btrmg0_3 (by rfl) rfl
  show SAllDefined k u (Btrmp3 ++ Btrmi3 :: [Btrmi4, Btrmi5])
  refine sAllDefined_stage (by rfl)
    (sDefined_udiv (fun h => hSq (hSq3.symm.trans h))) ?_
  exact sAllDefined_of_noDiv k _ _ (by rfl)

/-- **`latchBlock`**: `μ(q)+1` latched at the Möbius round. -/
theorem latchBlock_vals (k : Nat) (u : RegState) :
    srun k u latchBlock rMuQ = semMuQ (u rQg) (u rMuQ) (u rMu1) := by
  have hQg0 : srun k u Blatp0 rQg = u rQg := rfl
  have hMuQ0 : srun k u Blatp0 rMuQ = u rMuQ := rfl
  have hMu10 : srun k u Blatp0 rMu1 = u rMu1 := rfl
  have h1 : srun k u Blatp1 rT1 = MS 1 (u rQg) :=
    step_write Blats0 (denoteOperand_lit_of_lt k _ one_lt_M) hQg0 (dop_sub _ _)
  have hMuQ1 : srun k u Blatp1 rMuQ = u rMuQ := run_frame Blatg0_1 (by rfl) hMuQ0
  have h2 : srun k u Blatp2 rT1 = MMul (MS 1 (u rQg)) (u rMuQ) :=
    step_write Blats1 h1 hMuQ1 (dop_mul _ _)
  have hQg2 : srun k u Blatp2 rQg = u rQg := run_frame Blatg0_2 (by rfl) hQg0
  have hMu12 : srun k u Blatp2 rMu1 = u rMu1 := run_frame Blatg0_2 (by rfl) hMu10
  have h3 : srun k u Blatp3 rT2 = MMul (u rQg) (u rMu1) :=
    step_write Blats2 hQg2 hMu12 (dop_mul _ _)
  have hT1_3 : srun k u Blatp3 rT1 = MMul (MS 1 (u rQg)) (u rMuQ) :=
    run_frame Blatg2_3 (by rfl) h2
  have h4 : srun k u Blatp4 rMuQ = semMuQ (u rQg) (u rMuQ) (u rMu1) :=
    step_write Blats3 hT1_3 h3 (dop_add _ _)
  exact run_frame Blatfull (by rfl) h4

theorem latchBlock_defined (k : Nat) (u : RegState) :
    SAllDefined k u latchBlock := sAllDefined_of_noDiv k _ _ (by rfl)

/-- **`muBlock`**: `μ(n)+1` from `μ(q)+1` and the squarefulness test. -/
theorem muBlock_vals (k : Nat) (u : RegState) (hP : u rP ≠ 0) (hQ : u rQ < M) :
    srun k u muBlock rMun = semMun (u rQ) (u rP) (u rMuQ) := by
  have hQ0 : srun k u Bmup0 rQ = u rQ := rfl
  have hP0 : srun k u Bmup0 rP = u rP := rfl
  have hMuQ0 : srun k u Bmup0 rMuQ = u rMuQ := rfl
  have h1 : srun k u Bmup1 rT1 = u rQ % u rP :=
    step_write Bmus0 hQ0 hP0 (dop_urem hP hQ)
  have h2 : srun k u Bmup2 rT1 = semSqdiv (u rQ) (u rP) :=
    step_write Bmus1 h1 (denoteOperand_lit_of_lt k _ M_pos) (dop_eq _ _)
  have h3 : srun k u Bmup3 rT2 = MS 1 (semSqdiv (u rQ) (u rP)) :=
    step_write Bmus2 (denoteOperand_lit_of_lt k _ one_lt_M) h2 (dop_sub _ _)
  have hMuQ3 : srun k u Bmup3 rMuQ = u rMuQ := run_frame Bmug0_3 (by rfl) hMuQ0
  have h4 : srun k u Bmup4 rT3 = MS 2 (u rMuQ) :=
    step_write Bmus3 (denoteOperand_lit_of_lt k _ (show (2:Nat) < M by decide))
      hMuQ3 (dop_sub _ _)
  have hT2_4 : srun k u Bmup4 rT2 = MS 1 (semSqdiv (u rQ) (u rP)) :=
    run_frame Bmug3_4 (by rfl) h3
  have h5 : srun k u Bmup5 rT3 =
      MMul (MS 2 (u rMuQ)) (MS 1 (semSqdiv (u rQ) (u rP))) :=
    step_write Bmus4 h4 hT2_4 (dop_mul _ _)
  have hT1_5 : srun k u Bmup5 rT1 = semSqdiv (u rQ) (u rP) :=
    run_frame Bmug2_5 (by rfl) h2
  have h6 : srun k u Bmup6 rMun = semMun (u rQ) (u rP) (u rMuQ) :=
    step_write Bmus5 hT1_5 h5 (dop_add _ _)
  exact run_frame Bmufull (by rfl) h6

theorem muBlock_defined (k : Nat) (u : RegState) (hP : u rP ≠ 0) :
    SAllDefined k u muBlock := by
  refine sAllDefined_cons (sDefined_urem hP) ?_
  exact sAllDefined_of_noDiv k _ _ (by rfl)

/-- **`lbBlock`**: the little-Mertens accumulator advances, and its magnitude
is read off. -/
theorem lbBlock_vals (k : Nat) (u : RegState) (hN : u rN ≠ 0) :
    srun k u lbBlock rLb = semLb (u rLb) (u rMun) (u rC) (u rN) ∧
      srun k u lbBlock rAbsN = semAbsN (semLb (u rLb) (u rMun) (u rC) (u rN)) := by
  have hN0 : srun k u Blbp0 rN = u rN := rfl
  have hMun0 : srun k u Blbp0 rMun = u rMun := rfl
  have hC0 : srun k u Blbp0 rC = u rC := rfl
  have hLb0 : srun k u Blbp0 rLb = u rLb := rfl
  have hDn1 : srun k u Blbp1 rDn = semDn (u rN) :=
    step_write Blbs0 (denoteOperand_lit_of_lt k _ (show fpDlit < M by decide)) hN0
      (dop_udiv hN (show fpDlit < M by decide))
  have hMun1 : srun k u Blbp1 rMun = u rMun := run_frame Blbg0_1 (by rfl) hMun0
  have h2 : srun k u Blbp2 rT1 = bitOf (u rMun = 2) :=
    step_write Blbs1 hMun1
      (denoteOperand_lit_of_lt k _ (show (2:Nat) < M by decide)) (dop_eq _ _)
  have hC2 : srun k u Blbp2 rC = u rC := run_frame Blbg0_2 (by rfl) hC0
  have h3 : srun k u Blbp3 rT1 = MMul (bitOf (u rMun = 2)) (u rC) :=
    step_write Blbs2 h2 hC2 (dop_mul _ _)
  have hDn3 : srun k u Blbp3 rDn = semDn (u rN) := run_frame Blbg1_3 (by rfl) hDn1
  have h4 : srun k u Blbp4 rT1 =
      MMul (MMul (bitOf (u rMun = 2)) (u rC)) (semDn (u rN)) :=
    step_write Blbs3 h3 hDn3 (dop_mul _ _)
  have hLb4 : srun k u Blbp4 rLb = u rLb := run_frame Blbg0_4 (by rfl) hLb0
  have h5 : srun k u Blbp5 rLb =
      MA (u rLb) (MMul (MMul (bitOf (u rMun = 2)) (u rC)) (semDn (u rN))) :=
    step_write Blbs4 hLb4 h4 (dop_add _ _)
  have hMun5 : srun k u Blbp5 rMun = u rMun := run_frame Blbg0_5 (by rfl) hMun0
  have h6 : srun k u Blbp6 rT2 = bitOf (u rMun = 0) :=
    step_write Blbs5 hMun5
      (denoteOperand_lit_of_lt k _ M_pos) (dop_eq _ _)
  have hC6 : srun k u Blbp6 rC = u rC := run_frame Blbg0_6 (by rfl) hC0
  have h7 : srun k u Blbp7 rT2 = MMul (bitOf (u rMun = 0)) (u rC) :=
    step_write Blbs6 h6 hC6 (dop_mul _ _)
  have hDn7 : srun k u Blbp7 rDn = semDn (u rN) := run_frame Blbg1_7 (by rfl) hDn1
  have h8 : srun k u Blbp8 rT2 =
      MMul (MMul (bitOf (u rMun = 0)) (u rC)) (semDn (u rN)) :=
    step_write Blbs7 h7 hDn7 (dop_mul _ _)
  have hLb8 : srun k u Blbp8 rLb =
      MA (u rLb) (MMul (MMul (bitOf (u rMun = 2)) (u rC)) (semDn (u rN))) :=
    run_frame Blbg5_8 (by rfl) h5
  have h9 : srun k u Blbp9 rLb = semLb (u rLb) (u rMun) (u rC) (u rN) :=
    step_write Blbs8 hLb8 h8 (dop_sub _ _)
  have h10 : srun k u Blbp10 rT1 =
      semBge (semLb (u rLb) (u rMun) (u rC) (u rN)) :=
    step_write Blbs9 h9 (denoteOperand_lit_of_lt k _ (show bias < M by decide))
      (dop_ge _ _)
  have hLb10 : srun k u Blbp10 rLb = semLb (u rLb) (u rMun) (u rC) (u rN) :=
    run_frame Blbg9_10 (by rfl) h9
  have h11 : srun k u Blbp11 rT2 =
      MS (semLb (u rLb) (u rMun) (u rC) (u rN)) bias :=
    step_write Blbs10 hLb10
      (denoteOperand_lit_of_lt k _ (show bias < M by decide)) (dop_sub _ _)
  have hT1_11 : srun k u Blbp11 rT1 =
      semBge (semLb (u rLb) (u rMun) (u rC) (u rN)) :=
    run_frame Blbg10_11 (by rfl) h10
  have h12 : srun k u Blbp12 rT2 =
      MMul (MS (semLb (u rLb) (u rMun) (u rC) (u rN)) bias)
        (semBge (semLb (u rLb) (u rMun) (u rC) (u rN))) :=
    step_write Blbs11 h11 hT1_11 (dop_mul _ _)
  have hLb12 : srun k u Blbp12 rLb = semLb (u rLb) (u rMun) (u rC) (u rN) :=
    run_frame Blbg9_12 (by rfl) h9
  have h13 : srun k u Blbp13 rT3 =
      MS bias (semLb (u rLb) (u rMun) (u rC) (u rN)) :=
    step_write Blbs12 (denoteOperand_lit_of_lt k _ (show bias < M by decide))
      hLb12 (dop_sub _ _)
  have hT1_13 : srun k u Blbp13 rT1 =
      semBge (semLb (u rLb) (u rMun) (u rC) (u rN)) :=
    run_frame Blbg10_13 (by rfl) h10
  have h14 : srun k u Blbp14 rG =
      MS 1 (semBge (semLb (u rLb) (u rMun) (u rC) (u rN))) :=
    step_write Blbs13 (denoteOperand_lit_of_lt k _ one_lt_M)
      hT1_13 (dop_sub _ _)
  have hT3_14 : srun k u Blbp14 rT3 =
      MS bias (semLb (u rLb) (u rMun) (u rC) (u rN)) :=
    run_frame Blbg13_14 (by rfl) h13
  have h15 : srun k u Blbp15 rT3 =
      MMul (MS bias (semLb (u rLb) (u rMun) (u rC) (u rN)))
        (MS 1 (semBge (semLb (u rLb) (u rMun) (u rC) (u rN)))) :=
    step_write Blbs14 hT3_14 h14 (dop_mul _ _)
  have hT2_15 : srun k u Blbp15 rT2 =
      MMul (MS (semLb (u rLb) (u rMun) (u rC) (u rN)) bias)
        (semBge (semLb (u rLb) (u rMun) (u rC) (u rN))) :=
    run_frame Blbg12_15 (by rfl) h12
  have h16 : srun k u Blbp16 rAbsN =
      semAbsN (semLb (u rLb) (u rMun) (u rC) (u rN)) :=
    step_write Blbs15 hT2_15 h15 (dop_add _ _)
  exact ⟨run_frame (Blbfull.trans Blbg9_16) (by rfl) h9,
    run_frame Blbfull (by rfl) h16⟩

theorem lbBlock_defined (k : Nat) (u : RegState) (hN : u rN ≠ 0) :
    SAllDefined k u lbBlock := by
  refine sAllDefined_cons (sDefined_udiv hN) ?_
  exact sAllDefined_of_noDiv k _ _ (by rfl)

/-- **`starBlock`**: the `w = 1` term needs no cell. -/
theorem starBlock_vals (k : Nat) (u : RegState) :
    srun k u starBlock rSt = semStar (u rAcc) (u rAbsN) (u rN) := by
  have hAcc0 : srun k u Bstrp0 rAcc = u rAcc := rfl
  have hAbsN0 : srun k u Bstrp0 rAbsN = u rAbsN := rfl
  have hN0 : srun k u Bstrp0 rN = u rN := rfl
  have h1 : srun k u Bstrp1 rSt = MA (u rAcc) (u rAbsN) :=
    step_write Bstrs0 hAcc0 hAbsN0 (dop_add _ _)
  have hN1 : srun k u Bstrp1 rN = u rN := run_frame Bstrg0_1 (by rfl) hN0
  have h2 : srun k u Bstrp2 rSt = semStar (u rAcc) (u rAbsN) (u rN) :=
    step_write Bstrs1 h1 hN1 (dop_add _ _)
  exact run_frame Bstrfull (by rfl) h2

theorem starBlock_defined (k : Nat) (u : RegState) :
    SAllDefined k u starBlock := sAllDefined_of_noDiv k _ _ (by rfl)

end LeanCompCert.Ports.RamareMStar140M
