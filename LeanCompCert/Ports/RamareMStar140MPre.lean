import LeanCompCert.Ports.RamareMStar140MCore

/-!
# The pre-load stage of the `m★` body

`msPre c` is `decodeBlock ++ scanBlock ++ selectBlock ++ indexBlock` — thirty-six
instructions ending in the load index.  Each block gets

* a **value** theorem, whose right-hand side is written in `MA`/`MS`/`MMul`/
  `bitOf` — the machine's `denoteOp` on the nose, and the vocabulary `msRef` is
  written in, so no wrap-freedom side condition has to be proved to state one;
* a **definedness** theorem for its divisions.

The instruction names, prefix lists and split equations below are a `rfl`
regrouping of the very same lists; `decodeBlock`, `scanBlock`, `selectBlock`
and `indexBlock` are unchanged, so the emitted C is unchanged.
-/

namespace LeanCompCert.Ports.RamareMStar140M

open LeanCompCert
open LeanCompCert.Verified
open LeanCompCert.Verified.Reflect
open LeanCompCert.Verified.BlockDefined
open LeanCompCert.Verified.RegFrame
open LeanCompCert.Verified.InstrBlock (srun sval sdest SDefined SAllDefined NoDivI)

/-! ### `decodeBlock` -/

private def Bdeci0 (c : Cfg) : Instr := .binop rR .urem .idx (.lit c.B)
private def Bdeci1 (c : Cfg) : Instr := .binop rN .udiv .idx (.lit c.B)
private def Bdeci2 (c : Cfg) : Instr := .binop rN .add (.lit c.n0) (.reg rN)
private def Bdeci3 : Instr := .binop rD .add (.lit 2) (.reg rR)
private def Bdeci4 : Instr := .binop rSq .mul (.reg rD) (.reg rD)
private def Bdeci5 (c : Cfg) : Instr := .binop rW .lt (.reg rR) (.lit (c.B - 2))
private def Bdeci6 (c : Cfg) : Instr := .binop rQg .eq (.reg rR) (.lit (c.B - 2))
private def Bdeci7 (c : Cfg) : Instr := .binop rC .eq (.reg rR) (.lit (c.B - 1))
private def Bdeci8 : Instr := .binop rZ .eq (.reg rR) (.lit 0)
private def Bdeci9 : Instr := .binop rT1 .sub (.lit 1) (.reg rZ)
private def Bdeci10 : Instr := .binop rS .mul (.reg rS) (.reg rT1)
private def Bdeci11 : Instr := .binop rAcc .mul (.reg rAcc) (.reg rT1)

private def Bdecp0 (c : Cfg) : List Instr := []
private def Bdecp1 (c : Cfg) : List Instr := [Bdeci0 c]
private def Bdecp2 (c : Cfg) : List Instr := [Bdeci0 c, Bdeci1 c]
private def Bdecp3 (c : Cfg) : List Instr := [Bdeci0 c, Bdeci1 c, Bdeci2 c]
private def Bdecp4 (c : Cfg) : List Instr := [Bdeci0 c, Bdeci1 c, Bdeci2 c, Bdeci3]
private def Bdecp5 (c : Cfg) : List Instr := [Bdeci0 c, Bdeci1 c, Bdeci2 c, Bdeci3, Bdeci4]
private def Bdecp6 (c : Cfg) : List Instr := [Bdeci0 c, Bdeci1 c, Bdeci2 c, Bdeci3, Bdeci4, Bdeci5 c]
private def Bdecp7 (c : Cfg) : List Instr := [Bdeci0 c, Bdeci1 c, Bdeci2 c, Bdeci3, Bdeci4, Bdeci5 c, Bdeci6 c]
private def Bdecp8 (c : Cfg) : List Instr := [Bdeci0 c, Bdeci1 c, Bdeci2 c, Bdeci3, Bdeci4, Bdeci5 c, Bdeci6 c, Bdeci7 c]
private def Bdecp9 (c : Cfg) : List Instr := [Bdeci0 c, Bdeci1 c, Bdeci2 c, Bdeci3, Bdeci4, Bdeci5 c, Bdeci6 c, Bdeci7 c, Bdeci8]
private def Bdecp10 (c : Cfg) : List Instr := [Bdeci0 c, Bdeci1 c, Bdeci2 c, Bdeci3, Bdeci4, Bdeci5 c, Bdeci6 c, Bdeci7 c, Bdeci8, Bdeci9]
private def Bdecp11 (c : Cfg) : List Instr := [Bdeci0 c, Bdeci1 c, Bdeci2 c, Bdeci3, Bdeci4, Bdeci5 c, Bdeci6 c, Bdeci7 c, Bdeci8, Bdeci9, Bdeci10]
private def Bdecp12 (c : Cfg) : List Instr := [Bdeci0 c, Bdeci1 c, Bdeci2 c, Bdeci3, Bdeci4, Bdeci5 c, Bdeci6 c, Bdeci7 c, Bdeci8, Bdeci9, Bdeci10, Bdeci11]

private theorem Bdecs0 (c : Cfg) : Bdecp1 c = Bdecp0 c ++ [Bdeci0 c] := rfl
private theorem Bdecs1 (c : Cfg) : Bdecp2 c = Bdecp1 c ++ [Bdeci1 c] := rfl
private theorem Bdecs2 (c : Cfg) : Bdecp3 c = Bdecp2 c ++ [Bdeci2 c] := rfl
private theorem Bdecs3 (c : Cfg) : Bdecp4 c = Bdecp3 c ++ [Bdeci3] := rfl
private theorem Bdecs4 (c : Cfg) : Bdecp5 c = Bdecp4 c ++ [Bdeci4] := rfl
private theorem Bdecs5 (c : Cfg) : Bdecp6 c = Bdecp5 c ++ [Bdeci5 c] := rfl
private theorem Bdecs6 (c : Cfg) : Bdecp7 c = Bdecp6 c ++ [Bdeci6 c] := rfl
private theorem Bdecs7 (c : Cfg) : Bdecp8 c = Bdecp7 c ++ [Bdeci7 c] := rfl
private theorem Bdecs8 (c : Cfg) : Bdecp9 c = Bdecp8 c ++ [Bdeci8] := rfl
private theorem Bdecs9 (c : Cfg) : Bdecp10 c = Bdecp9 c ++ [Bdeci9] := rfl
private theorem Bdecs10 (c : Cfg) : Bdecp11 c = Bdecp10 c ++ [Bdeci10] := rfl
private theorem Bdecs11 (c : Cfg) : Bdecp12 c = Bdecp11 c ++ [Bdeci11] := rfl

private theorem Bdecfull (c : Cfg) : decodeBlock c = Bdecp12 c := rfl

private theorem Bdecg0_10 (c : Cfg) : Bdecp10 c = Bdecp0 c ++ [Bdeci0 c, Bdeci1 c, Bdeci2 c, Bdeci3, Bdeci4, Bdeci5 c, Bdeci6 c, Bdeci7 c, Bdeci8, Bdeci9] := rfl
private theorem Bdecg0_11 (c : Cfg) : Bdecp11 c = Bdecp0 c ++ [Bdeci0 c, Bdeci1 c, Bdeci2 c, Bdeci3, Bdeci4, Bdeci5 c, Bdeci6 c, Bdeci7 c, Bdeci8, Bdeci9, Bdeci10] := rfl
private theorem Bdecg1_3 (c : Cfg) : Bdecp3 c = Bdecp1 c ++ [Bdeci1 c, Bdeci2 c] := rfl
private theorem Bdecg1_5 (c : Cfg) : Bdecp5 c = Bdecp1 c ++ [Bdeci1 c, Bdeci2 c, Bdeci3, Bdeci4] := rfl
private theorem Bdecg1_6 (c : Cfg) : Bdecp6 c = Bdecp1 c ++ [Bdeci1 c, Bdeci2 c, Bdeci3, Bdeci4, Bdeci5 c] := rfl
private theorem Bdecg1_7 (c : Cfg) : Bdecp7 c = Bdecp1 c ++ [Bdeci1 c, Bdeci2 c, Bdeci3, Bdeci4, Bdeci5 c, Bdeci6 c] := rfl
private theorem Bdecg1_8 (c : Cfg) : Bdecp8 c = Bdecp1 c ++ [Bdeci1 c, Bdeci2 c, Bdeci3, Bdeci4, Bdeci5 c, Bdeci6 c, Bdeci7 c] := rfl
private theorem Bdecg1_12 (c : Cfg) : Bdecp12 c = Bdecp1 c ++ [Bdeci1 c, Bdeci2 c, Bdeci3, Bdeci4, Bdeci5 c, Bdeci6 c, Bdeci7 c, Bdeci8, Bdeci9, Bdeci10, Bdeci11] := rfl
private theorem Bdecg3_12 (c : Cfg) : Bdecp12 c = Bdecp3 c ++ [Bdeci3, Bdeci4, Bdeci5 c, Bdeci6 c, Bdeci7 c, Bdeci8, Bdeci9, Bdeci10, Bdeci11] := rfl
private theorem Bdecg4_12 (c : Cfg) : Bdecp12 c = Bdecp4 c ++ [Bdeci4, Bdeci5 c, Bdeci6 c, Bdeci7 c, Bdeci8, Bdeci9, Bdeci10, Bdeci11] := rfl
private theorem Bdecg5_12 (c : Cfg) : Bdecp12 c = Bdecp5 c ++ [Bdeci5 c, Bdeci6 c, Bdeci7 c, Bdeci8, Bdeci9, Bdeci10, Bdeci11] := rfl
private theorem Bdecg6_12 (c : Cfg) : Bdecp12 c = Bdecp6 c ++ [Bdeci6 c, Bdeci7 c, Bdeci8, Bdeci9, Bdeci10, Bdeci11] := rfl
private theorem Bdecg7_12 (c : Cfg) : Bdecp12 c = Bdecp7 c ++ [Bdeci7 c, Bdeci8, Bdeci9, Bdeci10, Bdeci11] := rfl
private theorem Bdecg8_12 (c : Cfg) : Bdecp12 c = Bdecp8 c ++ [Bdeci8, Bdeci9, Bdeci10, Bdeci11] := rfl
private theorem Bdecg9_12 (c : Cfg) : Bdecp12 c = Bdecp9 c ++ [Bdeci9, Bdeci10, Bdeci11] := rfl
private theorem Bdecg10_11 (c : Cfg) : Bdecp11 c = Bdecp10 c ++ [Bdeci10] := rfl
private theorem Bdecg10_12 (c : Cfg) : Bdecp12 c = Bdecp10 c ++ [Bdeci10, Bdeci11] := rfl
private theorem Bdecg11_12 (c : Cfg) : Bdecp12 c = Bdecp11 c ++ [Bdeci11] := rfl

/-! ### `scanBlock` -/

private def Bscni0 : Instr := .binop rG .eq (.reg rS) (.lit 0)
private def Bscni1 : Instr := .binop rT1 .le (.reg rSq) (.reg rN)
private def Bscni2 : Instr := .binop rG .mul (.reg rG) (.reg rT1)
private def Bscni3 : Instr := .binop rT2 .urem (.reg rN) (.reg rD)
private def Bscni4 : Instr := .binop rT2 .eq (.reg rT2) (.lit 0)
private def Bscni5 : Instr := .binop rG .mul (.reg rG) (.reg rT2)
private def Bscni6 : Instr := .binop rG .mul (.reg rG) (.reg rW)
private def Bscni7 : Instr := .binop rT1 .sub (.lit 1) (.reg rG)
private def Bscni8 : Instr := .binop rT1 .mul (.reg rT1) (.reg rS)
private def Bscni9 : Instr := .binop rT2 .mul (.reg rG) (.reg rD)
private def Bscni10 : Instr := .binop rS .add (.reg rT1) (.reg rT2)

private def Bscnp0 : List Instr := []
private def Bscnp1 : List Instr := [Bscni0]
private def Bscnp2 : List Instr := [Bscni0, Bscni1]
private def Bscnp3 : List Instr := [Bscni0, Bscni1, Bscni2]
private def Bscnp4 : List Instr := [Bscni0, Bscni1, Bscni2, Bscni3]
private def Bscnp5 : List Instr := [Bscni0, Bscni1, Bscni2, Bscni3, Bscni4]
private def Bscnp6 : List Instr := [Bscni0, Bscni1, Bscni2, Bscni3, Bscni4, Bscni5]
private def Bscnp7 : List Instr := [Bscni0, Bscni1, Bscni2, Bscni3, Bscni4, Bscni5, Bscni6]
private def Bscnp8 : List Instr := [Bscni0, Bscni1, Bscni2, Bscni3, Bscni4, Bscni5, Bscni6, Bscni7]
private def Bscnp9 : List Instr := [Bscni0, Bscni1, Bscni2, Bscni3, Bscni4, Bscni5, Bscni6, Bscni7, Bscni8]
private def Bscnp10 : List Instr := [Bscni0, Bscni1, Bscni2, Bscni3, Bscni4, Bscni5, Bscni6, Bscni7, Bscni8, Bscni9]
private def Bscnp11 : List Instr := [Bscni0, Bscni1, Bscni2, Bscni3, Bscni4, Bscni5, Bscni6, Bscni7, Bscni8, Bscni9, Bscni10]

private theorem Bscns0 : Bscnp1 = Bscnp0 ++ [Bscni0] := rfl
private theorem Bscns1 : Bscnp2 = Bscnp1 ++ [Bscni1] := rfl
private theorem Bscns2 : Bscnp3 = Bscnp2 ++ [Bscni2] := rfl
private theorem Bscns3 : Bscnp4 = Bscnp3 ++ [Bscni3] := rfl
private theorem Bscns4 : Bscnp5 = Bscnp4 ++ [Bscni4] := rfl
private theorem Bscns5 : Bscnp6 = Bscnp5 ++ [Bscni5] := rfl
private theorem Bscns6 : Bscnp7 = Bscnp6 ++ [Bscni6] := rfl
private theorem Bscns7 : Bscnp8 = Bscnp7 ++ [Bscni7] := rfl
private theorem Bscns8 : Bscnp9 = Bscnp8 ++ [Bscni8] := rfl
private theorem Bscns9 : Bscnp10 = Bscnp9 ++ [Bscni9] := rfl
private theorem Bscns10 : Bscnp11 = Bscnp10 ++ [Bscni10] := rfl

private theorem Bscnfull : scanBlock = Bscnp11 := rfl

private theorem Bscng0_1 : Bscnp1 = Bscnp0 ++ [Bscni0] := rfl
private theorem Bscng0_3 : Bscnp3 = Bscnp0 ++ [Bscni0, Bscni1, Bscni2] := rfl
private theorem Bscng0_6 : Bscnp6 = Bscnp0 ++ [Bscni0, Bscni1, Bscni2, Bscni3, Bscni4, Bscni5] := rfl
private theorem Bscng0_8 : Bscnp8 = Bscnp0 ++ [Bscni0, Bscni1, Bscni2, Bscni3, Bscni4, Bscni5, Bscni6, Bscni7] := rfl
private theorem Bscng0_9 : Bscnp9 = Bscnp0 ++ [Bscni0, Bscni1, Bscni2, Bscni3, Bscni4, Bscni5, Bscni6, Bscni7, Bscni8] := rfl
private theorem Bscng1_2 : Bscnp2 = Bscnp1 ++ [Bscni1] := rfl
private theorem Bscng3_5 : Bscnp5 = Bscnp3 ++ [Bscni3, Bscni4] := rfl
private theorem Bscng7_9 : Bscnp9 = Bscnp7 ++ [Bscni7, Bscni8] := rfl
private theorem Bscng7_11 : Bscnp11 = Bscnp7 ++ [Bscni7, Bscni8, Bscni9, Bscni10] := rfl
private theorem Bscng9_10 : Bscnp10 = Bscnp9 ++ [Bscni9] := rfl
private theorem Bscng9_11 : Bscnp11 = Bscnp9 ++ [Bscni9, Bscni10] := rfl
private theorem Bscng10_11 : Bscnp11 = Bscnp10 ++ [Bscni10] := rfl

/-! ### `selectBlock` -/

private def Bseli0 : Instr := .binop rT1 .eq (.reg rS) (.lit 0)
private def Bseli1 : Instr := .binop rT2 .sub (.lit 1) (.reg rT1)
private def Bseli2 : Instr := .binop rT2 .mul (.reg rT2) (.reg rS)
private def Bseli3 : Instr := .binop rT3 .mul (.reg rT1) (.reg rN)
private def Bseli4 : Instr := .binop rP .add (.reg rT3) (.reg rT2)
private def Bseli5 : Instr := .binop rQ .udiv (.reg rN) (.reg rP)

private def Bselp0 : List Instr := []
private def Bselp1 : List Instr := [Bseli0]
private def Bselp2 : List Instr := [Bseli0, Bseli1]
private def Bselp3 : List Instr := [Bseli0, Bseli1, Bseli2]
private def Bselp4 : List Instr := [Bseli0, Bseli1, Bseli2, Bseli3]
private def Bselp5 : List Instr := [Bseli0, Bseli1, Bseli2, Bseli3, Bseli4]
private def Bselp6 : List Instr := [Bseli0, Bseli1, Bseli2, Bseli3, Bseli4, Bseli5]

private theorem Bsels0 : Bselp1 = Bselp0 ++ [Bseli0] := rfl
private theorem Bsels1 : Bselp2 = Bselp1 ++ [Bseli1] := rfl
private theorem Bsels2 : Bselp3 = Bselp2 ++ [Bseli2] := rfl
private theorem Bsels3 : Bselp4 = Bselp3 ++ [Bseli3] := rfl
private theorem Bsels4 : Bselp5 = Bselp4 ++ [Bseli4] := rfl
private theorem Bsels5 : Bselp6 = Bselp5 ++ [Bseli5] := rfl

private theorem Bselfull : selectBlock = Bselp6 := rfl

private theorem Bselg0_2 : Bselp2 = Bselp0 ++ [Bseli0, Bseli1] := rfl
private theorem Bselg0_3 : Bselp3 = Bselp0 ++ [Bseli0, Bseli1, Bseli2] := rfl
private theorem Bselg0_5 : Bselp5 = Bselp0 ++ [Bseli0, Bseli1, Bseli2, Bseli3, Bseli4] := rfl
private theorem Bselg1_3 : Bselp3 = Bselp1 ++ [Bseli1, Bseli2] := rfl
private theorem Bselg1_6 : Bselp6 = Bselp1 ++ [Bseli1, Bseli2, Bseli3, Bseli4, Bseli5] := rfl
private theorem Bselg3_4 : Bselp4 = Bselp3 ++ [Bseli3] := rfl
private theorem Bselg3_6 : Bselp6 = Bselp3 ++ [Bseli3, Bseli4, Bseli5] := rfl
private theorem Bselg4_6 : Bselp6 = Bselp4 ++ [Bseli4, Bseli5] := rfl
private theorem Bselg5_6 : Bselp6 = Bselp5 ++ [Bseli5] := rfl

/-! ### `indexBlock` -/

private def Bidxi0 : Instr := .binop rQq .udiv (.reg rN) (.reg rSq)
private def Bidxi1 : Instr := .binop rI .mul (.reg rW) (.reg rQq)
private def Bidxi2 : Instr := .binop rT1 .mul (.reg rQg) (.reg rQ)
private def Bidxi3 : Instr := .binop rI .add (.reg rI) (.reg rT1)
private def Bidxi4 (c : Cfg) : Instr := .binop rT1 .add (.lit (c.limit + 1)) (.reg rIdx)
private def Bidxi5 : Instr := .binop rT1 .mul (.reg rC) (.reg rT1)
private def Bidxi6 : Instr := .binop rI .add (.reg rI) (.reg rT1)

private def Bidxp0 (c : Cfg) : List Instr := []
private def Bidxp1 (c : Cfg) : List Instr := [Bidxi0]
private def Bidxp2 (c : Cfg) : List Instr := [Bidxi0, Bidxi1]
private def Bidxp3 (c : Cfg) : List Instr := [Bidxi0, Bidxi1, Bidxi2]
private def Bidxp4 (c : Cfg) : List Instr := [Bidxi0, Bidxi1, Bidxi2, Bidxi3]
private def Bidxp5 (c : Cfg) : List Instr := [Bidxi0, Bidxi1, Bidxi2, Bidxi3, Bidxi4 c]
private def Bidxp6 (c : Cfg) : List Instr := [Bidxi0, Bidxi1, Bidxi2, Bidxi3, Bidxi4 c, Bidxi5]
private def Bidxp7 (c : Cfg) : List Instr := [Bidxi0, Bidxi1, Bidxi2, Bidxi3, Bidxi4 c, Bidxi5, Bidxi6]

private theorem Bidxs0 (c : Cfg) : Bidxp1 c = Bidxp0 c ++ [Bidxi0] := rfl
private theorem Bidxs1 (c : Cfg) : Bidxp2 c = Bidxp1 c ++ [Bidxi1] := rfl
private theorem Bidxs2 (c : Cfg) : Bidxp3 c = Bidxp2 c ++ [Bidxi2] := rfl
private theorem Bidxs3 (c : Cfg) : Bidxp4 c = Bidxp3 c ++ [Bidxi3] := rfl
private theorem Bidxs4 (c : Cfg) : Bidxp5 c = Bidxp4 c ++ [Bidxi4 c] := rfl
private theorem Bidxs5 (c : Cfg) : Bidxp6 c = Bidxp5 c ++ [Bidxi5] := rfl
private theorem Bidxs6 (c : Cfg) : Bidxp7 c = Bidxp6 c ++ [Bidxi6] := rfl

private theorem Bidxfull (c : Cfg) : indexBlock c = Bidxp7 c := rfl

private theorem Bidxg0_1 (c : Cfg) : Bidxp1 c = Bidxp0 c ++ [Bidxi0] := rfl
private theorem Bidxg0_2 (c : Cfg) : Bidxp2 c = Bidxp0 c ++ [Bidxi0, Bidxi1] := rfl
private theorem Bidxg0_4 (c : Cfg) : Bidxp4 c = Bidxp0 c ++ [Bidxi0, Bidxi1, Bidxi2, Bidxi3] := rfl
private theorem Bidxg0_5 (c : Cfg) : Bidxp5 c = Bidxp0 c ++ [Bidxi0, Bidxi1, Bidxi2, Bidxi3, Bidxi4 c] := rfl
private theorem Bidxg1_7 (c : Cfg) : Bidxp7 c = Bidxp1 c ++ [Bidxi1, Bidxi2, Bidxi3, Bidxi4 c, Bidxi5, Bidxi6] := rfl
private theorem Bidxg2_3 (c : Cfg) : Bidxp3 c = Bidxp2 c ++ [Bidxi2] := rfl
private theorem Bidxg4_6 (c : Cfg) : Bidxp6 c = Bidxp4 c ++ [Bidxi4 c, Bidxi5] := rfl
private theorem Bidxg6_7 (c : Cfg) : Bidxp7 c = Bidxp6 c ++ [Bidxi6] := rfl


/-! ## The named outputs -/

/-- The scan's gate: the round advances the trial scan exactly when the scan is
empty, `d² ≤ n`, `d ∣ n`, and this is a work round. -/
def semScanG (S sq n d w : Nat) : Nat :=
  MMul (bitOf ((S = 0 ∧ sq ≤ n) ∧ n % d = 0)) w

/-- The scan accumulator after one trial round. -/
def semScanS (S sq n d w : Nat) : Nat :=
  MA (MMul (MS 1 (semScanG S sq n d w)) S) (MMul (semScanG S sq n d w) d)

/-- The committed factor: the candidate itself when the scan is empty. -/
def semP (S n : Nat) : Nat :=
  MA (MMul (bitOf (S = 0)) n) (MMul (MS 1 (bitOf (S = 0))) S)

/-- The cofactor `n / p`. -/
def semQ (S n : Nat) : Nat := n / semP S n

/-- The load index: `⌊n/d²⌋` on a work round, `q` on the Möbius round, and the
log-constant cell on the commit round. -/
def semI (w qq qg q cc lim idx : Nat) : Nat :=
  MA (MA (MMul w qq) (MMul qg q)) (MMul cc (MA lim idx))

variable {c : Cfg}

/-! ## The decode -/

/-- **The decode, as values.** -/
theorem decodeBlock_vals (k : Nat) (s : RegState) {r n d : Nat}
    (hr : r = k % c.B) (hn : n = c.n0 + k / c.B) (hd : d = r + 2)
    (hkM : k < M) (hB0 : 0 < c.B) (hBM : c.B < M) (hn0 : c.n0 < M)
    (hnM : n < M) (hdM : d < M) (hB2 : c.B - 2 < M) (hB1 : c.B - 1 < M) :
    srun k s (decodeBlock c) rN = n ∧
      srun k s (decodeBlock c) rD = d ∧
      srun k s (decodeBlock c) rSq = MMul d d ∧
      srun k s (decodeBlock c) rW = bitOf (r < c.B - 2) ∧
      srun k s (decodeBlock c) rQg = bitOf (r = c.B - 2) ∧
      srun k s (decodeBlock c) rC = bitOf (r = c.B - 1) ∧
      srun k s (decodeBlock c) rS = MMul (s rS) (bitOf (r ≠ 0)) ∧
      srun k s (decodeBlock c) rAcc = MMul (s rAcc) (bitOf (r ≠ 0)) := by
  have hBne : c.B ≠ 0 := by omega
  have hdc : 2 + r = d := by omega
  have hR1 : srun k s (Bdecp1 c) rR = r := by
    refine step_write (Bdecs0 c) (denoteOperand_idx_of_lt k _ hkM)
      (denoteOperand_lit_of_lt k _ hBM) ?_
    rw [hr]; exact dop_urem hBne hkM
  have hR3 : srun k s (Bdecp3 c) rR = r := run_frameA (Bdecg1_3 c) hR1
  have hR5 : srun k s (Bdecp5 c) rR = r := run_frameA (Bdecg1_5 c) hR1
  have hR6 : srun k s (Bdecp6 c) rR = r := run_frameA (Bdecg1_6 c) hR1
  have hR7 : srun k s (Bdecp7 c) rR = r := run_frameA (Bdecg1_7 c) hR1
  have hR8 : srun k s (Bdecp8 c) rR = r := run_frameA (Bdecg1_8 c) hR1
  have hN2 : srun k s (Bdecp2 c) rN = k / c.B :=
    step_write (Bdecs1 c) (denoteOperand_idx_of_lt k _ hkM)
      (denoteOperand_lit_of_lt k _ hBM) (dop_udiv hBne hkM)
  have hN3 : srun k s (Bdecp3 c) rN = n := by
    refine step_write (Bdecs2 c) (denoteOperand_lit_of_lt k _ hn0) hN2 ?_
    rw [hn]; exact denoteOp_add_of_lt (by omega)
  have hD4 : srun k s (Bdecp4 c) rD = d := by
    refine step_write (Bdecs3 c) (denoteOperand_lit_of_lt k _ (by decide)) hR3 ?_
    rw [← hdc]; exact denoteOp_add_of_lt (by omega)
  have hSq5 : srun k s (Bdecp5 c) rSq = MMul d d :=
    step_write (Bdecs4 c) hD4 hD4 (dop_mul _ _)
  have hW6 : srun k s (Bdecp6 c) rW = bitOf (r < c.B - 2) :=
    step_write (Bdecs5 c) hR5 (denoteOperand_lit_of_lt k _ hB2) (dop_lt _ _)
  have hQg7 : srun k s (Bdecp7 c) rQg = bitOf (r = c.B - 2) :=
    step_write (Bdecs6 c) hR6 (denoteOperand_lit_of_lt k _ hB2) (dop_eq _ _)
  have hC8 : srun k s (Bdecp8 c) rC = bitOf (r = c.B - 1) :=
    step_write (Bdecs7 c) hR7 (denoteOperand_lit_of_lt k _ hB1) (dop_eq _ _)
  have hZ9 : srun k s (Bdecp9 c) rZ = bitOf (r = 0) :=
    step_write (Bdecs8 c) hR8 (denoteOperand_lit_of_lt k _ M_pos) (dop_eq _ _)
  have hT10 : srun k s (Bdecp10 c) rT1 = bitOf (r ≠ 0) := by
    have h : srun k s (Bdecp10 c) rT1 = MS 1 (bitOf (r = 0)) :=
      step_write (Bdecs9 c) (denoteOperand_lit_of_lt k _ one_lt_M) hZ9 (dop_sub _ _)
    rw [h, MS_one_bit]
  have hT11 : srun k s (Bdecp11 c) rT1 = bitOf (r ≠ 0) := run_frameA (Bdecg10_11 c) hT10
  have hS10 : srun k s (Bdecp10 c) rS = s rS :=
    run_frameA (Bdecg0_10 c) (srun_entry k rS s (Bdecp0 c) rfl)
  have hA11 : srun k s (Bdecp11 c) rAcc = s rAcc :=
    run_frameA (Bdecg0_11 c) (srun_entry k rAcc s (Bdecp0 c) rfl)
  have hS11 : srun k s (Bdecp11 c) rS = MMul (s rS) (bitOf (r ≠ 0)) :=
    step_write (Bdecs10 c) hS10 hT10 (dop_mul _ _)
  have hA12 : srun k s (Bdecp12 c) rAcc = MMul (s rAcc) (bitOf (r ≠ 0)) :=
    step_write (Bdecs11 c) hA11 hT11 (dop_mul _ _)
  exact ⟨run_frameA ((Bdecfull c).trans (Bdecg3_12 c)) hN3,
    run_frameA ((Bdecfull c).trans (Bdecg4_12 c)) hD4,
    run_frameA ((Bdecfull c).trans (Bdecg5_12 c)) hSq5,
    run_frameA ((Bdecfull c).trans (Bdecg6_12 c)) hW6,
    run_frameA ((Bdecfull c).trans (Bdecg7_12 c)) hQg7,
    run_frameA ((Bdecfull c).trans (Bdecg8_12 c)) hC8,
    run_frameA ((Bdecfull c).trans (Bdecg11_12 c)) hS11,
    run_frameA (Bdecfull c) hA12⟩

/-- **The decode is defined** when `B` is a nonzero word. -/
theorem decodeBlock_defined (k : Nat) (s : RegState) (hB0 : 0 < c.B)
    (hBM : c.B < M) : SAllDefined k s (decodeBlock c) := by
  have hbne : (c.B % M) ≠ 0 := by rw [Nat.mod_eq_of_lt hBM]; omega
  show SAllDefined k s (Bdeci0 c :: [Bdeci1 c, Bdeci2 c, Bdeci3, Bdeci4, Bdeci5 c,
    Bdeci6 c, Bdeci7 c, Bdeci8, Bdeci9, Bdeci10, Bdeci11])
  refine sAllDefined_cons (sDefined_urem (by rw [denoteOperand_lit]; exact hbne)) ?_
  refine sAllDefined_cons (sDefined_udiv (by rw [denoteOperand_lit]; exact hbne)) ?_
  exact sAllDefined_of_noDiv k _ _ (by rfl)

/-! ## The trial round -/

/-- **The trial round, as a value.**  The one register of the eleven that
survives is `rS`. -/
theorem scanBlock_vals (k : Nat) (u : RegState) (hD : u rD ≠ 0) (hN : u rN < M) :
    srun k u scanBlock rS = semScanS (u rS) (u rSq) (u rN) (u rD) (u rW) := by
  have e0 : srun k u Bscnp0 rS = u rS := srun_entry k rS u Bscnp0 rfl
  have hS3 : srun k u Bscnp3 rN = u rN := run_frameA Bscng0_3 (srun_entry k rN u Bscnp0 rfl)
  have hD3 : srun k u Bscnp3 rD = u rD := run_frameA Bscng0_3 (srun_entry k rD u Bscnp0 rfl)
  have hSq1 : srun k u Bscnp1 rSq = u rSq := run_frameA Bscng0_1 (srun_entry k rSq u Bscnp0 rfl)
  have hN1 : srun k u Bscnp1 rN = u rN := run_frameA Bscng0_1 (srun_entry k rN u Bscnp0 rfl)
  have hW6 : srun k u Bscnp6 rW = u rW := run_frameA Bscng0_6 (srun_entry k rW u Bscnp0 rfl)
  have hS8 : srun k u Bscnp8 rS = u rS := run_frameA Bscng0_8 (srun_entry k rS u Bscnp0 rfl)
  have hD9 : srun k u Bscnp9 rD = u rD := run_frameA Bscng0_9 (srun_entry k rD u Bscnp0 rfl)
  have hG1 : srun k u Bscnp1 rG = bitOf (u rS = 0) :=
    step_write Bscns0 e0 (denoteOperand_lit_of_lt k _ M_pos) (dop_eq _ _)
  have hG2 : srun k u Bscnp2 rG = bitOf (u rS = 0) := run_frameA Bscng1_2 hG1
  have hT2 : srun k u Bscnp2 rT1 = bitOf (u rSq ≤ u rN) :=
    step_write Bscns1 hSq1 hN1 (dop_le _ _)
  have hG3 : srun k u Bscnp3 rG = bitOf ((u rS = 0) ∧ (u rSq ≤ u rN)) := by
    have h : srun k u Bscnp3 rG =
        MMul (bitOf (u rS = 0)) (bitOf (u rSq ≤ u rN)) :=
      step_write Bscns2 hG2 hT2 (dop_mul _ _)
    rw [h, MMul_bit]
  have hG5 : srun k u Bscnp5 rG = bitOf ((u rS = 0) ∧ (u rSq ≤ u rN)) :=
    run_frameA Bscng3_5 hG3
  have hR4 : srun k u Bscnp4 rT2 = u rN % u rD :=
    step_write Bscns3 hS3 hD3 (dop_urem hD hN)
  have hE5 : srun k u Bscnp5 rT2 = bitOf (u rN % u rD = 0) :=
    step_write Bscns4 hR4 (denoteOperand_lit_of_lt k _ M_pos) (dop_eq _ _)
  have hG6 : srun k u Bscnp6 rG =
      bitOf ((u rS = 0 ∧ u rSq ≤ u rN) ∧ u rN % u rD = 0) := by
    have h : srun k u Bscnp6 rG =
        MMul (bitOf ((u rS = 0) ∧ (u rSq ≤ u rN))) (bitOf (u rN % u rD = 0)) :=
      step_write Bscns5 hG5 hE5 (dop_mul _ _)
    rw [h, MMul_bit]
  have hG7 : srun k u Bscnp7 rG = semScanG (u rS) (u rSq) (u rN) (u rD) (u rW) :=
    step_write Bscns6 hG6 hW6 (dop_mul _ _)
  have hG9 : srun k u Bscnp9 rG = semScanG (u rS) (u rSq) (u rN) (u rD) (u rW) :=
    run_frameA Bscng7_9 hG7
  have hT8 : srun k u Bscnp8 rT1 =
      MS 1 (semScanG (u rS) (u rSq) (u rN) (u rD) (u rW)) :=
    step_write Bscns7 (denoteOperand_lit_of_lt k _ one_lt_M) hG7 (dop_sub _ _)
  have hT9 : srun k u Bscnp9 rT1 =
      MMul (MS 1 (semScanG (u rS) (u rSq) (u rN) (u rD) (u rW))) (u rS) :=
    step_write Bscns8 hT8 hS8 (dop_mul _ _)
  have hT10 : srun k u Bscnp10 rT1 =
      MMul (MS 1 (semScanG (u rS) (u rSq) (u rN) (u rD) (u rW))) (u rS) :=
    run_frameA Bscng9_10 hT9
  have hU10 : srun k u Bscnp10 rT2 =
      MMul (semScanG (u rS) (u rSq) (u rN) (u rD) (u rW)) (u rD) :=
    step_write Bscns9 hG9 hD9 (dop_mul _ _)
  have hS11 : srun k u Bscnp11 rS = semScanS (u rS) (u rSq) (u rN) (u rD) (u rW) :=
    step_write Bscns10 hT10 hU10 (dop_add _ _)
  exact run_frameA Bscnfull hS11

/-- **The trial round is defined** as soon as its divisor is nonzero on entry. -/
theorem scanBlock_defined (k : Nat) (u : RegState) (hD : u rD ≠ 0) :
    SAllDefined k u scanBlock := by
  have hD3 : srun k u Bscnp3 rD = u rD :=
    run_frameA Bscng0_3 (srun_entry k rD u Bscnp0 rfl)
  show SAllDefined k u (Bscnp3 ++ Bscni3 :: [Bscni4, Bscni5, Bscni6, Bscni7,
    Bscni8, Bscni9, Bscni10])
  refine sAllDefined_stage (by rfl) (sDefined_urem ?_) ?_
  · show srun k u Bscnp3 rD ≠ 0
    rw [hD3]; exact hD
  · exact sAllDefined_of_noDiv k _ _ (by rfl)

/-! ## The factor select -/

theorem semP_eq {S n : Nat} (hS : S < M) (hn : n < M) :
    semP S n = if S = 0 then n else S := by
  unfold semP
  rw [MS_one_bit]
  exact select_bit (S = 0) hn hS

theorem semP_ne_zero {S n : Nat} (hS : S < M) (hn : n < M) (hn0 : n ≠ 0) :
    semP S n ≠ 0 := by
  rw [semP_eq hS hn]
  split
  · exact hn0
  · assumption

private theorem select_rP5 (k : Nat) (u : RegState) :
    srun k u Bselp5 rP = semP (u rS) (u rN) := by
  have hS0 : srun k u Bselp0 rS = u rS := srun_entry k rS u Bselp0 rfl
  have hS2 : srun k u Bselp2 rS = u rS := run_frameA Bselg0_2 hS0
  have hN3 : srun k u Bselp3 rN = u rN := run_frameA Bselg0_3 (srun_entry k rN u Bselp0 rfl)
  have hB1 : srun k u Bselp1 rT1 = bitOf (u rS = 0) :=
    step_write Bsels0 hS0 (denoteOperand_lit_of_lt k _ M_pos) (dop_eq _ _)
  have hB3 : srun k u Bselp3 rT1 = bitOf (u rS = 0) := run_frameA Bselg1_3 hB1
  have hB2 : srun k u Bselp2 rT2 = MS 1 (bitOf (u rS = 0)) :=
    step_write Bsels1 (denoteOperand_lit_of_lt k _ one_lt_M) hB1 (dop_sub _ _)
  have hB3' : srun k u Bselp3 rT2 = MMul (MS 1 (bitOf (u rS = 0))) (u rS) :=
    step_write Bsels2 hB2 hS2 (dop_mul _ _)
  have hB4' : srun k u Bselp4 rT2 = MMul (MS 1 (bitOf (u rS = 0))) (u rS) :=
    run_frameA Bselg3_4 hB3'
  have hB4 : srun k u Bselp4 rT3 = MMul (bitOf (u rS = 0)) (u rN) :=
    step_write Bsels3 hB3 hN3 (dop_mul _ _)
  exact step_write Bsels4 hB4 hB4' (dop_add _ _)

/-- **The factor select, as values.** -/
theorem selectBlock_vals (k : Nat) (u : RegState) (hS : u rS < M) (hN : u rN < M)
    (hN0 : u rN ≠ 0) :
    srun k u selectBlock rP = semP (u rS) (u rN) ∧
      srun k u selectBlock rQ = semQ (u rS) (u rN) := by
  have hB5 : srun k u Bselp5 rP = semP (u rS) (u rN) := select_rP5 k u
  have hN5 : srun k u Bselp5 rN = u rN := run_frameA Bselg0_5 (srun_entry k rN u Bselp0 rfl)
  have hB6 : srun k u Bselp6 rQ = semQ (u rS) (u rN) :=
    step_write Bsels5 hN5 hB5 (dop_udiv (semP_ne_zero hS hN hN0) hN)
  exact ⟨run_frameA (Bselfull.trans Bselg5_6) hB5, run_frameA Bselfull hB6⟩

theorem selectBlock_defined (k : Nat) (u : RegState) (hS : u rS < M) (hN : u rN < M)
    (hN0 : u rN ≠ 0) : SAllDefined k u selectBlock := by
  have hB5 : srun k u Bselp5 rP = semP (u rS) (u rN) := select_rP5 k u
  show SAllDefined k u (Bselp5 ++ Bseli5 :: [])
  refine sAllDefined_stage (by rfl) (sDefined_udiv ?_) ?_
  · show srun k u Bselp5 rP ≠ 0
    rw [hB5]; exact semP_ne_zero hS hN hN0
  · exact sAllDefined_of_noDiv k _ _ (by rfl)

/-! ## The load index -/

/-- **The load index, as a value.** -/
theorem indexBlock_vals (k : Nat) (u : RegState) (hSq : u rSq ≠ 0) (hN : u rN < M)
    (hlim : c.limit + 1 < M) :
    srun k u (indexBlock c) rQq = u rN / u rSq ∧
      srun k u (indexBlock c) rI =
        semI (u rW) (u rN / u rSq) (u rQg) (u rQ) (u rC) (c.limit + 1) (u rIdx) := by
  have hN0 : srun k u (Bidxp0 c) rN = u rN := srun_entry k rN u (Bidxp0 c) rfl
  have hSq0 : srun k u (Bidxp0 c) rSq = u rSq := srun_entry k rSq u (Bidxp0 c) rfl
  have hW1 : srun k u (Bidxp1 c) rW = u rW :=
    run_frameA (Bidxg0_1 c) (srun_entry k rW u (Bidxp0 c) rfl)
  have hQg2 : srun k u (Bidxp2 c) rQg = u rQg :=
    run_frameA (Bidxg0_2 c) (srun_entry k rQg u (Bidxp0 c) rfl)
  have hQ2 : srun k u (Bidxp2 c) rQ = u rQ :=
    run_frameA (Bidxg0_2 c) (srun_entry k rQ u (Bidxp0 c) rfl)
  have hIdx4 : srun k u (Bidxp4 c) rIdx = u rIdx :=
    run_frameA (Bidxg0_4 c) (srun_entry k rIdx u (Bidxp0 c) rfl)
  have hC5 : srun k u (Bidxp5 c) rC = u rC :=
    run_frameA (Bidxg0_5 c) (srun_entry k rC u (Bidxp0 c) rfl)
  have hQ1 : srun k u (Bidxp1 c) rQq = u rN / u rSq :=
    step_write (Bidxs0 c) hN0 hSq0 (dop_udiv hSq hN)
  have hI2 : srun k u (Bidxp2 c) rI = MMul (u rW) (u rN / u rSq) :=
    step_write (Bidxs1 c) hW1 hQ1 (dop_mul _ _)
  have hI3 : srun k u (Bidxp3 c) rI = MMul (u rW) (u rN / u rSq) :=
    run_frameA (Bidxg2_3 c) hI2
  have hT3 : srun k u (Bidxp3 c) rT1 = MMul (u rQg) (u rQ) :=
    step_write (Bidxs2 c) hQg2 hQ2 (dop_mul _ _)
  have hI4 : srun k u (Bidxp4 c) rI =
      MA (MMul (u rW) (u rN / u rSq)) (MMul (u rQg) (u rQ)) :=
    step_write (Bidxs3 c) hI3 hT3 (dop_add _ _)
  have hI6 : srun k u (Bidxp6 c) rI =
      MA (MMul (u rW) (u rN / u rSq)) (MMul (u rQg) (u rQ)) :=
    run_frameA (Bidxg4_6 c) hI4
  have hT5 : srun k u (Bidxp5 c) rT1 = MA (c.limit + 1) (u rIdx) :=
    step_write (Bidxs4 c) (denoteOperand_lit_of_lt k _ hlim) hIdx4 (dop_add _ _)
  have hT6 : srun k u (Bidxp6 c) rT1 = MMul (u rC) (MA (c.limit + 1) (u rIdx)) :=
    step_write (Bidxs5 c) hC5 hT5 (dop_mul _ _)
  have hI7 : srun k u (Bidxp7 c) rI =
      semI (u rW) (u rN / u rSq) (u rQg) (u rQ) (u rC) (c.limit + 1) (u rIdx) :=
    step_write (Bidxs6 c) hI6 hT6 (dop_add _ _)
  exact ⟨run_frameA ((Bidxfull c).trans (Bidxg1_7 c)) hQ1,
    run_frameA (Bidxfull c) hI7⟩

theorem indexBlock_defined (k : Nat) (u : RegState) (hSq : u rSq ≠ 0) (hN : u rN < M) :
    SAllDefined k u (indexBlock c) := by
  show SAllDefined k u (Bidxi0 :: [Bidxi1, Bidxi2, Bidxi3, Bidxi4 c, Bidxi5, Bidxi6])
  refine sAllDefined_cons (sDefined_udiv ?_) ?_
  · exact hSq
  · exact sAllDefined_of_noDiv k _ _ (by rfl)

end LeanCompCert.Ports.RamareMStar140M
