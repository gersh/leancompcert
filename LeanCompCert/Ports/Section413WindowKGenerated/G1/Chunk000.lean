import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk000

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨0, 0⟩, ⟨0, 0⟩, true⟩

def state01 : KState := ⟨⟨306746031746031554, 306746031746031944⟩, ⟨749999999999998559, 750000000000001413⟩, true⟩

def words00 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 0 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 0 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨383299621870312276, 383299621870314338⟩, ⟨(-315167548500896589), (-315167548500867067)⟩, true⟩

def words01 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 10 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 0 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨357060470389561373, 357060470389566379⟩, ⟨219104387125168036, 219104387125272948⟩, true⟩

def words02 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 20 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 0 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨343204632863719113, 343204632863728719⟩, ⟨811647543337376282, 811647543337644800⟩, true⟩

def words03 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 372295821447169839]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 30 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 0 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨359472963212234486, 359472963212250350⟩, ⟨184704511228945170, 184704511229497870⟩, true⟩

def words04 : List Nat := [371800914408549751, 371776511721103160, 371778489775206178, 371995502623492345, 372126398894446999, 372126398894447708, 371765720650466657, 371781672058202539, 371967053436839556, 371967053436840308]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 40 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 0 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨359682665211561329, 359682665211584637⟩, ⟨188452433075771543, 188452433076736601⟩, true⟩

def words05 : List Nat := [371894620295182261, 371778972419645363, 371863301879147817, 371883451765453506, 371917775067583587, 371950894043323462, 371974089766761594, 371974089766762435, 371676774246782484, 371623539096196914]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 50 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 0 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨355576249934679231, 355576249934711461⟩, ⟨465196589604009032, 465196589605558142⟩, true⟩

def words06 : List Nat := [371750053333747599, 371750053333748528, 371630897103487636, 371466894730290454, 371307938583960545, 371198435674729501, 371020846333627188, 371029244048327535, 371029244048328337, 371021915500505149]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 60 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 0 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨370849760260708699, 370849760260752010⟩, ⟨(-655981879553067168), (-655981879550683500)⟩, true⟩

def words07 : List Nat := [371010433195394634, 371090301988586291, 371336902500414625, 371366163465602743, 371366807009122492, 371367433837226529, 371387870405340434, 371387870405341839, 371449986766366988, 371551218537904066]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 70 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 0 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨361384924482646132, 361384924482702256⟩, ⟨117018524337046197, 117018524340523161⟩, true⟩

def words08 : List Nat := [371649981241842226, 371649981241843574, 371631404952932295, 371687771979357790, 371755241201271923, 371755241201273379, 371663451248599570, 371564548268202444, 371485130308706366, 371485130308708069]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 80 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 0 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨352776791864166943, 352776791864237312⟩, ⟨949360578249322069, 949360578254156953⟩, true⟩

def words09 : List Nat := [371486718280692863, 371502252810549623, 371519255348030071, 371519255348031648, 371405561973798133, 371320165404464470, 371244437471020474, 371244437471022125, 371166292654681549, 371070397646778882]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 90 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 0 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 0 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk000
