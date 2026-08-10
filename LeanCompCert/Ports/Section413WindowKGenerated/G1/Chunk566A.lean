import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk566A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362494269480174712, 362494316233802406⟩, ⟨(-534352194814414753), (-532564590621126199)⟩, true⟩

def state01 : KState := ⟨⟨362491164206566040, 362491210977446081⟩, ⟨(-358587724955459346), (-356799144194303784)⟩, true⟩

def words00 : List Nat := [371284907285014905, 371284907286964230, 371284907431090139, 371284907606009270, 371284907874774451, 371284907928908985, 371284907981919073, 371284908035599794, 371284908216999602, 371284908330536571]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 56600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 56600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362472867813956383, 362472914601980341⟩, ⟨677362389692870115, 679151941059183245⟩, true⟩

def words01 : List Nat := [371284908755153470, 371284909180513531, 371284909601751505, 371284909607704257, 371284909660067093, 371284909713420520, 371284909925595296, 371284909927502734, 371284909724121834, 371284909514397494]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 56610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 56600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483341404855456, 362483388209985646⟩, ⟨84300003348318613, 86090523355542167⟩, true⟩

def words02 : List Nat := [371284909326460424, 371284909328562330, 371284909196954866, 371284909194655781, 371284909191740148, 371284909131362007, 371284908733916300, 371284908531849322, 371284908436183526, 371284908438192525]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 56620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 56600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362474326079383708, 362474372901891313⟩, ⟨594961671297890294, 596753175475996932⟩, true⟩

def words03 : List Nat := [371284908412774927, 371284908379355758, 371284908621381588, 371284908744261493, 371284908937831879, 371284909132108040, 371284909263870604, 371284909265778717, 371284908981977219, 371284908798350989]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 56630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 56600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362466565731827335, 362466612571333390⟩, ⟨1034547575647034451, 1036340042703539607⟩, true⟩

def words04 : List Nat := [371284908634312960, 371284908636221291, 371284908280229929, 371284907919746429, 371284907558520717, 371284907292770220, 371284906871664818, 371284906692232257, 371284906512147126, 371284906305538219]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 56640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 56600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk566A
