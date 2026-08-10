import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk997A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360570134362252493, 360570200220888005⟩, ⟨1215207549536387012, 1219641135696652678⟩, true⟩

def state01 : KState := ⟨⟨360590697108999926, 360590762981346699⟩, ⟨(-835051531526851562), (-830616578288819142)⟩, true⟩

def words00 : List Nat := [360582433210071602, 360582433086473911, 360582433046568545, 360582433068561568, 360582433069904411, 360582432987353219, 360582432804188149, 360582432722012551, 360582432656116211, 360582432741169700]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 99700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 99700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360587247857090274, 360587313743245708⟩, ⟨(-491111887236226035), (-486675557068948997)⟩, true⟩

def words01 : List Nat := [360582432774903760, 360582432808785856, 360582432942909185, 360582433127708859, 360582433211803848, 360582433296103394, 360582433320837058, 360582433322287491, 360582433320826918, 360582433371437675]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 99710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 99700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360601415852696456, 360601481752530283⟩, ⟨(-1903976796524174304), (-1899539102278620438)⟩, true⟩

def words02 : List Nat := [360582433522062702, 360582433718746534, 360582433851829170, 360582433985061545, 360582434092437305, 360582434276833841, 360582434521387123, 360582434766214908, 360582434933598931, 360582435126082352]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 99720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 99700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360606582730679299, 360606648644204294⟩, ⟨(-2419313784922399415), (-2414874725188267263)⟩, true⟩

def words03 : List Nat := [360582435322756647, 360582435519849604, 360582435817004715, 360582436046402751, 360582436189504634, 360582436332748812, 360582436491215855, 360582436701110594, 360582436945036755, 360582437189284169]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 99730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 99700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360588702208564898, 360588768135921687⟩, ⟨(-635912154269675720), (-631471714885944014)⟩, true⟩

def words04 : List Nat := [360582437382971878, 360582437476553345, 360582437567360065, 360582437658570667, 360582437723960525, 360582437725411556, 360582437722356999, 360582437669079664, 360582437615520986, 360582437655877518]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 99740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 99700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk997A
