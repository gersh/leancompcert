import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk239A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk239B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk239A

def state06 : KState := ⟨⟨360657598725150794, 360657602111106310⟩, ⟨(-1804686086450691168), (-1804631201195290906)⟩, true⟩

def words05 : List Nat := [360582269890299434, 360582270530922277, 360582271715848238, 360582273691591101, 360582274186856735, 360582274682105503, 360582276917447178, 360582280469342471, 360582283613237815, 360582286756939319]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 23950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 23900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360602668356587792, 360602671745517026⟩, ⟨(-488656096285385364), (-488601139764951064)⟩, true⟩

def words06 : List Nat := [360582288481019209, 360582288481331220, 360582289484580624, 360582290494289903, 360582291055047976, 360582291055360461, 360582290864714022, 360582289788444106, 360582288712200855, 360582288735222715]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 23960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 23900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360550024478279558, 360550027870147779⟩, ⟨773606630730152853, 773661657712800993⟩, true⟩

def words07 : List Nat := [360582291323798692, 360582293912219703, 360582295422494041, 360582295422806232, 360582295204722733, 360582293715221366, 360582292473570389, 360582292473883246, 360582292003344149, 360582290658209197]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 23970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 23900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584931833052132, 360584935227870032⟩, ⟨(-63318201530937038), (-63263103800449532)⟩, true⟩

def words08 : List Nat := [360582289704755946, 360582291461915352, 360582294116955737, 360582296771834114, 360582297843564921, 360582297843877268, 360582298154127399, 360582298494614175, 360582298494871600, 360582298276354862]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 23980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 23900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360609122682182560, 360609126079974937⟩, ⟨(-643846487071809777), (-643791317968820743)⟩, true⟩

def words09 : List Nat := [360582298276635052, 360582297064309095, 360582296374954206, 360582297993186313, 360582299164345739, 360582300335463754, 360582300433787107, 360582300434101067, 360582301441369906, 360582302559372928]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 23990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 23900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 23900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk239B
