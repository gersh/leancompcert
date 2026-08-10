import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk761A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk761B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk761A

def state06 : KState := ⟨⟨360601122227040673, 360601159861574300⟩, ⟨(-1447532042679305420), (-1445596140092901238)⟩, true⟩

def words05 : List Nat := [360582178878815068, 360582178955904448, 360582178956804885, 360582178893863434, 360582178860220868, 360582178679948006, 360582178499471977, 360582178568566015, 360582178818672723, 360582179069041470]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 76150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 76100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590031663084457, 360590069307947820⟩, ⟨(-602911017878758691), (-600974328528733821)⟩, true⟩

def words06 : List Nat := [360582179223083667, 360582179244287131, 360582179437472202, 360582179630978731, 360582179780685622, 360582179781771085, 360582179759529907, 360582179600806059, 360582179441878764, 360582179503054505]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 76160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 76100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360568706074892471, 360568743729980253⟩, ⟨1021617270334152770, 1023554738529392292⟩, true⟩

def words07 : List Nat := [360582179670029800, 360582179837206734, 360582179917990175, 360582180003772746, 360582180004688538, 360582179976497046, 360582179976920921, 360582179978006944, 360582179908618897, 360582179733373918]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 76170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 76100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360586855705289777, 360586893370635498⟩, ⟨(-361178674382615270), (-359240424686431370)⟩, true⟩

def words08 : List Nat := [360582179557897516, 360582179378659425, 360582179285434158, 360582179196290352, 360582179107073844, 360582178872074125, 360582178611798202, 360582178470929602, 360582178329725543, 360582178372477101]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 76180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 76100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360571938703903662, 360571976379588485⟩, ⟨775429385019847015, 777368422501623899⟩, true⟩

def words09 : List Nat := [360582178373444639, 360582178344330230, 360582178336339439, 360582178478669746, 360582178499103751, 360582178519698548, 360582178520672620, 360582178410239262, 360582178197565199, 360582178064923152]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 76190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 76100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 76100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk761B
