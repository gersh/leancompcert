import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk995A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk995B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk995A

def state06 : KState := ⟨⟨362498940368854858, 362499091530189525⟩, ⟨(-1377211736181801043), (-1367051138090045865)⟩, true⟩

def words05 : List Nat := [371285360181298081, 371285360179536001, 371285360263765489, 371285360295796315, 371285360311301997, 371285360327866257, 371285360417573358, 371285360458463465, 371285360598754026, 371285360740642514]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 99550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 99500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485426630463527, 362485577823407239⟩, ⟨(-31745175021304635), (-21581429770150839)⟩, true⟩

def words06 : List Nat := [371285360846553804, 371285360850054617, 371285360919550625, 371285361007720172, 371285361124609397, 371285361128109800, 371285361110744144, 371285361078747964, 371285361073106359, 371285361079277220]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 99560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 99500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478644115624158, 362478795340038724⟩, ⟨643668438060260153, 653835317025622261⟩, true⟩

def words07 : List Nat := [371285361184723299, 371285361291590532, 371285361397192411, 371285361400693134, 371285361371748773, 371285361346083292, 371285361389480142, 371285361392980902, 371285361332132802, 371285361270115302]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 99570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 99500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485884951893921, 362486036207672215⟩, ⟨(-77365647716857146), (-67195645392834156)⟩, true⟩

def words08 : List Nat := [371285361241495946, 371285361245421838, 371285361294732862, 371285361347184020, 371285361381922187, 371285361385436279, 371285361377924477, 371285361420467889, 371285361481224405, 371285361491629673]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 99580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 99500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488601591894993, 362488752879617402⟩, ⟨(-347932869390157879), (-337759685594871527)⟩, true⟩

def words09 : List Nat := [371285361496597405, 371285361502780536, 371285361557437035, 371285361578626616, 371285361628777594, 371285361680304094, 371285361730528938, 371285361734038268, 371285361713721395, 371285361752162910]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 99590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 99500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 99500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk995B
