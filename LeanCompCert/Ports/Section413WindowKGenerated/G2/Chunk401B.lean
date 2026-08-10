import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk401A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk401B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk401A

def state06 : KState := ⟨⟨360624069190034326, 360624079127643905⟩, ⟨(-1664404301262118200), (-1664134564755457458)⟩, true⟩

def words05 : List Nat := [360582635323285534, 360582635860522960, 360582637016570190, 360582637972440858, 360582638398581488, 360582638824743412, 360582639432716525, 360582640481130160, 360582641513416539, 360582642545767073]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 40150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 40100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360646939963291051, 360646949906080051⟩, ⟨(-2583275449063353248), (-2583005504525342410)⟩, true⟩

def words06 : List Nat := [360582643103845346, 360582643275861788, 360582644066478976, 360582644857216141, 360582645362353222, 360582646113647707, 360582646553165679, 360582646992716729, 360582648050726198, 360582649652052884]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 40160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 40100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360595098545797624, 360595108493719003⟩, ⟨(-500488525108266725), (-500218374377490101)⟩, true⟩

def words07 : List Nat := [360582651400779752, 360582653149526279, 360582654420321263, 360582655288686677, 360582655997956760, 360582656707341609, 360582658034914343, 360582658745917680, 360582659056252051, 360582659366659510]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 40170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 40100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360606992844380286, 360607002797437959⟩, ⟨(-978495421821481688), (-978225064688730644)⟩, true⟩

def words08 : List Nat := [360582659966052326, 360582660965115030, 360582661757593082, 360582662550130932, 360582662823924179, 360582662824468767, 360582662672216397, 360582662504146387, 360582662785312071, 360582663391484171]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 40180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 40100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360624937484923094, 360624947443166163⟩, ⟨(-1699747595102070212), (-1699477029543333772)⟩, true⟩

def words09 : List Nat := [360582663687360126, 360582663983280886, 360582664897010437, 360582666424173729, 360582667793613938, 360582669163077409, 360582670222404352, 360582670842448710, 360582671894545897, 360582672946771961]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 40190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 40100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 40100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk401B
