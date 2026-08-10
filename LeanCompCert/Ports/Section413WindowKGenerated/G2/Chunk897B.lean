import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk897A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk897B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk897A

def state06 : KState := ⟨⟨360567028661541131, 360567081609692329⟩, ⟨1338537293767246553, 1341746666318083321⟩, true⟩

def words05 : List Nat := [360582031320316906, 360582031053100795, 360582030785636243, 360582030642577756, 360582030595002559, 360582030491340402, 360582030387547362, 360582030222264308, 360582029932784741, 360582029767739545]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 89750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 89700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360563093487435820, 360563146447787509⟩, ⟨1691722827025253685, 1694933294754673003⟩, true⟩

def words06 : List Nat := [360582029602271636, 360582029434115178, 360582029195567627, 360582028894875994, 360582028593984910, 360582028224882001, 360582027917922154, 360582027735201927, 360582027552323254, 360582027290995203]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 89760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 89700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360574640351756255, 360574693324331743⟩, ⟨655042297010553144, 658253862129384428⟩, true⟩

def words07 : List Nat := [360582027081726883, 360582026891673503, 360582026701243908, 360582026609818847, 360582026394420169, 360582026070128491, 360582025745597601, 360582025463316206, 360582025258767727, 360582025178443231]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 89770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 89700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360574551709456459, 360574604694375332⟩, ⟨663002500847382740, 666215174215430000⟩, true⟩

def words08 : List Nat := [360582025097933417, 360582024955333408, 360582024940740278, 360582024996319987, 360582025020297682, 360582025021592994, 360582024921751641, 360582024757267031, 360582024592556170, 360582024397841369]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 89780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 89700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360564591620627135, 360564644617747032⟩, ⟨1557394451674123147, 1560608220632911839⟩, true⟩

def words09 : List Nat := [360582024316260362, 360582024271991117, 360582024227598149, 360582024087557441, 360582023965943170, 360582023813479201, 360582023660613157, 360582023631873449, 360582023520630765, 360582023328444504]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 89790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 89700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 89700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk897B
