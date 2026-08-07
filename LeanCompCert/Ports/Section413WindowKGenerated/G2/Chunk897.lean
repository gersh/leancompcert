import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk897

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582924555178673, 360582977429835727⟩, ⟨(-87616002983126402), (-84413225064505992)⟩, true⟩

def state01 : KState := ⟨⟨360574689842642198, 360574742729468620⟩, ⟨651062464353577078, 654266333927894602⟩, true⟩

def words00 : List Nat := [360582036491524827, 360582036492818791, 360582036481600631, 360582036408798830, 360582036335813869, 360582036146717487, 360582036019540582, 360582035993356314, 360582035967034103, 360582035855473836]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 89700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 89700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360582728884184627, 360582781783245664⟩, ⟨(-70165681332600728), (-66960714130936398)⟩, true⟩

def words01 : List Nat := [360582035800760622, 360582035827761415, 360582035851004088, 360582035852299295, 360582035802572460, 360582035647583738, 360582035492341732, 360582035442672636, 360582035452055897, 360582035461714129]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 89710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 89700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581125651683679, 360581178563084520⟩, ⟨73564656554797250, 76770730942377198⟩, true⟩

def words02 : List Nat := [360582035462879175, 360582035408851352, 360582035256323371, 360582035116070842, 360582034975479945, 360582034764102048, 360582034655802378, 360582034454266339, 360582034252486884, 360582034137930641]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 89720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 89700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360560072407279104, 360560125330884625⟩, ⟨1962806347249773540, 1966013516825507152⟩, true⟩

def words03 : List Nat := [360582034207203378, 360582034286257275, 360582034287430655, 360582034271550263, 360582034131435410, 360582033940627914, 360582033749446568, 360582033613186557, 360582033457724252, 360582033214958901]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 89730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 89700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360563470469458140, 360563523405276261⟩, ⟨1657895513680284702, 1661103779275712984⟩, true⟩

def words04 : List Nat := [360582032971882255, 360582032808662678, 360582032707289131, 360582032648007115, 360582032588626470, 360582032427304849, 360582032208786992, 360582031987714967, 360582031766260190, 360582031525379612]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 89740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 89700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk897
