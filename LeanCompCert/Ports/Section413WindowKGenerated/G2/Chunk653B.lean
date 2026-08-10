import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk653A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk653B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk653A

def state06 : KState := ⟨⟨360583806889244278, 360583834272380380⟩, ⟨(-61089063672471488), (-59880065265255030)⟩, true⟩

def words05 : List Nat := [360582919429123452, 360582919198031602, 360582918968271574, 360582918969192749, 360582918837457778, 360582918506829516, 360582918176035074, 360582918098980719, 360582918113755538, 360582918128727969]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 65350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 65300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360602210521427949, 360602237913332857⟩, ⟨(-1264162751599262801), (-1262953180020085203)⟩, true⟩

def words06 : List Nat := [360582918129548398, 360582918027249938, 360582917933317476, 360582917979240251, 360582917980013091, 360582917920124439, 360582917920953446, 360582917832250618, 360582917839160039, 360582918135755337]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 65360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 65300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360562401168148948, 360562428568740992⟩, ⟨1338467457270391627, 1339677596770721005⟩, true⟩

def words07 : List Nat := [360582918665628035, 360582919195661087, 360582919512170322, 360582919595450671, 360582919615008446, 360582919634818169, 360582919653691970, 360582919654613204, 360582919514355733, 360582919201912769]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 65370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 65300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587412202026112, 360587439611309398⟩, ⟨(-296817162557554143), (-295606454780007149)⟩, true⟩

def words08 : List Nat := [360582918889254173, 360582918894686206, 360582919164796608, 360582919435081345, 360582919504454154, 360582919505375469, 360582919341422015, 360582919172097306, 360582919002508643, 360582919012835908]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 65380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 65300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582500967917615, 360582528385975079⟩, ⟨24372980926089783, 25584262488986907⟩, true⟩

def words09 : List Nat := [360582919013656930, 360582918944821310, 360582919039489654, 360582919384842418, 360582919519263100, 360582919653823800, 360582919671221634, 360582919672145170, 360582919587578690, 360582919582649223]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 65390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 65300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 65300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk653B
