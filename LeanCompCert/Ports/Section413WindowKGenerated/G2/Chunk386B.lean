import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk386A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk386B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk386A

def state06 : KState := ⟨⟨360619921481051599, 360619930661757366⟩, ⟨(-1459549167250044325), (-1459309264114916073)⟩, true⟩

def words05 : List Nat := [360582181714665649, 360582181297564403, 360582181130173018, 360582181756446553, 360582181809080186, 360582181861747581, 360582181901064316, 360582182419398307, 360582183396236883, 360582184373143132]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 38650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 38600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360582630401080227, 360582639586769106⟩, ⟨(-17946700767700288), (-17706604960866616)⟩, true⟩

def words06 : List Nat := [360582184826833054, 360582185091096832, 360582185461606541, 360582185832255160, 360582185832696593, 360582185604877393, 360582184712288604, 360582183484777066, 360582182257220010, 360582181708644391]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 38660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 38600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360547606112164992, 360547615302772616⟩, ⟨1336733144324531865, 1336973430363763319⟩, true⟩

def words07 : List Nat := [360582182387776935, 360582183066974444, 360582183413044190, 360582183413567043, 360582183313364458, 360582182564806933, 360582181816131255, 360582181734291962, 360582181175970902, 360582180282875092]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 38670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 38600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360593865935728848, 360593875131279360⟩, ⟨(-452723838152614096), (-452483360898402668)⟩, true⟩

def words08 : List Nat := [360582179389707296, 360582179010669551, 360582179563586065, 360582180116575175, 360582180117057122, 360582180098192297, 360582180024026132, 360582180036692503, 360582180037122634, 360582180335050305]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 38680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 38600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360617527137502132, 360617536338033913⟩, ⟨(-1368348834928895252), (-1368108164924916964)⟩, true⟩

def words09 : List Nat := [360582180335520793, 360582180291499833, 360582180868885703, 360582181824195967, 360582182508682745, 360582183193228424, 360582183543172537, 360582183791337396, 360582184705262804, 360582185619320575]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 38690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 38600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 38600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk386B
