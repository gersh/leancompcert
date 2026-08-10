import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk363A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360539334751151285, 360539342803651827⟩, ⟨1545870141377519831, 1546067744355879007⟩, true⟩

def state01 : KState := ⟨⟨360556322289723569, 360556330346825190⟩, ⟨929163630521598510, 929361400542248870⟩, true⟩

def words00 : List Nat := [360581933028678665, 360581932303750095, 360581931605461512, 360581930524937969, 360581929444394442, 360581928025279113, 360581926990651296, 360581926713416750, 360581926436154342, 360581925538247450]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 36300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 36300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360600085971285631, 360600094032992913⟩, ⟨(-660238753273505165), (-660040815998235241)⟩, true⟩

def words01 : List Nat := [360581924833756923, 360581924237611815, 360581923801732204, 360581923802220666, 360581923468332137, 360581922481991475, 360581921495603877, 360581920858158541, 360581921102531599, 360581921603379240]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 36310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 36300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594236302799728, 360594244369165995⟩, ⟨(-447898751335819010), (-447700644823304228)⟩, true⟩

def words02 : List Nat := [360581921722245581, 360581922127318684, 360581922510895492, 360581922894592283, 360581923075320943, 360581923075809651, 360581922830456623, 360581922203566795, 360581921576618050, 360581921541695700]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 36320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 36300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360507591752459396, 360507599823422657⟩, ⟨2700503084178746063, 2700701357723179377⟩, true⟩

def words03 : List Nat := [360581922386428506, 360581923231208613, 360581923486858232, 360581923487347114, 360581923323112663, 360581922678646728, 360581922034080447, 360581921125476431, 360581919461808940, 360581917417195998]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 36330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 36300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360583179049371870, 360583187124948822⟩, ⟨(-46642719717089494), (-46444278488474342)⟩, true⟩

def words04 : List Nat := [360581915372584314, 360581914083931503, 360581913173162780, 360581913018205872, 360581912863207420, 360581912068197931, 360581911026165416, 360581910312361597, 360581909598451520, 360581909463302968]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 36340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 36300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk363A
