import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk397A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk397B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk397A

def state06 : KState := ⟨⟨360587590340019837, 360587600072788682⟩, ⟨(-203983425866810285), (-203721874854330847)⟩, true⟩

def words05 : List Nat := [360582471743971491, 360582472643743596, 360582473053676902, 360582473697745027, 360582474182226583, 360582474666826204, 360582475632463780, 360582476153261890, 360582476282612952, 360582476412044377]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 39750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 39700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360615199736457270, 360615209474305573⟩, ⟨(-1301829969502391944), (-1301568216505578328)⟩, true⟩

def words06 : List Nat := [360582477172441628, 360582478290686048, 360582479617571900, 360582480944492923, 360582481650568925, 360582481967130359, 360582481967576926, 360582481796974595, 360582482085854946, 360582482909308325]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 39760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 39700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360609964390266716, 360609974133249360⟩, ⟨(-1093595415962766287), (-1093333458749070807)⟩, true⟩

def words07 : List Nat := [360582483415630133, 360582483921980500, 360582484803555269, 360582486177801423, 360582487183417445, 360582488189073464, 360582488879032873, 360582488940034337, 360582489631399768, 360582490322919075]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 39770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 39700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580614658024384, 360580624406082782⟩, ⟨73932560258019821, 74194719410796817⟩, true⟩

def words08 : List Nat := [360582490997235586, 360582491042694623, 360582491043174485, 360582490711561843, 360582490379878147, 360582489804789922, 360582489627281247, 360582489545472802, 360582489463604178, 360582489063519596]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 39780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 39700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360625734034114003, 360625743787257233⟩, ⟨(-1721674877578591495), (-1721412516075310101)⟩, true⟩

def words09 : List Nat := [360582489600349047, 360582490184168282, 360582490953465303, 360582491280983618, 360582491281488935, 360582491008559684, 360582490735542185, 360582491128757147, 360582492215943135, 360582493303197152]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 39790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 39700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 39700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk397B
