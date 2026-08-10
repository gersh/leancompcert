import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk440A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk440B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk440A

def state06 : KState := ⟨⟨360628081382580532, 360628093435135025⟩, ⟨(-1976710495117674451), (-1976351629239473533)⟩, true⟩

def words05 : List Nat := [360583234036793474, 360583234507658609, 360583235493137524, 360583235964990582, 360583235965554404, 360583235926740359, 360583235996500641, 360583236500612467, 360583237519186593, 360583238537850818]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 44050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 44000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360611595382321219, 360611607440608163⟩, ⟨(-1250470870211392145), (-1250111751733583849)⟩, true⟩

def words06 : List Nat := [360583239243823833, 360583239436242181, 360583240033837917, 360583240631591516, 360583240874884973, 360583241046194783, 360583241046731387, 360583240882289851, 360583240937723493, 360583241582067772]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 44060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 44000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360547521893640074, 360547533957601609⟩, ⟨1573738780877028886, 1574098149462867270⟩, true⟩

def words07 : List Nat := [360583242740600505, 360583243899206389, 360583244739492049, 360583245066515561, 360583245088613188, 360583245110868264, 360583245210590333, 360583245211192539, 360583244797727418, 360583243988215558]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 44070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 44000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360614285192769399, 360614297262414766⟩, ⟨(-1369610121944285270), (-1369250502787216636)⟩, true⟩

def words08 : List Nat := [360583243178603499, 360583242538916035, 360583242205647938, 360583242020713348, 360583241835740116, 360583241216414629, 360583240821554786, 360583240881574620, 360583241455422809, 360583242160403308]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 44080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 44000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578456498282205, 360578468573679865⟩, ⟨210271735091160202, 210631607893800910⟩, true⟩

def words09 : List Nat := [360583242503656860, 360583242846954450, 360583243176663844, 360583243765189437, 360583244222037275, 360583244678965694, 360583244877183581, 360583244907725598, 360583244908217020, 360583244800616233]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 44090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 44000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 44000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk440B
