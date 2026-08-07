import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk440

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360619146642195475, 360619158660593643⟩, ⟨(-1581994532419131131), (-1581637170441814245)⟩, true⟩

def state01 : KState := ⟨⟨360598158729941559, 360598170754072386⟩, ⟨(-658483344455717527), (-658125730213172585)⟩, true⟩

def words00 : List Nat := [360583213734298295, 360583214316587912, 360583215269275588, 360583216222097451, 360583216897721199, 360583217058523206, 360583217059058819, 360583216960402122, 360583216861643254, 360583217089529132]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 44000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 44000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360567690200924286, 360567702230716043⟩, ⟨682587062332149200, 682944925740982372⟩, true⟩

def words01 : List Nat := [360583217507284238, 360583217925132205, 360583217984362683, 360583217984964153, 360583217718352556, 360583217319937156, 360583217037868060, 360583217038472285, 360583217006115701, 360583216654290350]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 44010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 44000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360628334271446981, 360628346306924301⟩, ⟨(-1987358723559317131), (-1987000609844854205)⟩, true⟩

def words02 : List Nat := [360583216465426459, 360583217100463444, 360583217546263637, 360583217992149321, 360583217992704528, 360583217987631230, 360583217468096434, 360583217464168432, 360583217970839403, 360583218996396608]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 44020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 44000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360608547835279350, 360608559876479942⟩, ⟨(-1116078881151147988), (-1115720515412275798)⟩, true⟩

def words03 : List Nat := [360583219701349624, 360583220406334090, 360583221188740975, 360583222296664686, 360583223272612242, 360583224248613732, 360583224814727578, 360583225046736978, 360583225622492194, 360583226198420582]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 44030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 44000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360614120615201381, 360614132662069703⟩, ⟨(-1361494693082530135), (-1361136077708526729)⟩, true⟩

def words04 : List Nat := [360583227289195864, 360583228258701285, 360583228933913767, 360583229609178617, 360583230004707098, 360583230657236337, 360583231479153010, 360583232301146332, 360583232863995265, 360583233566073959]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 44040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 44000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk440
