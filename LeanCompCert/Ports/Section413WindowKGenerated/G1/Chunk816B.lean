import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk816A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk816B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk816A

def state06 : KState := ⟨⟨362484495007391811, 362484595158174732⟩, ⟨45068366634247653, 50590716166889747⟩, true⟩

def words05 : List Nat := [371285214233416663, 371285214336507083, 371285214480139678, 371285214559582281, 371285214644658379, 371285214730806922, 371285214809548580, 371285214812375931, 371285214691021325, 371285214686905652]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 81650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 81600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488082408453677, 362488182584477842⟩, ⟨(-247851340985028041), (-242326930125422681)⟩, true⟩

def words06 : List Nat := [371285214808257982, 371285214843243745, 371285214866340622, 371285214890456793, 371285214959406733, 371285214973416495, 371285215136113084, 371285215299939546, 371285215434126280, 371285215473384242]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 81660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 81600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500078184296779, 362500178385903393⟩, ⟨(-1227592138939741293), (-1222065638633856447)⟩, true⟩

def words07 : List Nat := [371285215661554996, 371285215851214893, 371285216116223312, 371285216198616577, 371285216235171482, 371285216272593353, 371285216458746510, 371285216571253944, 371285216756357582, 371285216942744839]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 81670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 81600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490199395165263, 362490299622308682⟩, ⟨(-420713344669877796), (-415184758384989298)⟩, true⟩

def words08 : List Nat := [371285217121516988, 371285217124345216, 371285217143174912, 371285217186559287, 371285217238389739, 371285217241238501, 371285217188108360, 371285217135586503, 371285217176151584, 371285217241650042]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 81680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 81600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362472935481213337, 362473035733791975⟩, ⟨989731037359064076, 995261701573505594⟩, true⟩

def words09 : List Nat := [371285217438558995, 371285217636603592, 371285217823673411, 371285217826502227, 371285217844845346, 371285217879421013, 371285217930823312, 371285217933652230, 371285217785507636, 371285217639563989]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 81690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 81600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 81600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk816B
