import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk431A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk431B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk431A

def state06 : KState := ⟨⟨360630274822310245, 360630286367918364⟩, ⟨(-2036270820623563959), (-2035934063495039301)⟩, true⟩

def words05 : List Nat := [360583110637158038, 360583111501847285, 360583112447425949, 360583112858275510, 360583112858832593, 360583112754041610, 360583112936250197, 360583113492957075, 360583114586409726, 360583115679947858]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 43150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 43100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360605925913512770, 360605937464731759⟩, ⟨(-985334992530681532), (-984997993208994716)⟩, true⟩

def words06 : List Nat := [360583116502452695, 360583117340006483, 360583118354353198, 360583119368834473, 360583120129977672, 360583120491582073, 360583120582362787, 360583120673204918, 360583120739640706, 360583121268831526]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 43160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 43100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360545955836307447, 360545967393070757⟩, ⟨1603941805207636926, 1604279043905380642⟩, true⟩

def words07 : List Nat := [360583122045303528, 360583122821851849, 360583123214591679, 360583123215180478, 360583123073615760, 360583122556222238, 360583122057120777, 360583122057709589, 360583121542484128, 360583120682647075]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 43170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 43100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360602940872562002, 360602952434891613⟩, ⟨(-857086206296803522), (-856748727218441436)⟩, true⟩

def words08 : List Nat := [360583119822715367, 360583119247326054, 360583118939932344, 360583118507025555, 360583118074092881, 360583117190150330, 360583116509232206, 360583116059667849, 360583115695970565, 360583116155870094]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 43180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 43100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360571427717685733, 360571439285628247⟩, ⟨504213876270228828, 504551597797702642⟩, true⟩

def words09 : List Nat := [360583116346842916, 360583116537866381, 360583117085316987, 360583117978449085, 360583118639920037, 360583119301456385, 360583119412624661, 360583119413213802, 360583118990446861, 360583118720762454]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 43190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 43100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 43100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk431B
