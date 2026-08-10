import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk808A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk808B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk808A

def state06 : KState := ⟨⟨360581672867689970, 360581715490109069⟩, ⟨32515851910113192, 34843477790793822⟩, true⟩

def words05 : List Nat := [360582144392171560, 360582144913378723, 360582145358030165, 360582145650169325, 360582145878689186, 360582146107522044, 360582146332161301, 360582146404380482, 360582146405411703, 360582146401286299]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 80850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 80800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360591722635398494, 360591765268736569⟩, ⟨(-780130154157807104), (-777801645314060372)⟩, true⟩

def words06 : List Nat := [360582146415116104, 360582146511134104, 360582146759538199, 360582147008180524, 360582147123604425, 360582147124761809, 360582147173615125, 360582147261056928, 360582147341913151, 360582147462040547]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 80860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 80800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360593187952772595, 360593230597147269⟩, ⟨(-898689582425382824), (-896360180996307014)⟩, true⟩

def words07 : List Nat := [360582147464381511, 360582147466838458, 360582147514560991, 360582147639609208, 360582147724405885, 360582147809388043, 360582147817890775, 360582147864131935, 360582148002095381, 360582148140439312]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 80870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 80800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587672549181864, 360587715204455926⟩, ⟨(-452605241270981187), (-450274958246132705)⟩, true⟩

def words08 : List Nat := [360582148361990151, 360582148495938840, 360582148497971107, 360582148500110257, 360582148501096034, 360582148415798603, 360582148539191245, 360582148662802328, 360582148693698181, 360582148763711639]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 80880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 80800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360602301459275687, 360602344125496589⟩, ⟨(-1636000003654319787), (-1633668835086160815)⟩, true⟩

def words09 : List Nat := [360582148904751490, 360582149046162022, 360582149277076911, 360582149485001017, 360582149561949213, 360582149638985575, 360582149868387173, 360582150192201779, 360582150442775070, 360582150693584918]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 80890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 80800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 80800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk808B
