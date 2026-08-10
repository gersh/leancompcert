import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk651A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk651B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk651A

def state06 : KState := ⟨⟨362471591287315526, 362471653946505814⟩, ⟨901153505054503064, 903911155971341694⟩, true⟩

def words05 : List Nat := [371285527152351831, 371285527049436637, 371285526961597549, 371285526964042273, 371285526863959413, 371285526824653540, 371285526784567949, 371285526717118895, 371285526335184486, 371285526125081188]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 65150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 65100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362466520961520806, 362466583640506100⟩, ⟨1231544031264982931, 1234302972127704271⟩, true⟩

def words06 : List Nat := [371285525913699679, 371285525852281675, 371285525525008622, 371285525135248609, 371285524744655033, 371285524427059574, 371285523990934946, 371285523791031205, 371285523590379217, 371285523382291089]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 65160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 65100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362488306978980506, 362488369677973190⟩, ⟨(-188345762491049939), (-185585517642723353)⟩, true⟩

def words07 : List Nat := [371285523093180437, 371285523040458540, 371285523166509981, 371285523168729317, 371285523036732147, 371285522840471366, 371285522643320649, 371285522544790797, 371285522398458666, 371285522444613120]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 65170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 65100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489045284610614, 362489108003637403⟩, ⟨(-236481441833958192), (-233719891064214424)⟩, true⟩

def words08 : List Nat := [371285522489817027, 371285522492050524, 371285522475712907, 371285522587108977, 371285522769380127, 371285522771614784, 371285522742634499, 371285522714181920, 371285522790318950, 371285522847848043]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 65180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 65100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470348058097805, 362470410797160884⟩, ⟨982508594333380158, 985271451371314266⟩, true⟩

def words09 : List Nat := [371285522974091491, 371285523101229326, 371285523231700699, 371285523233922066, 371285523091507825, 371285522945444538, 371285522798245295, 371285522772979123, 371285522551737186, 371285522322488665]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 65190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 65100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 65100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk651B
