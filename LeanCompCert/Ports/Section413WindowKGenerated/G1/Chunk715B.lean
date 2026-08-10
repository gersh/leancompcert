import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk715A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk715B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk715A

def state06 : KState := ⟨⟨362479640312696224, 362479716440326424⟩, ⟨391941864322863195, 395620941820133107⟩, true⟩

def words05 : List Nat := [371285244816313176, 371285244948071183, 371285245037623596, 371285245040125003, 371285245007509642, 371285244984153804, 371285245108195683, 371285245110650504, 371285245035513234, 371285244961033805]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 71550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 71500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362497092976417467, 362497169126054830⟩, ⟨(-857062001365400847), (-853381348925376029)⟩, true⟩

def words06 : List Nat := [371285244889816316, 371285244892520008, 371285244902594079, 371285245006986285, 371285245089737169, 371285245092207603, 371285245064344813, 371285245132137854, 371285245393608014, 371285245562755095]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 71560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 71500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497149291198201, 362497225463142356⟩, ⟨(-861081129952592212), (-857398880899810450)⟩, true⟩

def words07 : List Nat := [371285245731514336, 371285245901077628, 371285246213576409, 371285246439004847, 371285246669463650, 371285246900849645, 371285247093691735, 371285247100552928, 371285247269561372, 371285247439911334]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 71570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 71500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490622667727559, 362490698861561047⟩, ⟨(-393821391298803648), (-390137575293587646)⟩, true⟩

def words08 : List Nat := [371285247772975975, 371285247944344393, 371285248100112161, 371285248256739013, 371285248456467163, 371285248571010353, 371285248808480878, 371285249046934698, 371285249249084453, 371285249327746831]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 71580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 71500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362503340312663005, 362503416528706445⟩, ⟨(-1304321162828554308), (-1300635756701020546)⟩, true⟩

def words09 : List Nat := [371285249534267345, 371285249742074823, 371285250143497318, 371285250285794924, 371285250382639688, 371285250480250353, 371285250771737089, 371285250966659489, 371285251222047431, 371285251478543724]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 71590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 71500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 71500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk715B
