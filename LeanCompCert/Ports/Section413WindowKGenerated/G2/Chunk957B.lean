import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk957A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk957B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk957A

def state06 : KState := ⟨⟨360606173710431600, 360606234277846211⟩, ⟨(-2303314190641504703), (-2299397790362532547)⟩, true⟩

def words05 : List Nat := [360582220273174117, 360582220531378288, 360582220786574812, 360582221096488343, 360582221336114245, 360582221575954658, 360582221747837000, 360582221933794953, 360582222185673438, 360582222438053785]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 95750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 95700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360592941337663880, 360593001918139191⟩, ⟨(-1036170206725750183), (-1032252555687678575)⟩, true⟩

def words06 : List Nat := [360582222687658679, 360582222828767174, 360582222908079923, 360582222987542794, 360582223027959252, 360582223152658536, 360582223274211618, 360582223396008862, 360582223462533107, 360582223576515029]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 95760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 95700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360606091028436410, 360606151622021065⟩, ⟨(-2295597507645456783), (-2291678601061055343)⟩, true⟩

def words07 : List Nat := [360582223689893938, 360582223803675035, 360582224026102686, 360582224251421895, 360582224382674460, 360582224514031681, 360582224661633568, 360582224886029732, 360582225136964022, 360582225388205788]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 95770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 95700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360603610339577381, 360603670946402118⟩, ⟨(-2058086196593539032), (-2054166021809216028)⟩, true⟩

def words08 : List Nat := [360582225555632036, 360582225641302124, 360582225835742010, 360582226030593214, 360582226197253651, 360582226290738305, 360582226314904469, 360582226339242969, 360582226472305546, 360582226697758622]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 95780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 95700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360579445153479886, 360579505773382441⟩, ⟨256875642990499640, 260797070563363998⟩, true⟩

def words09 : List Nat := [360582227031766215, 360582227366033258, 360582227630523121, 360582227811036523, 360582227880553951, 360582227950428664, 360582228052092435, 360582228106739882, 360582228107985533, 360582228081008364]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 95790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 95700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 95700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk957B
