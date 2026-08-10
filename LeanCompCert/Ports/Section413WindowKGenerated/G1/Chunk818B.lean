import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk818A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk818B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk818A

def state06 : KState := ⟨⟨362492520537108866, 362492621197841712⟩, ⟨(-611315125426629863), (-605751082317717631)⟩, true⟩

def words05 : List Nat := [371285221417741468, 371285221411409440, 371285221543185836, 371285221546020512, 371285221488872827, 371285221393165777, 371285221303868844, 371285221307047323, 371285221352485506, 371285221446039050]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 81850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 81800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485490042390081, 362485590728673626⟩, ⟨(-35789674039346288), (-30223539218042620)⟩, true⟩

def words06 : List Nat := [371285221536748721, 371285221539603484, 371285221607056544, 371285221708654464, 371285221815739394, 371285221818574449, 371285221726895138, 371285221623067402, 371285221560430964, 371285221568174573]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 81860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 81800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474835103272486, 362474935815157232⟩, ⟨836638426798085538, 842206657715742400⟩, true⟩

def words07 : List Nat := [371285221665001700, 371285221763076434, 371285221830719437, 371285221833569828, 371285221790309817, 371285221787726453, 371285221890232633, 371285221893068222, 371285221802948030, 371285221680542134]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 81870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 81800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488138947587163, 362488239684865137⟩, ⟨(-252712531446871680), (-247142221200551864)⟩, true⟩

def words08 : List Nat := [371285221556846511, 371285221549609139, 371285221531259983, 371285221598762873, 371285221640283507, 371285221643168778, 371285221575333153, 371285221593344252, 371285221703888954, 371285221743684781]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 81880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 81800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483262762872871, 362483363526016328⟩, ⟨146623534374406309, 152195962868075517⟩, true⟩

def words09 : List Nat := [371285221779902868, 371285221817030829, 371285221914474720, 371285221938602407, 371285221967560314, 371285221997618916, 371285222026676250, 371285222029512508, 371285221859674555, 371285221840581262]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 81890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 81800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 81800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk818B
