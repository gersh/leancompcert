import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk818

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362497342547911220, 362497443055483355⟩, ⟨(-1005270688805218996), (-999719178853090508)⟩, true⟩

def state01 : KState := ⟨⟨362478772309572482, 362478872842755715⟩, ⟨513888253424990467, 519441858494598953⟩, true⟩

def words00 : List Nat := [371285221835611416, 371285221849031687, 371285221999546368, 371285222151505003, 371285222347839596, 371285222350672527, 371285222347985525, 371285222297972033, 371285222246815682, 371285222211518637]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 81800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 81800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479801556983770, 362479902115631653⟩, ⟨429708847562228398, 435264536027680188⟩, true⟩

def words01 : List Nat := [371285222164636497, 371285222196488874, 371285222227334815, 371285222230174217, 371285222105824610, 371285222028740623, 371285222018935741, 371285222021788364, 371285221959161235, 371285221897299066]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 81810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 81800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480942131744693, 362481042715793027⟩, ⟨336407661316935880, 341965428178868906⟩, true⟩

def words02 : List Nat := [371285221863277276, 371285221866414911, 371285221875539718, 371285221912998324, 371285221927851372, 371285221930685144, 371285221761329630, 371285221720196012, 371285221686633303, 371285221689618994]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 81820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 81800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484993128269902, 362485093738165926⟩, ⟨4883894525863632, 10443776628663418⟩, true⟩

def words03 : List Nat := [371285221640668904, 371285221592638176, 371285221571212801, 371285221574340425, 371285221541504689, 371285221537016694, 371285221531655364, 371285221497222995, 371285221348276191, 371285221350294820]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 81830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 81800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482816093527569, 362482916728642752⟩, ⟨183079000058102533, 188640946229330479⟩, true⟩

def words04 : List Nat := [371285221479366996, 371285221482201392, 371285221429636495, 371285221378007734, 371285221325264870, 371285221319444868, 371285221303944651, 371285221372985878, 371285221440991781, 371285221443929611]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 81840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 81800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk818
