import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk882

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360585045077460448, 360585096131806853⟩, ⟨(-260468379868631677), (-257427522687375859)⟩, true⟩

def state01 : KState := ⟨⟨360568738014464900, 360568789080767877⟩, ⟨1177900962486395121, 1180942874297122135⟩, true⟩

def words00 : List Nat := [360582177626570456, 360582177639447665, 360582177640579806, 360582177589146061, 360582177537513056, 360582177377171444, 360582177293707190, 360582177207492388, 360582177121159834, 360582176937862279]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 88200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 88200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360595248100307391, 360595299178608966⟩, ⟨(-1160698848249344020), (-1157655877982537426)⟩, true⟩

def words01 : List Nat := [360582176787118766, 360582176765075360, 360582176762779429, 360582176787514031, 360582176788686234, 360582176704382456, 360582176619839231, 360582176653013352, 360582176802788827, 360582176952857926]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 88210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 88200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591214454878197, 360591265545288616⟩, ⟨(-804950341571927928), (-801906303002515818)⟩, true⟩

def words02 : List Nat := [360582177004000069, 360582177005271174, 360582176977818703, 360582177029122688, 360582177046798624, 360582177048070720, 360582176991103433, 360582176870186985, 360582176749005706, 360582176831537185]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 88220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 88200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360558301092918701, 360558352195293819⟩, ⟨2099162943579940198, 2102208037854470878⟩, true⟩

def words03 : List Nat := [360582176893769385, 360582176956232487, 360582176957365038, 360582176955552256, 360582176853003445, 360582176662357747, 360582176471324912, 360582176408788558, 360582176217797652, 360582175949122633]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 88230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 88200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360569004292921583, 360569055407317799⟩, ⟨1154750613835386486, 1157796768908218778⟩, true⟩

def words04 : List Nat := [360582175680165240, 360582175539863396, 360582175597544968, 360582175676093215, 360582175677277741, 360582175635183382, 360582175464553469, 360582175283635597, 360582175102366544, 360582174917447071]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 88240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 88200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360553321967098414, 360553373093600539⟩, ⟨2538771383084583675, 2541818606565499853⟩, true⟩

def words05 : List Nat := [360582174769920194, 360582174540196686, 360582174310241873, 360582174067441590, 360582173889166631, 360582173649996042, 360582173410676467, 360582173085697301, 360582172632214288, 360582172307361762]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 88250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 88200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360559580556055092, 360559631694551727⟩, ⟨1986298801368977284, 1989347083544274000⟩, true⟩

def words06 : List Nat := [360582171982093738, 360582171785271263, 360582171460084547, 360582171038874702, 360582170617454629, 360582170146321139, 360582169749086051, 360582169442013701, 360582169134809605, 360582168763584743]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 88260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 88200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360577913152253066, 360577964302747023⟩, ⟨367991948867290113, 371041290105818963⟩, true⟩

def words07 : List Nat := [360582168509296111, 360582168353694562, 360582168197710191, 360582168118840402, 360582168054220871, 360582167864647049, 360582167674850545, 360582167482404272, 360582167354139247, 360582167307845639]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 88270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 88200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360577139321586878, 360577190484206474⟩, ⟨436184850326886813, 439235262075385025⟩, true⟩

def words08 : List Nat := [360582167261383238, 360582167123332667, 360582166911982397, 360582166739400041, 360582166566459748, 360582166361489430, 360582166136982178, 360582165848432439, 360582165559644296, 360582165399395911]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 88280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 88200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360556159670123294, 360556210844741017⟩, ⟨2288569093654512323, 2291620564777113699⟩, true⟩

def words09 : List Nat := [360582165344095333, 360582165286039732, 360582165227849123, 360582165091926225, 360582164859318069, 360582164594830815, 360582164329977632, 360582164033932150, 360582163805118168, 360582163512518788]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 88290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 88200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 88200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk882
