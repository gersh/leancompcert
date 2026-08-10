import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk882A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk882B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk882A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk882B
