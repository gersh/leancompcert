import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk187A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk187B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk187A

def state06 : KState := ⟨⟨360575067481508014, 360575069512586111⟩, ⟨196157161533955727, 196182951327016371⟩, true⟩

def words05 : List Nat := [360585505182217613, 360585513003542748, 360585518510004312, 360585521189911268, 360585521852417307, 360585522514916569, 360585526010082714, 360585527582983604, 360585527583197836, 360585527025983074]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 18750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 18700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360677113558935112, 360677115592269957⟩, ⟨(-1718668244817999979), (-1718642412677084521)⟩, true⟩

def words06 : List Nat := [360585527854549571, 360585531082240737, 360585535792224789, 360585540501752352, 360585542777644960, 360585544696693569, 360585546442440324, 360585548188068457, 360585552330824874, 360585557208983128]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 18760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 18700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360700680961907008, 360700682997520660⟩, ⟨(-2161088006472274633), (-2161062131546998575)⟩, true⟩

def words07 : List Nat := [360585560662328672, 360585564115334116, 360585570395394123, 360585578967297763, 360585586773758745, 360585594579427016, 360585600179789857, 360585604338363899, 360585610466281819, 360585616593625927]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 18770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 18700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360651329016831638, 360651331054702533⟩, ⟨(-1234331910550940622), (-1234305993223170056)⟩, true⟩

def words08 : List Nat := [360585622626261391, 360585625841919967, 360585627621936828, 360585629401788457, 360585629401990406, 360585630399283555, 360585634587037921, 360585638774397912, 360585641539115563, 360585645035160031]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 18780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 18700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360686991452900953, 360686993493033617⟩, ⟨(-1904833208518442425), (-1904807248681014425)⟩, true⟩

def words09 : List Nat := [360585648019400421, 360585651003395137, 360585656808746169, 360585659800208976, 360585660126870712, 360585660453513036, 360585663600757841, 360585668568462027, 360585673958280950, 360585679347579598]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 18790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 18700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 18700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk187B
