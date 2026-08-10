import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk622A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk622B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk622A

def state06 : KState := ⟨⟨360583289496986317, 360583314247889711⟩, ⟨(-40264512492400532), (-39223512568842058)⟩, true⟩

def words05 : List Nat := [360582683175647595, 360582683514643769, 360582683724707306, 360582683849020947, 360582683907397941, 360582683966004476, 360582684099968768, 360582684240698926, 360582684251596031, 360582684262624958]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 62250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 62200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360603867597785904, 360603892356929341⟩, ⟨(-1321608279513130915), (-1320566766523447253)⟩, true⟩

def words06 : List Nat := [360582684393875881, 360582684654740495, 360582684920629559, 360582685186675637, 360582685202178700, 360582685203052498, 360582685037880061, 360582685047426432, 360582685245589830, 360582685587060166]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 62260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 62200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360575369942310157, 360575394709790066⟩, ⟨453154098647428429, 454196130789287015⟩, true⟩

def words07 : List Nat := [360582685675439199, 360582685763911004, 360582686109906419, 360582686618068729, 360582687000957075, 360582687383974433, 360582687637274659, 360582687638148553, 360582687634662768, 360582687518569599]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 62270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 62200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360599473906088645, 360599498681799810⟩, ⟨(-1048148341320569900), (-1047105796494526368)⟩, true⟩

def words08 : List Nat := [360582687466240455, 360582687614138092, 360582687614920293, 360582687600674502, 360582687586285372, 360582687626895709, 360582687963518811, 360582688300300923, 360582688505963417, 360582688776733356]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 62280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 62200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360614505655248514, 360614530439219868⟩, ⟨(-1984654328210278634), (-1983611268815670752)⟩, true⟩

def words09 : List Nat := [360582689252153311, 360582689727815273, 360582690067723271, 360582690151155261, 360582690151961258, 360582690017389824, 360582690004708735, 360582690259276873, 360582690771061928, 360582691283045559]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 62290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 62200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 62200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk622B
