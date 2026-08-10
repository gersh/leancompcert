import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk745A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk745B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk745A

def state06 : KState := ⟨⟨360556740206207398, 360556776215656576⟩, ⟨1901107699659716372, 1902921131078392598⟩, true⟩

def words05 : List Nat := [360582299127160611, 360582299337792598, 360582299458356770, 360582299459417475, 360582299400159424, 360582299200699890, 360582299000935932, 360582298797341849, 360582298567742850, 360582298226534774]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 74550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 74500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360592491189937655, 360592527209398807⟩, ⟨(-764605440030270818), (-762791262068654694)⟩, true⟩

def words06 : List Nat := [360582297885095464, 360582297723596240, 360582297817386744, 360582297938018983, 360582297939006647, 360582297907722287, 360582297854929860, 360582297919072848, 360582298010740317, 360582298149012482]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 74560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 74500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360587033263385759, 360587069292966590⟩, ⟨(-357578093256276535), (-355763160622266543)⟩, true⟩

def words07 : List Nat := [360582298149974719, 360582298133096809, 360582298277633623, 360582298532620523, 360582298693740132, 360582298855025775, 360582298926326123, 360582299004873544, 360582299069696254, 360582299134875089]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 74570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 74500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360580496619357180, 360580532658917019⟩, ⟨129915487645636138, 131731164565297820⟩, true⟩

def words08 : List Nat := [360582299253138236, 360582299254199496, 360582299243000245, 360582299141288568, 360582299039422155, 360582298814209744, 360582298742410655, 360582298796890938, 360582298797838207, 360582298728960796]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 74580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 74500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360603152111679530, 360603188161275607⟩, ⟨(-1560087307885858313), (-1558270882313427791)⟩, true⟩

def words09 : List Nat := [360582298710339802, 360582298715733062, 360582298851849441, 360582299020054593, 360582299035059415, 360582299050149191, 360582299244475863, 360582299529665183, 360582299810546764, 360582300091647675]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 74590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 74500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 74500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk745B
