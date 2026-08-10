import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk699A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk699B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk699A

def state06 : KState := ⟨⟨360573309837031117, 360573341380556155⟩, ⟨644466569647036910, 645957176499497566⟩, true⟩

def words05 : List Nat := [360582577304877411, 360582576944061375, 360582576583069864, 360582576282344804, 360582576100276786, 360582575795581860, 360582575490796809, 360582575082157768, 360582574747198064, 360582574616355176]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 69950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 69900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360558531894611294, 360558563447456008⟩, ⟨1678385176469639587, 1679876435373263583⟩, true⟩

def words06 : List Nat := [360582574485811615, 360582574486802317, 360582574284250591, 360582573979914021, 360582573675439122, 360582573229116690, 360582572932393848, 360582572648703201, 360582572364912837, 360582571971614552]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 69960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 69900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360552277508024911, 360552309070238021⟩, ⟨2116059037981855224, 2117550952436859022⟩, true⟩

def words07 : List Nat := [360582571629300077, 360582571319568264, 360582571009532387, 360582570861822497, 360582570584073953, 360582570130905011, 360582569677561809, 360582569221819575, 360582568875045893, 360582568443665242]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 69970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 69900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360550616564482620, 360550648136129434⟩, ⟨2232249123042871992, 2233741697716426376⟩, true⟩

def words08 : List Nat := [360582568012154169, 360582567478917756, 360582566915939015, 360582566491941247, 360582566067681756, 360582565592396013, 360582565122802380, 360582564521773501, 360582563920575423, 360582563291118953]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 69980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 69900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360535467402754303, 360535498983749457⟩, ⟨3292658543057464593, 3294151772067183613⟩, true⟩

def words09 : List Nat := [360582562835931005, 360582562584537943, 360582562333069292, 360582561882546092, 360582561283190922, 360582560632931661, 360582559982397849, 360582559535626639, 360582558966019272, 360582558294778989]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 69990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 69900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 69900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk699B
