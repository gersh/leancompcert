import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk264A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk264B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk264A

def state06 : KState := ⟨⟨360558172646607781, 360558176812207841⟩, ⟨649143485376897698, 649218042817640826⟩, true⟩

def words05 : List Nat := [360582715267618919, 360582715719365468, 360582716134186642, 360582717267306536, 360582717267600586, 360582717058476038, 360582716849329622, 360582715920578532, 360582713568399190, 360582712641490443]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 26450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 26400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360521471308223314, 360521475477092167⟩, ⟨1620486260942615363, 1620560904892213063⟩, true⟩

def words06 : List Nat := [360582711714526543, 360582711706485772, 360582710789303646, 360582709153218527, 360582707517200717, 360582705242992722, 360582704055372426, 360582702385233964, 360582700715186033, 360582698027333656]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 26460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 26400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360592815843457817, 360592820015603570⟩, ⟨(-268394208229701821), (-268319477524143783)⟩, true⟩

def words07 : List Nat := [360582695714798858, 360582694420390799, 360582693125979566, 360582692480406878, 360582692322636762, 360582690927209666, 360582689531823883, 360582687761703020, 360582687104461463, 360582687487469280]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 26470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 26400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360600629822030496, 360600633997491140⟩, ⟨(-475826894029636330), (-475752075529596166)⟩, true⟩

def words08 : List Nat := [360582687487785769, 360582686616326097, 360582684323860873, 360582682999966090, 360582681676079658, 360582679986565816, 360582678755858502, 360582676800492492, 360582674845199492, 360582674989694923]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 26480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 26400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360540587188338556, 360540591367072242⟩, ⟨1115204612959186581, 1115279518178735469⟩, true⟩

def words09 : List Nat := [360582676587778054, 360582678185807004, 360582679067122775, 360582679554082751, 360582679554378896, 360582679053978876, 360582679473513091, 360582679473860844, 360582678974477472, 360582677386626157]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 26490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 26400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 26400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk264B
