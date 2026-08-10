import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk891A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360554260013851930, 360554312156423382⟩, ⟨2470052176044887597, 2473189505256020913⟩, true⟩

def state01 : KState := ⟨⟨360574729854107960, 360574782008785180⟩, ⟨646068083648861354, 649206491544384496⟩, true⟩

def words00 : List Nat := [360582069303905135, 360582069119457361, 360582068957860404, 360582068699874086, 360582068441684100, 360582068131862510, 360582067884841107, 360582067763842245, 360582067642716763, 360582067459257006]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 89100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 89100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360587582956213091, 360587635123010553⟩, ⟨(-499366138508335386), (-496226650516798862)⟩, true⟩

def words01 : List Nat := [360582067378545480, 360582067317529147, 360582067319459992, 360582067342434833, 360582067343625456, 360582067258887175, 360582067173923570, 360582067048596679, 360582067048851390, 360582067112659269]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 89110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 89100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580938126025448, 360580990305059976⟩, ⟨92799955300296322, 95940533920204482⟩, true⟩

def words02 : List Nat := [360582067113804289, 360582067104338675, 360582067171055135, 360582067268200202, 360582067285656745, 360582067286941752, 360582067178762916, 360582067006135791, 360582066833262330, 360582066716301087]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 89120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 89100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360561374328783852, 360561426519930178⟩, ⟨1836573612766572175, 1839715270972505173⟩, true⟩

def words03 : List Nat := [360582066705284421, 360582066634484013, 360582066563553598, 360582066383739997, 360582066130016625, 360582065844940224, 360582065559479334, 360582065399984345, 360582065243186789, 360582065012985737]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 89130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 89100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360584902924778089, 360584955128057934⟩, ⟨(-260895541835188323), (-257752801989392341)⟩, true⟩

def words04 : List Nat := [360582064782503200, 360582064590037759, 360582064465681940, 360582064433496910, 360582064401235955, 360582064254399532, 360582064067426228, 360582063984053023, 360582063900679887, 360582063934442727]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 89140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 89100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk891A
