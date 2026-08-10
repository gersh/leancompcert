import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk854A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk854B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk854A

def state06 : KState := ⟨⟨360580879404367233, 360580927219097963⟩, ⟨121751814826863589, 124511351179560713⟩, true⟩

def words05 : List Nat := [360582384433964823, 360582384412306513, 360582384504109925, 360582384505338030, 360582384483364034, 360582384342883890, 360582384202149940, 360582384188602307, 360582384189604583, 360582384173827422]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 85450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 85400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360577678833790081, 360577726660240064⟩, ⟨395170405492274436, 397930943426631802⟩, true⟩

def words06 : List Nat := [360582384157873640, 360582384063993771, 360582383990147166, 360582383871014846, 360582383751546941, 360582383597751975, 360582383336187544, 360582382997509207, 360582382658601647, 360582382456933953]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 85460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 85400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360548253875095908, 360548301713097484⟩, ⟨2910331372497652303, 2913092897806196203⟩, true⟩

def words07 : List Nat := [360582382459018233, 360582382515808915, 360582382516913573, 360582382505509329, 360582382357033477, 360582382130427688, 360582381903480045, 360582381673135203, 360582381344224346, 360582380946810706]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 85470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 85400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360562077586330841, 360562125435927982⟩, ⟨1728565484447350986, 1731328001001038924⟩, true⟩

def words08 : List Nat := [360582380549136561, 360582380117726330, 360582379754755165, 360582379493928418, 360582379232990713, 360582378845679691, 360582378321303033, 360582377934029760, 360582377546398453, 360582377254865882]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 85480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 85400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360561886286106380, 360561934147434846⟩, ⟨1744849649921432642, 1747613169440156668⟩, true⟩

def words09 : List Nat := [360582377019103599, 360582376665832981, 360582376312328608, 360582375960771600, 360582375677790435, 360582375360550514, 360582375043183927, 360582374657333796, 360582374305191655, 360582374067545258]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 85490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 85400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 85400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk854B
