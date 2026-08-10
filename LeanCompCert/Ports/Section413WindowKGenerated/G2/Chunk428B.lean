import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk428A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk428B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk428A

def state06 : KState := ⟨⟨360652506158143054, 360652517537264201⟩, ⟨(-2986606641806266991), (-2986277045299595895)⟩, true⟩

def words05 : List Nat := [360582834927614127, 360582835454574808, 360582836526126039, 360582837612380994, 360582838240542461, 360582838868724083, 360582839676058329, 360582840757790459, 360582842383946068, 360582844010157984]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 42850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 42800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360634531853086456, 360634543237778205⟩, ⟨(-2216319609248646448), (-2215989773958324194)⟩, true⟩

def words06 : List Nat := [360582845173639637, 360582846054253677, 360582847479273668, 360582848904399813, 360582850188609811, 360582850931331499, 360582851256537892, 360582851581794581, 360582852316329231, 360582853522727044]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 42860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 42800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360627877183955324, 360627888574151202⟩, ⟨(-1930935903449386954), (-1930605832169741642)⟩, true⟩

def words07 : List Nat := [360582855067236641, 360582856611786653, 360582857855362359, 360582859263717362, 360582860301315288, 360582861339016775, 360582862741098707, 360582864066106547, 360582865116639186, 360582866167207107]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 42870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 42800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360628977964889829, 360628989360609867⟩, ⟨(-1977999364776549455), (-1977669056593096575)⟩, true⟩

def words08 : List Nat := [360582867633693944, 360582869521175530, 360582871375047569, 360582873228943793, 360582874615009958, 360582875693867641, 360582876926764512, 360582878159772900, 360582879099883631, 360582880175545563]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 42880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 42800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360619208633077350, 360619220034367136⟩, ⟨(-1558993652919870001), (-1558663105823373453)⟩, true⟩

def words09 : List Nat := [360582880822916775, 360582881470319748, 360582882474538264, 360582883752036209, 360582884737350987, 360582885722724563, 360582886409013073, 360582886712959364, 360582887560362904, 360582888407928980]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 42890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 42800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 42800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk428B
