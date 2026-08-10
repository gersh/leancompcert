import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk776A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk776B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk776A

def state06 : KState := ⟨⟨360607577834378714, 360607617026153417⟩, ⟨(-1977321233472449346), (-1975265559480762892)⟩, true⟩

def words05 : List Nat := [360582181605210569, 360582181735601504, 360582181872884004, 360582181914276569, 360582181915299901, 360582181818119153, 360582181746363318, 360582181909569171, 360582182237984433, 360582182566650182]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 77650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 77600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360602871958615022, 360602911160942993⟩, ⟨(-1611913171035624110), (-1609856677424288058)⟩, true⟩

def words06 : List Nat := [360582182811369223, 360582183081058909, 360582183446927457, 360582183813111396, 360582184063759763, 360582184149206541, 360582184151668097, 360582184154250349, 360582184280853322, 360582184548984550]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 77660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 77600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360562103740592673, 360562142953379244⟩, ⟨1554775798172960298, 1556833104155634004⟩, true⟩

def words07 : List Nat := [360582184776259460, 360582185003755280, 360582185115172654, 360582185116281585, 360582185113832492, 360582185016456402, 360582184956492387, 360582184957601197, 360582184831042376, 360582184574184544]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 77670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 77600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360620809524961576, 360620848748216209⟩, ⟨(-3005801653831929805), (-3003743534639149153)⟩, true⟩

def words08 : List Nat := [360582184317082120, 360582184261406405, 360582184426728616, 360582184592258796, 360582184616161762, 360582184685067263, 360582184919177691, 360582185153624814, 360582185553158098, 360582186051962600]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 77680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 77600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360603027836619449, 360603067070448631⟩, ⟨(-1624305131085216751), (-1622246190305546341)⟩, true⟩

def words09 : List Nat := [360582186432341746, 360582186812828615, 360582187105843911, 360582187507586436, 360582187828480607, 360582188149546892, 360582188365787669, 360582188470207054, 360582188739811745, 360582189009801979]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 77690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 77600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 77600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk776B
