import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk830A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk830B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk830A

def state06 : KState := ⟨⟨362496929910496405, 362497033660269179⟩, ⟨(-979712328523375629), (-973893558164866191)⟩, true⟩

def words05 : List Nat := [371285308099878618, 371285308176438944, 371285308347349496, 371285308350228880, 371285308343883263, 371285308309656031, 371285308333312120, 371285308336485651, 371285308475768552, 371285308620140059]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 83050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 83000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489865972129111, 362489969747935469⟩, ⟨(-392951675619348535), (-387130742778820111)⟩, true⟩

def words06 : List Nat := [371285308735303702, 371285308757763907, 371285308924230205, 371285309092211762, 371285309285833744, 371285309312347510, 371285309337827161, 371285309364259356, 371285309449155890, 371285309508588660]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 83060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 83000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485668655687935, 362485772457456360⟩, ⟨(-44198374659153742), (-38375285023508292)⟩, true⟩

def words07 : List Nat := [371285309711606961, 371285309915856384, 371285310118773554, 371285310149604506, 371285310222164066, 371285310296178827, 371285310513612189, 371285310538830118, 371285310546571379, 371285310555396642]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 83070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 83000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489161275794910, 362489265103379683⟩, ⟨(-334381699598639192), (-328556465008725240)⟩, true⟩

def words08 : List Nat := [371285310693518014, 371285310766452572, 371285310840982839, 371285310916600406, 371285310969669564, 371285310972550146, 371285310832250100, 371285310800374174, 371285310876431570, 371285310927054826]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 83080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 83000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362490747006848635, 362490850860628623⟩, ⟨(-466111802198121671), (-460284390914479933)⟩, true⟩

def words09 : List Nat := [371285310976535682, 371285311026962193, 371285311221118596, 371285311365638534, 371285311553217561, 371285311741946478, 371285311900561592, 371285311903442593, 371285311935415666, 371285312005609857]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 83090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 83000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 83000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk830B
