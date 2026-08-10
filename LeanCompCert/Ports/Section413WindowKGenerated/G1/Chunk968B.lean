import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk968A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk968B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk968A

def state06 : KState := ⟨⟨362502331631701071, 362502474404365572⟩, ⟨(-1671065782452756225), (-1661729091827263587)⟩, true⟩

def words05 : List Nat := [371285317113684106, 371285317298405748, 371285317557755203, 371285317689466941, 371285317784632502, 371285317880867648, 371285318082434187, 371285318232136842, 371285318411604256, 371285318592513256]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 96850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 96800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362503254217084321, 362503397020406804⟩, ⟨(-1760471823149105015), (-1751132162835364419)⟩, true⟩

def words06 : List Nat := [371285318771880403, 371285318841839980, 371285318980696969, 371285319121353566, 371285319292239949, 371285319422687675, 371285319542874310, 371285319664152538, 371285319880544758, 371285320071032530]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 96860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 96800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362492131270176537, 362492274104186449⟩, ⟨(-682891593933666211), (-673548960779402819)⟩, true⟩

def words07 : List Nat := [371285320355892815, 371285320642161798, 371285320907955186, 371285321032462856, 371285321184047134, 371285321337336496, 371285321543239795, 371285321621317277, 371285321695621734, 371285321771316440]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 96870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 96800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487070772320205, 362487213636718072⟩, ⟨(-192565351908784289), (-183219774613406917)⟩, true⟩

def words08 : List Nat := [371285321923599764, 371285322028859844, 371285322175795492, 371285322324075522, 371285322453897224, 371285322457296390, 371285322492828039, 371285322535598919, 371285322625101027, 371285322648136951]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 96880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 96800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362486058164233133, 362486201059568222⟩, ⟨(-94405960260561627), (-85057385303901273)⟩, true⟩

def words09 : List Nat := [371285322669781750, 371285322692544552, 371285322820620006, 371285322911926562, 371285323033726194, 371285323156875800, 371285323278416498, 371285323281815854, 371285323270174945, 371285323283432745]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 96890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 96800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 96800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk968B
