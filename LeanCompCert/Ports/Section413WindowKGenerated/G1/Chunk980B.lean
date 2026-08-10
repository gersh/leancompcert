import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk980A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk980B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk980A

def state06 : KState := ⟨⟨362503882566781422, 362504029037257206⟩, ⟨(-1840749945910950412), (-1831052861455051924)⟩, true⟩

def words05 : List Nat := [371285355119665208, 371285355234191761, 371285355433320718, 371285355540402028, 371285355629611892, 371285355719975151, 371285355912884788, 371285356060088400, 371285356252863242, 371285356447119893]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 98050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 98000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487597540517140, 362487744042086405⟩, ⟨(-243805504524964197), (-234105370883251665)⟩, true⟩

def words06 : List Nat := [371285356639906244, 371285356694941296, 371285356791944166, 371285356890781219, 371285356992996778, 371285356996440367, 371285356960187683, 371285356914312922, 371285356912862977, 371285356941201503]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 98060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 98000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362480787886386863, 362480934418992530⟩, ⟨424082271358879165, 433785448896202469⟩, true⟩

def words07 : List Nat := [371285357056547683, 371285357173350186, 371285357275480763, 371285357278924786, 371285357242286793, 371285357239377099, 371285357270745081, 371285357274200165, 371285357231871825, 371285357190698242]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 98070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 98000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486927702938112, 362487074266363726⟩, ⟨(-178105414894531340), (-168399214381116816)⟩, true⟩

def words08 : List Nat := [371285357206845461, 371285357217649270, 371285357312664444, 371285357409116539, 371285357494876454, 371285357498321000, 371285357445209276, 371285357429675295, 371285357480094500, 371285357501172413]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 98080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 98000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362495418626882266, 362495565221737825⟩, ⟨(-1011045531178622523), (-1001336247546502461)⟩, true⟩

def words09 : List Nat := [371285357503819142, 371285357504402453, 371285357594632595, 371285357637575718, 371285357691153324, 371285357746092522, 371285357797220175, 371285357809878042, 371285357916264715, 371285358024588495]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 98090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 98000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 98000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk980B
