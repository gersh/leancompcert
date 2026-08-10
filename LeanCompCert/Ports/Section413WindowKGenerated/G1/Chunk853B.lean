import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk853A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk853B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk853A

def state06 : KState := ⟨⟨362468515629789215, 362468625436074796⟩, ⟨1416325931268804338, 1422654755324067488⟩, true⟩

def words05 : List Nat := [371285293157863608, 371285293127365397, 371285293095841696, 371285293054488645, 371285292829318980, 371285292636402667, 371285292441957410, 371285292335423513, 371285292155055404, 371285291963199024]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 85350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 85300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481080590826740, 362481190423596901⟩, ⟨343758947008678834, 350090031928110528⟩, true⟩

def words06 : List Nat := [371285291769962951, 371285291715130619, 371285291613683158, 371285291633714717, 371285291636072142, 371285291623136762, 371285291426362409, 371285291332248855, 371285291276001299, 371285291279072222]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 85360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 85300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477409955850898, 362477519815668478⟩, ⟨657174295456766873, 663507689547336233⟩, true⟩

def words07 : List Nat := [371285291233279709, 371285291171139899, 371285291153551612, 371285291156866590, 371285291195705515, 371285291239180244, 371285291276556265, 371285291279522910, 371285291133891803, 371285291046513493]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 85370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 85300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481664842554559, 362481774728784343⟩, ⟨293902905694802197, 300238554997841115⟩, true⟩

def words08 : List Nat := [371285291003564073, 371285291006551050, 371285290931695535, 371285290854216501, 371285290775560505, 371285290740138724, 371285290713350844, 371285290762897951, 371285290811378280, 371285290814450087]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 85380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 85300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481645830743168, 362481755743871170⟩, ⟨295517099513415255, 301855045787768073⟩, true⟩

def words09 : List Nat := [371285290820992483, 371285290870317529, 371285290935573513, 371285290938540882, 371285290821268294, 371285290682837100, 371285290543236049, 371285290496024186, 371285290384245484, 371285290346280863]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 85390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 85300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 85300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk853B
