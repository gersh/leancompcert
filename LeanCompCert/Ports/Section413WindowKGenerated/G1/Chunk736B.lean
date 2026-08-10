import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk736A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk736B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk736A

def state06 : KState := ⟨⟨362479033043307589, 362479113886805518⟩, ⟨451301757428599277, 455323280113507251⟩, true⟩

def words05 : List Nat := [371285295505362018, 371285295543798863, 371285295581918134, 371285295584493537, 371285295469021940, 371285295410974522, 371285295454768453, 371285295457311936, 371285295386312604, 371285295305215965]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 73650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 73600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362471287051463277, 362471367917641980⟩, ⟨1021925493479546397, 1025948686947930523⟩, true⟩

def words06 : List Nat := [371285295223050613, 371285295173286993, 371285295030131583, 371285295023986450, 371285295017035080, 371285294984445546, 371285294705560741, 371285294491605014, 371285294276320269, 371285294192746473]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 73660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 73600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362481583686000557, 362481664575260957⟩, ⟨263314727527885867, 267339621542690751⟩, true⟩

def words07 : List Nat := [371285294005614749, 371285293817980048, 371285293629297235, 371285293625748932, 371285293529759903, 371285293440634068, 371285293350678915, 371285293240789910, 371285293009249081, 371285292963175489]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 73670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 73600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481300160668555, 362481381072501686⟩, ⟨284283040133070478, 288309597423984808⟩, true⟩

def words08 : List Nat := [371285293050406186, 371285293073120673, 371285293096166230, 371285293120037373, 371285293199039188, 371285293201829875, 371285293327583921, 371285293469413737, 371285293535579888, 371285293538201564]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 73680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 73600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362500862896169525, 362500943830886671⟩, ⟨(-1157395201901730503), (-1153366958176403339)⟩, true⟩

def words09 : List Nat := [371285293584324646, 371285293684855938, 371285293968000959, 371285294006637109, 371285294008602230, 371285293999568037, 371285294098916246, 371285294130152361, 371285294344213446, 371285294559395424]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 73690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 73600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 73600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk736B
