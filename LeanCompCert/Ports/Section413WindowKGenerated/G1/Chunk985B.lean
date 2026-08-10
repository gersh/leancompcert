import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk985A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk985B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk985A

def state06 : KState := ⟨⟨362474503161771688, 362474651187528352⟩, ⟨1044554913644107946, 1054404898219043868⟩, true⟩

def words05 : List Nat := [371285349443487786, 371285349535571193, 371285349611020310, 371285349614481757, 371285349552486274, 371285349504576908, 371285349489865971, 371285349493327621, 371285349393682105, 371285349289174244]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 98550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 98500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487999863918855, 362488147920613815⟩, ⟨(-285710902985794869), (-275857868971247729)⟩, true⟩

def words06 : List Nat := [371285349182978057, 371285349181228582, 371285349172643238, 371285349222391657, 371285349255286887, 371285349258774981, 371285349218342287, 371285349222344442, 371285349318379164, 371285349350355106]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 98560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 98500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362490350854355122, 362490498942555390⟩, ⟨(-517451836126220012), (-507595696474325242)⟩, true⟩

def words07 : List Nat := [371285349352962406, 371285349355286979, 371285349457766896, 371285349525796547, 371285349624274578, 371285349724121847, 371285349822306452, 371285349825773913, 371285349864486456, 371285349920974413]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 98570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 98500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484204349000762, 362484352468056227⟩, ⟨88507913475498723, 98367094995905323⟩, true⟩

def words08 : List Nat := [371285350018209922, 371285350024356788, 371285350026951344, 371285350020903325, 371285350034649243, 371285350038501536, 371285350076198659, 371285350145588604, 371285350203541936, 371285350207127086]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 98580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 98500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362494420158923269, 362494568309308773⟩, ⟨(-918734856786607767), (-908872586285235349)⟩, true⟩

def words09 : List Nat := [371285350264875648, 371285350334606716, 371285350455171454, 371285350458634490, 371285350442474475, 371285350403202889, 371285350422452671, 371285350434821837, 371285350530657998, 371285350628085609]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 98590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 98500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 98500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk985B
