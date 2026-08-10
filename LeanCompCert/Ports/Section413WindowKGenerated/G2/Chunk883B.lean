import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk883A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk883B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk883A

def state06 : KState := ⟨⟨360563556444246962, 360563607691099781⟩, ⟨1636102908941736798, 1639160760587912054⟩, true⟩

def words05 : List Nat := [360582159332787501, 360582159339613434, 360582159340758114, 360582159283736401, 360582159229661998, 360582159113875327, 360582158997716595, 360582158981087281, 360582158836360657, 360582158627729341]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 88350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 88300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360569769490970392, 360569820749861253⟩, ⟨1087027270848820791, 1090086186235958991⟩, true⟩

def words06 : List Nat := [360582158418836495, 360582158156816837, 360582157959140547, 360582157736349532, 360582157513465186, 360582157174831718, 360582156853580371, 360582156626343407, 360582156398715377, 360582156227808928]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 88360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 88300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360566965365345001, 360567016636366740⟩, ⟨1334845886784017273, 1337905874235415665⟩, true⟩

def words07 : List Nat := [360582156089367717, 360582155886903129, 360582155684199254, 360582155574030158, 360582155574317156, 360582155477705899, 360582155380958023, 360582155211017289, 360582154912932891, 360582154743113011]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 88370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 88300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360563941106547109, 360563992389578592⟩, ⟨1602177646138645562, 1605238695070766674⟩, true⟩

def words08 : List Nat := [360582154572860728, 360582154481369538, 360582154425627235, 360582154281576509, 360582154137328499, 360582153910566962, 360582153747778201, 360582153618683218, 360582153489481998, 360582153252742647]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 88380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 88300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360587012073817911, 360587063368875359⟩, ⟨(-437217279151142483), (-434155167186805387)⟩, true⟩

def words09 : List Nat := [360582153048311532, 360582152945808908, 360582152842933702, 360582152815395985, 360582152688619639, 360582152450482469, 360582152212074615, 360582152101826390, 360582152109997941, 360582152166884581]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 88390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 88300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 88300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk883B
