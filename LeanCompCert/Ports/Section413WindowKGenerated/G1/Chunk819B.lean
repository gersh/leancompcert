import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk819A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk819B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk819A

def state06 : KState := ⟨⟨362491046971989565, 362491147888481831⟩, ⟨(-491034687110902565), (-485449694718854001)⟩, true⟩

def words05 : List Nat := [371285224054117271, 371285224089329696, 371285224272222936, 371285224397854018, 371285224550805916, 371285224704868034, 371285224840518583, 371285224843358269, 371285224877438568, 371285224953247771]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 81950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 81900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483291931770111, 362483392873572155⟩, ⟨144588081723946764, 150175148636931772⟩, true⟩

def words06 : List Nat := [371285225103289088, 371285225106127954, 371285225074218878, 371285225013762537, 371285224952253205, 371285224908282729, 371285224853043525, 371285224902004176, 371285224945104730, 371285224948094992]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 81960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 81900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362504532219704792, 362504633187134287⟩, ⟨(-1596565635975753721), (-1590976468251891997)⟩, true⟩

def words07 : List Nat := [371285225054157053, 371285225184070885, 371285225461309995, 371285225587209683, 371285225691288850, 371285225796272428, 371285225955482557, 371285226059876561, 371285226298532443, 371285226538419928]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 81970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 81900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487361843063702, 362487462836129599⟩, ⟨(-188904340715836899), (-183313071192381829)⟩, true⟩

def words08 : List Nat := [371285226776997592, 371285226832656942, 371285226931138866, 371285227031179052, 371285227163593926, 371285227166433511, 371285227100673226, 371285227035804015, 371285227034942896, 371285227065481694]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 81980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 81900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478828026624819, 362478929045318546⟩, ⟨510822734989859349, 516416105867608583⟩, true⟩

def words09 : List Nat := [371285227101813883, 371285227139279225, 371285227171378177, 371285227174237326, 371285227073272237, 371285226988272242, 371285226948211222, 371285226951100741, 371285226876275398, 371285226802707176]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 81990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 81900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 81900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk819B
