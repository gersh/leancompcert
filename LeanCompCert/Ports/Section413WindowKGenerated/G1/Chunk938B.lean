import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk938A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk938B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk938A

def state06 : KState := ⟨⟨362491005789682290, 362491139530013811⟩, ⟨(-570233740960982535), (-561758449748481911)⟩, true⟩

def words05 : List Nat := [371285154379302623, 371285154391730518, 371285154504145219, 371285154507431166, 371285154481559060, 371285154438997855, 371285154420347996, 371285154423969457, 371285154458675926, 371285154526127762]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 93850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 93800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469670729747351, 362469804499762675⟩, ⟨1432345842107843358, 1440823919593453988⟩, true⟩

def words06 : List Nat := [371285154592747375, 371285154596033902, 371285154525188420, 371285154455978545, 371285154385114193, 371285154349794513, 371285154162382980, 371285153969953238, 371285153776218628, 371285153641337124]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 93860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 93800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362466569632405770, 362466703432020222⟩, ⟨1723525426338660138, 1732006282448348238⟩, true⟩

def words07 : List Nat := [371285153480051984, 371285153433650975, 371285153386111297, 371285153332181225, 371285153201494175, 371285153106095767, 371285153009068518, 371285152960195979, 371285152775674610, 371285152582877150]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 93870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 93800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484153794157480, 362484287623201994⟩, ⟨72647878489134737, 81131497640774115⟩, true⟩

def words08 : List Nat := [371285152388589106, 371285152297924930, 371285152149258416, 371285152101355005, 371285152052412757, 371285151966397851, 371285151794459501, 371285151737769847, 371285151732031257, 371285151735435893]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 93880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 93800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487271299171587, 362487405158157156⟩, ⟨(-220071660632933501), (-211585230163600641)⟩, true⟩

def words09 : List Nat := [371285151728738951, 371285151688826271, 371285151717596755, 371285151734608744, 371285151774318812, 371285151815342259, 371285151855610042, 371285151858962349, 371285151850280244, 371285151878318139]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 93890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 93800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 93800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk938B
