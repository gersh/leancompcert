import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk276A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk276B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk276A

def state06 : KState := ⟨⟨360561463017846955, 360561467587404840⟩, ⟨586771120087561679, 586856610565270349⟩, true⟩

def words05 : List Nat := [360582683939935787, 360582683064136309, 360582682614992538, 360582684053773082, 360582685161966140, 360582686270138451, 360582686361523239, 360582686361887586, 360582685151274983, 360582684384605320]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 27650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 27600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360547214671006490, 360547219243995767⟩, ⟨980891754524843745, 980977339932189731⟩, true⟩

def words06 : List Nat := [360582683869565873, 360582683869930268, 360582682820166202, 360582681116175552, 360582679412242084, 360582676850955307, 360582675149012718, 360582674372748544, 360582673596501271, 360582671984867910]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 27660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 27600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360577845655663485, 360577850232099314⟩, ⟨132969887675709105, 133055568465665427⟩, true⟩

def words07 : List Nat := [360582670703944332, 360582668958424626, 360582667212924604, 360582666768326972, 360582665488660186, 360582663010627591, 360582660532702274, 360582658432465906, 360582657326214798, 360582657152925386]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 27670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 27600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360512416787369475, 360512421367276419⟩, ⟨1943964764081808395, 1944050540969273225⟩, true⟩

def words08 : List Nat := [360582656979596170, 360582656152851721, 360582654026243325, 360582651858780841, 360582649691380316, 360582646629128329, 360582642654871116, 360582637684163994, 360582632713746272, 360582629043006621]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 27680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 27600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360486718075280622, 360486722658627218⟩, ⟨2655816261245805461, 2655902133394419981⟩, true⟩

def words09 : List Nat := [360582626507904872, 360582625272165990, 360582624036473546, 360582621893642216, 360582618948608468, 360582615372388273, 360582611796319703, 360582609519291473, 360582607063223890, 360582603602071060]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 27690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 27600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 27600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk276B
