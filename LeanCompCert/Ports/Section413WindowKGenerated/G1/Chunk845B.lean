import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk845A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk845B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk845A

def state06 : KState := ⟨⟨362499375310466862, 362499482989770933⟩, ⟨(-1204023748393255750), (-1197875634320096656)⟩, true⟩

def words05 : List Nat := [371285316278206369, 371285316439558262, 371285316643267185, 371285316681433621, 371285316697321716, 371285316714075795, 371285316801576003, 371285316832532811, 371285317002051734, 371285317172972172]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 84550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 84500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362483279447693755, 362483387153464605⟩, ⟨157092136675461073, 163242488914039593⟩, true⟩

def words06 : List Nat := [371285317335868588, 371285317338804640, 371285317411867974, 371285317512152572, 371285317636783180, 371285317639719334, 371285317578135552, 371285317490853984, 371285317414853141, 371285317418202858]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 84560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 84500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362480217977027147, 362480325709207597⟩, ⟨416060255711976516, 422212841547993576⟩, true⟩

def words07 : List Nat := [371285317474698327, 371285317555181927, 371285317634638203, 371285317637626669, 371285317601020972, 371285317582047338, 371285317665354524, 371285317668305057, 371285317640595298, 371285317584846614]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 84570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 84500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487751971064212, 362487859729551999⟩, ⟨(-221218359005373283), (-215063547962264421)⟩, true⟩

def words08 : List Nat := [371285317527854903, 371285317515022597, 371285317466136854, 371285317496689937, 371285317503462160, 371285317506398838, 371285317326608896, 371285317274090310, 371285317303651680, 371285317336768343]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 84580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 84500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485765581135311, 362485873366413821⟩, ⟨(-53161164499704075), (-47004087099738967)⟩, true⟩

def words09 : List Nat := [371285317366743856, 371285317397724897, 371285317532892033, 371285317610886805, 371285317695413113, 371285317781000223, 371285317858384993, 371285317861322343, 371285317758841354, 371285317769114738]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 84590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 84500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 84500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk845B
