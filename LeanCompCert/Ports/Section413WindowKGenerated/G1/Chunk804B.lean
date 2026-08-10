import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk804A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk804B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk804A

def state06 : KState := ⟨⟨362486378400888911, 362486475519440018⟩, ⟨(-110429051758038860), (-105152500216998478)⟩, true⟩

def words05 : List Nat := [371285168922463774, 371285168806131813, 371285168697197237, 371285168700289273, 371285168685279664, 371285168703603003, 371285168718551876, 371285168721383526, 371285168624363133, 371285168644056702]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 80450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 80400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475130805716621, 362475227949027835⟩, ⟨794601567672251812, 799880111541338004⟩, true⟩

def words06 : List Nat := [371285168759968716, 371285168762751071, 371285168673055138, 371285168584431253, 371285168494758099, 371285168389671095, 371285168206144998, 371285168155349667, 371285168103660858, 371285168052315288]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 80460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 80400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489059234854883, 362489156403395891⟩, ⟨(-326255945086614944), (-320975370852015388)⟩, true⟩

def words07 : List Nat := [371285167961455158, 371285167995644597, 371285168182600774, 371285168185383462, 371285168166874775, 371285168108600862, 371285168097477278, 371285168100581363, 371285168137668376, 371285168190390934]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 80470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 80400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478423608605236, 362478520802224836⟩, ⟨529693626079090836, 534976218770651110⟩, true⟩

def words08 : List Nat := [371285168245228307, 371285168248011218, 371285168096975726, 371285168013598682, 371285167928870200, 371285167892534777, 371285167727266649, 371285167532168980, 371285167335918430, 371285167295190058]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 80480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 80400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362473559981628912, 362473657200344985⟩, ⟨921230981843666264, 926515594672338264⟩, true⟩

def words09 : List Nat := [371285167286155082, 371285167360800439, 371285167404534051, 371285167407317565, 371285167260954863, 371285167128040177, 371285166993598430, 371285166991615087, 371285166850651279, 371285166710837810]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 80490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 80400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 80400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk804B
