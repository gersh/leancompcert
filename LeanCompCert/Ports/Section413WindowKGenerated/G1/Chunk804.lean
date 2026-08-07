import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk804

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476758339221028, 362476855307446218⟩, ⟨663569273268512086, 668833734070375400⟩, true⟩

def state01 : KState := ⟨⟨362475058738417659, 362475155731445025⟩, ⟨800224585598116825, 805491040621951691⟩, true⟩

def words00 : List Nat := [371285174033405193, 371285174007087972, 371285173851605502, 371285173697103110, 371285173541574049, 371285173415983479, 371285173211692847, 371285173163135476, 371285173113641483, 371285173030793638]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 80400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 80400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362493283346775607, 362493380364887257⟩, ⟨(-665298420615730006), (-660029948435452768)⟩, true⟩

def words01 : List Nat := [371285172925873305, 371285172946940482, 371285173096076616, 371285173098859180, 371285173074171133, 371285173026945584, 371285173002448488, 371285173005527404, 371285173075685935, 371285173180837874]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 80410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 80400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476461695950877, 362476558739171332⟩, ⟨687519939677450774, 692790431237548290⟩, true⟩

def words02 : List Nat := [371285173255910022, 371285173258691096, 371285173147144375, 371285173101030559, 371285173053488335, 371285173052356636, 371285172844548569, 371285172619012331, 371285172392374937, 371285172321556482]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 80420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 80400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362460816172758829, 362460913241019206⟩, ⟨1946003421672922762, 1951275927325238040⟩, true⟩

def words03 : List Nat := [371285172216361748, 371285172176365509, 371285172135395413, 371285172092640209, 371285171860239180, 371285171676689306, 371285171491764847, 371285171371665406, 371285171072094761, 371285170773681131]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 80430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 80400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477962712256054, 362478059805439886⟩, ⟨566660891242291485, 571935401860180527⟩, true⟩

def words04 : List Nat := [371285170474010779, 371285170317707843, 371285170095302654, 371285169929370015, 371285169762527286, 371285169580362185, 371285169282416440, 371285169140363754, 371285169005811467, 371285169008694830]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 80440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 80400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk804
