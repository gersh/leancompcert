import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk832A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362481803841776690, 362481907955163502⟩, ⟨277917553227743603, 283766550846933099⟩, true⟩

def state01 : KState := ⟨⟨362487875068955747, 362487979208181078⟩, ⟨(-227201156751701816), (-221350009234736498)⟩, true⟩

def words00 : List Nat := [371285318599946753, 371285318603182537, 371285318705591662, 371285318831180552, 371285318933756532, 371285318936641649, 371285318898658155, 371285318954396835, 371285319068079582, 371285319103035909]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 83200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 83200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362482616941984286, 362482721107478580⟩, ⟨210357925721288668, 216211259208882982⟩, true⟩

def words01 : List Nat := [371285319136924338, 371285319171760614, 371285319271057542, 371285319316056443, 371285319335157538, 371285319355437229, 371285319374422578, 371285319377308133, 371285319203631124, 371285319175962225]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 83210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 83200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485201119569970, 362485305310792210⟩, ⟨(-4720394339264346), 1135080360652980⟩, true⟩

def words02 : List Nat := [371285319259889058, 371285319262774865, 371285319185728373, 371285319080892646, 371285318974930038, 371285318912546781, 371285318855347664, 371285318901069946, 371285318945623374, 371285318948667504]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 83220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 83200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490987422629486, 362491091639967013⟩, ⟨(-486291900033423255), (-480434251628131121)⟩, true⟩

def words03 : List Nat := [371285319094674514, 371285319242423729, 371285319532961346, 371285319632023219, 371285319715808847, 371285319800463354, 371285319880695772, 371285319890091036, 371285319961401204, 371285320034008073]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 83230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 83200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478498276673331, 362478602520080541⟩, ⟨553348446698811045, 559208265273681057⟩, true⟩

def words04 : List Nat := [371285320105617497, 371285320108504356, 371285320008938473, 371285320033829774, 371285320101352060, 371285320104239268, 371285319995047085, 371285319886680704, 371285319777086901, 371285319736480225]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 83240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 83200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk832A
