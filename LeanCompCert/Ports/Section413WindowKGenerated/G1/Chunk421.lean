import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk421

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362478720125112471, 362478745380201725⟩, ⟨269975336010702417, 270693759474394313⟩, true⟩

def state01 : KState := ⟨⟨362487337992151908, 362487363259639492⟩, ⟨(-92759133899929042), (-92040188403952598)⟩, true⟩

def words00 : List Nat := [371285175420674656, 371285175553110446, 371285176159036363, 371285176765511871, 371285177223682834, 371285177225069701, 371285177084911101, 371285177139129763, 371285177549622280, 371285177602960621]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 42100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 42100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362469127979863699, 362469153260024375⟩, ⟨674264776731728679, 674984255952629587⟩, true⟩

def words01 : List Nat := [371285177656244424, 371285177710030097, 371285178164488434, 371285178338155574, 371285178679921070, 371285179022187983, 371285179338974515, 371285179340361027, 371285178905981139, 371285178527259718]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 42110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 42100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362467591154533582, 362467616447043601⟩, ⟨739003347602068065, 739723347041685697⟩, true⟩

def words02 : List Nat := [371285178259812051, 371285178261198666, 371285177623368719, 371285176970692756, 371285176317531363, 371285175816610758, 371285175138961443, 371285174949921237, 371285174760414931, 371285174561143808]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 42120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 42100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362491544746656698, 362491570051693400⟩, ⟨(-270300636038641071), (-269580108785606619)⟩, true⟩

def words03 : List Nat := [371285174292212268, 371285174440726469, 371285174733647579, 371285174735034828, 371285174277521255, 371285173733427822, 371285173188783331, 371285173059119241, 371285172800268459, 371285172953646709]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 42130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 42100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362465794120724101, 362465819438273601⟩, ⟨814859334180587105, 815580388786911971⟩, true⟩

def words04 : List Nat := [371285172995995439, 371285172997385764, 371285172460787273, 371285172124780710, 371285171788085830, 371285171620399619, 371285170917895296, 371285170078214898, 371285169238022805, 371285168913689661]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 42140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 42100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362465982795482529, 362466008125542448⟩, ⟨807015177851355538, 807736759835272002⟩, true⟩

def words05 : List Nat := [371285168477143742, 371285168500233919, 371285168521315366, 371285168522727065, 371285168077179691, 371285167800943400, 371285167809051919, 371285167810439826, 371285167419954593, 371285166967094519]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 42150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 42100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472809810981533, 362472835153469043⟩, ⟨519132265747378092, 519854371742875072⟩, true⟩

def words06 : List Nat := [371285166513634049, 371285166215117065, 371285165635319169, 371285165344363031, 371285165053011509, 371285164663090898, 371285163668724358, 371285163172301815, 371285162739695044, 371285162741131905]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 42160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 42100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475949401097606, 362475974756220408⟩, ⟨386759933134553898, 387482572023141740⟩, true⟩

def words07 : List Nat := [371285162449846148, 371285162157616482, 371285162075996629, 371285162102503465, 371285162143800842, 371285162185628694, 371285162186669631, 371285162156771876, 371285161377524979, 371285161161436699]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 42170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 42100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362472898029686535, 362472923397183966⟩, ⟨515594363611444675, 516317524526015447⟩, true⟩

def words08 : List Nat := [371285161289148679, 371285161290563498, 371285161275944892, 371285161246747103, 371285161217018963, 371285161128381763, 371285161015070725, 371285161240511225, 371285161308154937, 371285161309592737]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 42180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 42100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362519920336727509, 362519945716807116⟩, ⟨(-1468498187006250164), (-1467774495187544190)⟩, true⟩

def words09 : List Nat := [371285161192681241, 371285161366573138, 371285162101710453, 371285162317600813, 371285162385925351, 371285162454701366, 371285163084796562, 371285163503922487, 371285164329090547, 371285165154849164]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 42190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 42100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 42100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk421
