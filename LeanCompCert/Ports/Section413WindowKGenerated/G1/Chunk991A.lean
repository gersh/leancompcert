import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk991A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362471802640409706, 362471952355045774⟩, ⟨1318034744880372636, 1328051642017072260⟩, true⟩

def state01 : KState := ⟨⟨362490009687787836, 362490159433596166⟩, ⟨(-486364316943627212), (-476344330478390544)⟩, true⟩

def words00 : List Nat := [371285353348738766, 371285353312202176, 371285353243776968, 371285353263143500, 371285353265837625, 371285353269247775, 371285353186853898, 371285353163050316, 371285353211304326, 371285353263438683]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 99100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 99100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488203012071892, 362488352789664152⟩, ⟨(-307295521732920287), (-297272385004316327)⟩, true⟩

def words01 : List Nat := [371285353314418222, 371285353366623649, 371285353459510726, 371285353502994367, 371285353569780640, 371285353637869088, 371285353704610284, 371285353708093330, 371285353669150616, 371285353703849801]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 99110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 99100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362474085922968145, 362474235731555388⟩, ⟨1092070014245411011, 1102096223360142305⟩, true⟩

def words02 : List Nat := [371285353788686378, 371285353792172630, 371285353767064310, 371285353728064550, 371285353687776920, 371285353664050756, 371285353588043183, 371285353531733676, 371285353474216718, 371285353417658083]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 99120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 99100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362502502651449363, 362502652491485083⟩, ⟨(-1725023411220562491), (-1714994084458689273)⟩, true⟩

def words03 : List Nat := [371285353307868184, 371285353301672847, 371285353385116261, 371285353407727463, 371285353412450561, 371285353418284259, 371285353524432942, 371285353601003263, 371285353777854619, 371285353956222592]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 99130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 99100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362493080608190274, 362493230479694236⟩, ⟨(-790922088139351344), (-780889641459719044)⟩, true⟩

def words04 : List Nat := [371285354113416676, 371285354166175871, 371285354270012512, 371285354375725999, 371285354506467270, 371285354513580996, 371285354519691651, 371285354527014140, 371285354634650257, 371285354718063393]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 99140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 99100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk991A
