import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk266

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362514761707550250, 362514771413178870⟩, ⟨(-784520944235183627), (-784346412378046051)⟩, true⟩

def state01 : KState := ⟨⟨362451728057756338, 362451737770994877⟩, ⟨892496708108952831, 892671442429728785⟩, true⟩

def words00 : List Nat := [371285286921965434, 371285286922810007, 371285287058473656, 371285287670488829, 371285288399774872, 371285288400619521, 371285287484116291, 371285286308262862, 371285285132149029, 371285284236324818]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 26600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 26600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362426642307328078, 362426652028160359⟩, ⟨1560269693006509086, 1560444629436601548⟩, true⟩

def words01 : List Nat := [371285282976278247, 371285282247699713, 371285281518905580, 371285280797822974, 371285278905515051, 371285277441157456, 371285275976466957, 371285275671159751, 371285273486676453, 371285271285464514]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 26610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 26600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362450767775082267, 362450777503490404⟩, ⟨917988309761343124, 918163447898388220⟩, true⟩

def words02 : List Nat := [371285269084055407, 371285267470001404, 371285265383655634, 371285264516507249, 371285263649146625, 371285262551325313, 371285259575537704, 371285258008213292, 371285256440563144, 371285256040775361]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 26620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 26600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362452455491327004, 362452465227448832⟩, ⟨873084461842176155, 873259805433028835⟩, true⟩

def words03 : List Nat := [371285254746741261, 371285253166418867, 371285251585865362, 371285251413012427, 371285250656594052, 371285249965804133, 371285249274792630, 371285248594826435, 371285246479635233, 371285245250175298]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 26630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 26600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476310292041194, 362476320035703056⟩, ⟨237611627398419224, 237787171895195986⟩, true⟩

def words04 : List Nat := [371285244196523538, 371285244197389423, 371285243631683668, 371285243044374831, 371285242456795230, 371285242268663649, 371285241894380349, 371285242410919946, 371285242630390684, 371285242631271357]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 26640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 26600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362496356935487132, 362496366686788738⟩, ⟨(-296735386390910164), (-296559638256615432)⟩, true⟩

def words05 : List Nat := [371285242995185020, 371285243694267033, 371285245122418324, 371285245123264274, 371285244677383405, 371285244014823640, 371285243351942651, 371285243278857313, 371285242918469635, 371285243336642209]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 26650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 26600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362453950200675076, 362453959959617080⟩, ⟨833839923311857319, 834015875178220155⟩, true⟩

def words06 : List Nat := [371285243752496916, 371285243753343126, 371285242296258388, 371285241202652252, 371285240108697417, 371285239440182081, 371285237135036716, 371285234837402105, 371285232539604330, 371285231645975469]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 26660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 26600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362388190390765736, 362388200157341124⟩, ⟨2588184380969536881, 2588360536456192885⟩, true⟩

def words07 : List Nat := [371285230499703114, 371285230526280511, 371285230526915924, 371285230378838790, 371285228359299245, 371285226280786911, 371285224201995993, 371285222439087315, 371285218805372801, 371285215169951926]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 26670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 26600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362448041781543561, 362448051555701773⟩, ⟨991167474841981722, 991343832677513826⟩, true⟩

def words08 : List Nat := [371285211534418747, 371285209301826930, 371285206369630208, 371285204840263508, 371285203310746910, 371285201519541681, 371285198471322279, 371285196825789033, 371285195179932396, 371285194449395199]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 26680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 26600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362466232549649912, 362466242331523694⟩, ⟨505546776813237375, 505723340616819747⟩, true⟩

def words09 : List Nat := [371285193058452360, 371285191360187825, 371285189661714932, 371285189365001071, 371285188365849432, 371285187705910869, 371285187045733438, 371285186098960628, 371285183988995831, 371285183280610467]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 26690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 26600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 26600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk266
