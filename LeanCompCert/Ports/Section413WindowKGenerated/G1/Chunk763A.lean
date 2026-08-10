import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk763A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362478786821731736, 362478873800926015⟩, ⟨478587642266578084, 483069270800776824⟩, true⟩

def state01 : KState := ⟨⟨362482995298217973, 362483082300924367⟩, ⟨157502706462865071, 161986129093118941⟩, true⟩

def words00 : List Nat := [371285204950157344, 371285204953084324, 371285205054339484, 371285205192806949, 371285205303297803, 371285205305926767, 371285205187356384, 371285205088019109, 371285205036088952, 371285205038823635]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 76300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 76300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362489562016766481, 362489649043475536⟩, ⟨(-343642952909181276), (-339157698520076404)⟩, true⟩

def words01 : List Nat := [371285205012990676, 371285204980179653, 371285204999358566, 371285205007068220, 371285205065872988, 371285205125659937, 371285205184498086, 371285205187145561, 371285205149967005, 371285205211522076]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 76310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 76300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478276465691739, 362478363515848916⟩, ⟨517727324820964215, 522214368892546987⟩, true⟩

def words02 : List Nat := [371285205343004874, 371285205345636662, 371285205283177130, 371285205215407391, 371285205146658886, 371285205113034656, 371285205021569489, 371285205053522295, 371285205055521811, 371285205050879606]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 76320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 76300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362494441077241788, 362494528151136389⟩, ⟨(-716193613783020550), (-711704757710915864)⟩, true⟩

def words03 : List Nat := [371285205005912679, 371285205051908475, 371285205268095682, 371285205270725898, 371285205258527125, 371285205204491737, 371285205213560095, 371285205216485571, 371285205319292905, 371285205444364001]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 76330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 76300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486492366834818, 362486579464461979⟩, ⟨(-109325110435673121), (-104834442497284343)⟩, true⟩

def words04 : List Nat := [371285205568413708, 371285205593445029, 371285205789045180, 371285205986027516, 371285206233928245, 371285206276408183, 371285206298454556, 371285206321341434, 371285206384280424, 371285206405268291]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 76340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 76300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk763A
