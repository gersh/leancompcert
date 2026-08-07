import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk539

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362506693957572800, 362506736191304617⟩, ⟨(-1173745879156840959), (-1172208052803135561)⟩, true⟩

def state01 : KState := ⟨⟨362476248222934367, 362476290472982898⟩, ⟨467404298363944572, 468943004273331412⟩, true⟩

def words00 : List Nat := [371284989170595358, 371284989172404795, 371284989322544398, 371284989527408497, 371284989836943477, 371284989838752987, 371284989689969659, 371284989432014546, 371284989173352561, 371284989100404032]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 53900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 53900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362460002223966403, 362460044490317132⟩, ⟨1343340803607184123, 1344880388452993919⟩, true⟩

def words01 : List Nat := [371284988940296088, 371284988836705122, 371284988732489525, 371284988628923050, 371284988238803663, 371284987896008629, 371284987552309641, 371284987552761338, 371284987094546823, 371284986634019896]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 53910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 53900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480821835561985, 362480864118151896⟩, ⟨220670611649477777, 222211072192087019⟩, true⟩

def words02 : List Nat := [371284986172701505, 371284985855341508, 371284985452240284, 371284985393366277, 371284985333935195, 371284985220536793, 371284984695880437, 371284984515703386, 371284984477342198, 371284984479216092]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 53920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 53900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475460658368203, 362475502957415880⟩, ⟨509829192634100692, 511370540828132506⟩, true⟩

def words03 : List Nat := [371284984404169557, 371284984329864413, 371284984353041983, 371284984355037283, 371284984292977557, 371284984198060832, 371284984102533087, 371284984007339315, 371284983489513283, 371284983315977767]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 53930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 53900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362469006949576114, 362469049264782771⟩, ⟨857985055757356498, 859527275649860576⟩, true⟩

def words04 : List Nat := [371284983141458721, 371284983097665415, 371284982767611063, 371284982438428500, 371284982108536347, 371284981884879021, 371284981498140408, 371284981418998618, 371284981339289735, 371284981188335132]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 53940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 53900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362505555335249997, 362505597666847894⟩, ⟨(-1113987949804205149), (-1112444845525399349)⟩, true⟩

def words05 : List Nat := [371284980942089486, 371284980992109681, 371284981338799590, 371284981340611417, 371284981282840269, 371284981131303419, 371284981138774326, 371284981179834347, 371284981563133489, 371284981947244377]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 53950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 53900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482543253707418, 362482585601669576⟩, ⟨127773286630893018, 129317274010179150⟩, true⟩

def words06 : List Nat := [371284982330887509, 371284982332699074, 371284982258783961, 371284982260209718, 371284982334968004, 371284982336792021, 371284982112635872, 371284981889398318, 371284981695065206, 371284981697167264]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 53960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 53900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362453188986669823, 362453231350913568⟩, ⟨1712272979141880970, 1713817845322751976⟩, true⟩

def words07 : List Nat := [371284981898034489, 371284982144007553, 371284982386734466, 371284982388546551, 371284982173939726, 371284981981096753, 371284981787326800, 371284981634975775, 371284981063512760, 371284980477355265]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 53970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 53900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362461041997963391, 362461084378432248⟩, ⟨1288378514812015678, 1289924256907873086⟩, true⟩

def words08 : List Nat := [371284979890433246, 371284979549224610, 371284979036124064, 371284978788450360, 371284978540163284, 371284978204472679, 371284977411190283, 371284976961494130, 371284976510887745, 371284976289099184]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 53980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 53900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470492885983641, 362470535283024670⟩, ⟨778084451940511956, 779631088847259350⟩, true⟩

def words09 : List Nat := [371284975847974627, 371284975339587989, 371284974830462460, 371284974664678773, 371284974326729119, 371284974094779225, 371284973862243961, 371284973601143763, 371284973160853744, 371284972895781101]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 53990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 53900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 53900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk539
