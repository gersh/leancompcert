import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk837

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486258156033023, 362486363573385752⟩, ⟨(-92685218611682089), (-86727404550046629)⟩, true⟩

def state01 : KState := ⟨⟨362482436341649270, 362482541784850207⟩, ⟨227234975249442218, 233194952943614688⟩, true⟩

def words00 : List Nat := [371285327573138571, 371285327576042464, 371285327543082182, 371285327510978045, 371285327486068028, 371285327489324082, 371285327475295183, 371285327505989771, 371285327529678214, 371285327532705226]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 83700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 83700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362501033006227463, 362501138475744393⟩, ⟨(-1329603232962725529), (-1323641052228750033)⟩, true⟩

def words01 : List Nat := [371285327587778244, 371285327677677304, 371285327824988099, 371285327827898810, 371285327827703517, 371285327805491712, 371285327899459919, 371285327948873466, 371285328139693184, 371285328331906781]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 83710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 83700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483020826452284, 362483126322137983⟩, ⟨178421278848786906, 184385650569974896⟩, true⟩

def words02 : List Nat := [371285328480808261, 371285328483714186, 371285328555625635, 371285328647831585, 371285328754253205, 371285328757157999, 371285328673635155, 371285328564628120, 371285328464417857, 371285328467731797]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 83720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 83700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362480725952674087, 362480831474484107⟩, ⟨370620581969457641, 376587141213264149⟩, true⟩

def words03 : List Nat := [371285328501476662, 371285328562695293, 371285328623623439, 371285328626579257, 371285328568987422, 371285328556511708, 371285328669060295, 371285328671965650, 371285328624797142, 371285328574331412]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 83730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 83700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485227923584386, 362485333471440731⟩, ⟨(-6404785561229597), (-436045064681213)⟩, true⟩

def words04 : List Nat := [371285328528861331, 371285328532072010, 371285328481050119, 371285328472266032, 371285328462557345, 371285328430604407, 371285328261206325, 371285328221685846, 371285328261920158, 371285328264994663]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 83740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 83700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362481373383644118, 362481478957999448⟩, ⟨316474808884307164, 322445768802571812⟩, true⟩

def words05 : List Nat := [371285328267166650, 371285328270312727, 371285328392183728, 371285328473876264, 371285328561808719, 371285328650790597, 371285328738720661, 371285328741626623, 371285328639392844, 371285328597073023]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 83750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 83700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479812946944074, 362479918547186067⟩, ⟨447232980724763914, 453206109044973706⟩, true⟩

def words06 : List Nat := [371285328649643478, 371285328652602620, 371285328652946916, 371285328634570920, 371285328615120880, 371285328602398747, 371285328582940697, 371285328639935576, 371285328668434591, 371285328671443498]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 83760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 83700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500250452956320, 362500356079467336⟩, ⟨(-1264929420187446176), (-1258954091184308258)⟩, true⟩

def words07 : List Nat := [371285328649375254, 371285328693408899, 371285328878394099, 371285328881300694, 371285328876654150, 371285328852718181, 371285328942718476, 371285328990008956, 371285329171343857, 371285329353942643]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 83770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 83700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480067655839041, 362480173308627394⟩, ⟨426041642467085020, 432019173117516568⟩, true⟩

def words08 : List Nat := [371285329523577293, 371285329526484228, 371285329571001742, 371285329625158972, 371285329703826925, 371285329706733883, 371285329595683489, 371285329458027953, 371285329319221522, 371285329283959982]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 83780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 83700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476294281134890, 362476399960103271⟩, ⟨742270117861459867, 748249842273723315⟩, true⟩

def words09 : List Nat := [371285329305283105, 371285329389359805, 371285329457205709, 371285329460112888, 371285329337999794, 371285329260830515, 371285329182221476, 371285329163352569, 371285329059089859, 371285328955834462]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 83790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 83700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 83700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk837
