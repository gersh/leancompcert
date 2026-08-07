import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk500

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362493383486050772, 362493419610006511⟩, ⟨(-422020734497875158), (-420800472630093518)⟩, true⟩

def state01 : KState := ⟨⟨362482784981687333, 362482821120714616⟩, ⟨107887213856633269, 109108229378787619⟩, true⟩

def words00 : List Nat := [371285003859274191, 371285003860945320, 371285003521415368, 371285003519706047, 371285003604803113, 371285003606483255, 371285003337410341, 371285003064524768, 371285002847053246, 371285002848956544]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 50000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 50000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362462515190588000, 362462551344615819⟩, ⟨1121763480629127101, 1122985246406154243⟩, true⟩

def words01 : List Nat := [371285003027719159, 371285003250755261, 371285003471785918, 371285003473459654, 371285003284902786, 371285003110002173, 371285002962709193, 371285002964378688, 371285002516237909, 371285002069254087]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 50010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 50000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473097524486870, 362473133693480875⟩, ⟨592508869601758716, 593731384062994578⟩, true⟩

def words02 : List Nat := [371285001621561234, 371285001573733594, 371285001590532433, 371285001799734208, 371285001898323876, 371285001899993400, 371285001466255731, 371285001324025723, 371285001198929566, 371285001200657829]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 50020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 50000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362474412637581580, 362474448821817766⟩, ⟨526760637257186129, 527983914360210199⟩, true⟩

def words03 : List Nat := [371285000964719687, 371285000684044910, 371285000519109954, 371285000520951098, 371285000541734379, 371285000614749339, 371285000681294199, 371285000682964308, 371285000267873424, 371285000059115133]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 50030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 50000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362477932487214876, 362477968686359739⟩, ⟨350586737059988706, 351810760267942392⟩, true⟩

def words04 : List Nat := [371284999986725800, 371284999988396020, 371284999645375177, 371284999224516142, 371284998803050583, 371284998505061433, 371284998054149729, 371284998002644330, 371284997950558674, 371284997872379079]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 50040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 50000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362510555424625973, 362510591638819969⟩, ⟨(-1282320267751954518), (-1281095491257138930)⟩, true⟩

def words05 : List Nat := [371284997991268153, 371284998251434397, 371284998909358072, 371284999135059362, 371284999296886428, 371284999459240354, 371284999787042431, 371284999924220047, 371285000436574818, 371285000949635632]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 50050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 50000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480155587197976, 362480191816468278⟩, ⟨239538750847453483, 240764282139515931⟩, true⟩

def words06 : List Nat := [371285001329199395, 371285001330870298, 371285001290229987, 371285001403584870, 371285001542437550, 371285001544108610, 371285001151766211, 371285000758629220, 371285000368230152, 371285000370135934]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 50060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 50000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362469369921360764, 362469406165719054⟩, ⟨779628430826110284, 780854717649346192⟩, true⟩

def words07 : List Nat := [371285000277756468, 371285000282095963, 371285000286475154, 371285000288146484, 371284999761339250, 371284999352841324, 371284998943485323, 371284998932874119, 371284998622087014, 371284998312636973]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 50070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 50000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362475574406419773, 362475610665726264⟩, ⟨468924709819439638, 470151745326110376⟩, true⟩

def words08 : List Nat := [371284998024470565, 371284998026317119, 371284997889169593, 371284997863557457, 371284997837474543, 371284997721316709, 371284997127404393, 371284996932403370, 371284996803850595, 371284996805581048]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 50080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 50000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362472644831942755, 362472681106485809⟩, ⟨615766413055224617, 616994211837515153⟩, true⟩

def words09 : List Nat := [371284996619449840, 371284996408135819, 371284996380942897, 371284996450463116, 371284996602557052, 371284996755306822, 371284996908132280, 371284996909805189, 371284996603979824, 371284996360215101]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 50090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 50000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 50000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk500
