import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk142

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362436004608651859, 362436007227637145⟩, ⟨685976510420601949, 686001670080461435⟩, true⟩

def state01 : KState := ⟨⟨362454122263136119, 362454124885955839⟩, ⟨428594400617492709, 428619614745695469⟩, true⟩

def words00 : List Nat := [371284313802824581, 371284312913032413, 371284309595722118, 371284308315781068, 371284307035891350, 371284304903077481, 371284296182888744, 371284292399263387, 371284288615945531, 371284288124150470]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 14200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 14200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362453322880458527, 362453325507173252⟩, ⟨440127595060678303, 440152864556549659⟩, true⟩

def words01 : List Nat := [371284286001946159, 371284283870837463, 371284283619038061, 371284283619509928, 371284284904220419, 371284286321926362, 371284286832880010, 371284286833308265, 371284280768234573, 371284278591881871]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 14210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 14200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362425998064736906, 362426000695267614⟩, ⟨829059752991481217, 829085076770642639⟩, true⟩

def words02 : List Nat := [371284279162495478, 371284279162925796, 371284277223776606, 371284274317149889, 371284271410755650, 371284269830465065, 371284265790530658, 371284265307611537, 371284264824624570, 371284263877050513]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 14220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 14200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362511920456358077, 362511923090774515⟩, ⟨(-394166224687497487), (-394140845594767461)⟩, true⟩

def words03 : List Nat := [371284259783244322, 371284256885763853, 371284255005191567, 371284255005623088, 371284251650011750, 371284248073839981, 371284244498001455, 371284244417232614, 371284244660119201, 371284246604179840]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 14230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 14200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362456080348430174, 362456082986713300⟩, ⟨400966801721762617, 400992235896055755⟩, true⟩

def words04 : List Nat := [371284248108262359, 371284248108691322, 371284243059762742, 371284242920017380, 371284242780093071, 371284241756642408, 371284235782172349, 371284229816644218, 371284223851774091, 371284222792741094]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 14240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 14200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362399368135542581, 362399370777693833⟩, ⟨1209828834164651614, 1209854323478766330⟩, true⟩

def words05 : List Nat := [371284223748256470, 371284226678122977, 371284229602118027, 371284229602547336, 371284225983633339, 371284223909607313, 371284223809815249, 371284223810244635, 371284219246496086, 371284213296871868]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 14250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 14200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362428126735145197, 362428129381138292⟩, ⟨799763498570561673, 799789042689444493⟩, true⟩

def words06 : List Nat := [371284207347896595, 371284204677796520, 371284199559358161, 371284197510383789, 371284195461562954, 371284192649300309, 371284185788257030, 371284181422410045, 371284177056958488, 371284176265699571]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 14260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 14200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362447564139897969, 362447566789820090⟩, ⟨522227390102738291, 522252990308015629⟩, true⟩

def words07 : List Nat := [371284172338694271, 371284167922077903, 371284163505905592, 371284161109185837, 371284156972364191, 371284154159646288, 371284151347181628, 371284148532368383, 371284141688798744, 371284139128076954]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 14270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 14200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362376462635493767, 362376465289244114⟩, ⟨1538227193207228329, 1538252848099786973⟩, true⟩

def words08 : List Nat := [371284138885721508, 371284138886151812, 371284135679466249, 371284132106738219, 371284128534350270, 371284126501194978, 371284122025397132, 371284118562749366, 371284115100437272, 371284110694989376]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 14280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 14200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362490995528651541, 362490998186288680⟩, ⟨(-98906844808248022), (-98881134353665234)⟩, true⟩

def words09 : List Nat := [371284103162890724, 371284099696667893, 371284097637205075, 371284097637642849, 371284095010041834, 371284091541991283, 371284088074249019, 371284086723898821, 371284083421163478, 371284083905164727]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 14290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 14200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 14200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk142
