import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk009

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362122243319761191, 362122243327636893⟩, ⟨302243198045460627, 302243202873158719⟩, true⟩

def state01 : KState := ⟨⟨362075904275642479, 362075904283703559⟩, ⟨343723647789033992, 343723652784549912⟩, true⟩

def words00 : List Nat := [371257986653390012, 371257986653410811, 371257305967144717, 371256355943583190, 371255408019513352, 371254821947344756, 371253658567021027, 371253672710094316, 371253672710110126, 371253622583466801]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨363056910611117555, 363056910619369420⟩, ⟨(-553735399060742803), (-553735393890637159)⟩, true⟩

def words01 : List Nat := [371253974430473366, 371254739217913267, 371256063074729732, 371256063074750798, 371255824229399103, 371255355483219603, 371254887759379372, 371254873151615894, 371255024321638361, 371255677835557654]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨361834021728779167, 361834021737223367⟩, ⟨572916699245934400, 572916704593978118⟩, true⟩

def words02 : List Nat := [371256319134739273, 371256319134760493, 371255426142695196, 371255220475346064, 371255027343739293, 371255027343760662, 371253521238083036, 371251988649182713, 371250459359711504, 371250061204528720]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360833610292639721, 360833610301278650⟩, ⟨1508426652515257006, 1508426658045414840⟩, true⟩

def words03 : List Nat := [371249399508015969, 371249058416475488, 371248718056099646, 371248376083120467, 371246542108137958, 371244568724823499, 371242599553628597, 371241743031001890, 371240028467437048, 371238319511965262]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨361968121659323815, 361968121668158834⟩, ⟨438851443105336625, 438851448820839469⟩, true⟩

def words04 : List Nat := [371236614188695686, 371236013526676104, 371234867365586535, 371234317197048032, 371233768192880833, 371232943502206842, 371231235733875033, 371230621441802009, 371230070561631624, 371230070561654455]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨361591274547121135, 361591274556157810⟩, ⟨803369407617121944, 803369413525230092⟩, true⟩

def words05 : List Nat := [371229584810994308, 371229103009599146, 371229217106329558, 371229307161015986, 371229721750806166, 371230135474168196, 371230273468085466, 371230273468107658, 371228990315802062, 371228117695246592]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨361806286215460017, 361806286224696056⟩, ⟨598741278014048283, 598741284114583145⟩, true⟩

def words06 : List Nat := [371227290133947313, 371227290133969683, 371226423239933153, 371225538451938833, 371224655497693844, 371224103976476325, 371223380121245284, 371223539187565306, 371223545280460991, 371223545280484287]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362745891413503121, 362745891422943916⟩, ⟨(-316225301822636438), (-316225295522437306)⟩, true⟩

def words07 : List Nat := [371223312324720088, 371223714235326271, 371224528257044963, 371224528257067617, 371223965839855699, 371223307268843268, 371223017454643463, 371223017454668350, 371223212549936248, 371223541478476600]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362123621934471558, 362123621944118855⟩, ⟨294339682359504407, 294339688863132627⟩, true⟩

def words08 : List Nat := [371223874375553607, 371223874375576396, 371222853967555661, 371222846323180559, 371223154174474025, 371223154174496970, 371222608569071411, 371221847943698046, 371221088856486323, 371220934761152323]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362226788737721934, 362226788747577509⟩, ⟨197159867472022664, 197159874182935698⟩, true⟩

def words09 : List Nat := [371221330793531261, 371222025436949141, 371222702514024907, 371222702514048370, 371222823969199927, 371223046755645545, 371224252610332210, 371224252610355433, 371224145978965725, 371223948621760445]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk009
