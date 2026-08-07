import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk829

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488728977087353, 362488832312270150⟩, ⟨(-298833974448595414), (-293049606803759892)⟩, true⟩

def state01 : KState := ⟨⟨362486197566542370, 362486300927474838⟩, ⟨(-88938262085548791), (-83151759663712751)⟩, true⟩

def words00 : List Nat := [371285297457311525, 371285297471703225, 371285297630447377, 371285297790384468, 371285297926130611, 371285297929004668, 371285297884379329, 371285297901725627, 371285298008570532, 371285298023642250]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 82900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 82900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362491295392149234, 362491398779285367⟩, ⟨(-511623109470570799), (-505834434369789737)⟩, true⟩

def words01 : List Nat := [371285298025792808, 371285298028657696, 371285298175555345, 371285298269352145, 371285298347902870, 371285298427495119, 371285298493296345, 371285298496190425, 371285298505143149, 371285298582298238]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 82910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 82900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485396302773199, 362485499715551663⟩, ⟨(-22388512559384532), (-16597711062385492)⟩, true⟩

def words02 : List Nat := [371285298780912172, 371285298859894234, 371285298934530138, 371285299010108899, 371285299120091061, 371285299173931755, 371285299323355065, 371285299473974172, 371285299571359219, 371285299576748775]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 82920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 82900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362507160767604939, 362507264206336571⟩, ⟨(-1827433233718744343), (-1821640279795038551)⟩, true⟩

def words03 : List Nat := [371285299712870940, 371285299850449389, 371285300115562274, 371285300187787017, 371285300233938321, 371285300281038114, 371285300463397596, 371285300585958479, 371285300852721912, 371285301120772194]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 82930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 82900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489720295913072, 362489823760615323⟩, ⟨(-380896645279079497), (-375101537226413049)⟩, true⟩

def words04 : List Nat := [371285301387431193, 371285301479213031, 371285301572257064, 371285301666829150, 371285301795216934, 371285301798092978, 371285301753237935, 371285301704745639, 371285301737535694, 371285301795392163]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 82940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 82900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362477257077390884, 362477360567992747⟩, ⟨653039999544481972, 658837256100950116⟩, true⟩

def words05 : List Nat := [371285301926112191, 371285302058012083, 371285302187690131, 371285302195740059, 371285302235268015, 371285302276188488, 371285302376421074, 371285302379297137, 371285302285998047, 371285302193548448]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 82950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 82900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492493518847855, 362492597035189217⟩, ⟨(-611015558670471036), (-605216166630811666)⟩, true⟩

def words06 : List Nat := [371285302107669791, 371285302110890884, 371285302173441093, 371285302279558647, 371285302361579992, 371285302364470035, 371285302377789450, 371285302452107045, 371285302634638454, 371285302725531255]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 82960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 82900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362488033949971971, 362488137492550773⟩, ⟨(-240991213603285969), (-235189644507746365)⟩, true⟩

def words07 : List Nat := [371285302787753709, 371285302850859824, 371285302959065059, 371285302996050168, 371285303074435467, 371285303153959276, 371285303216682222, 371285303219609013, 371285303195849064, 371285303233569709]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 82970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 82900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482524232074057, 362482627800231257⟩, ⟨216250739184549521, 222054430910147311⟩, true⟩

def words08 : List Nat := [371285303414965981, 371285303417842675, 371285303405850972, 371285303401120307, 371285303395270015, 371285303397664380, 371285303373933112, 371285303424501947, 371285303474211655, 371285303477191254]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 82980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 82900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497611092371808, 362497714686632123⟩, ⟨(-1035865025607114747), (-1030059167463585693)⟩, true⟩

def words09 : List Nat := [371285303526854567, 371285303610371817, 371285303817655067, 371285303877689335, 371285303893763269, 371285303910691458, 371285304071704544, 371285304180443305, 371285304331953342, 371285304484737404]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 82990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 82900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 82900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk829
