import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk373

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362464395084555772, 362464414714893259⟩, ⟨760652119813504297, 761146947323713131⟩, true⟩

def state01 : KState := ⟨⟨362487613041142050, 362487632682371326⟩, ⟨(-105556462216171450), (-105061228385527558)⟩, true⟩

def words00 : List Nat := [371284820253037863, 371284820070384687, 371284819529819715, 371284819254805743, 371284818979426316, 371284818584885970, 371284817415440864, 371284816965169916, 371284816781100088, 371284816857858836]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 37300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 37300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362490413610237260, 362490433262560117⟩, ⟨(-210006890796097288), (-209511243007912724)⟩, true⟩

def words01 : List Nat := [371284816932084219, 371284817006742476, 371284817799205650, 371284818239339881, 371284818749761745, 371284819260611174, 371284819634604768, 371284819635822416, 371284819347779024, 371284819499718610]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 37310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 37300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473739370376199, 362473759033538474⟩, ⟨412410574691884725, 412906627063785311⟩, true⟩

def words02 : List Nat := [371284820369061957, 371284820370279302, 371284820282916999, 371284820045639086, 371284819807896288, 371284819788022923, 371284819634553536, 371284819859695102, 371284820018805612, 371284820020065766]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 37320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 37300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362522580092961668, 362522599767134685⟩, ⟨(-1411130477324527256), (-1410634013866561974)⟩, true⟩

def words03 : List Nat := [371284819724611551, 371284819725001850, 371284820272448906, 371284820273674830, 371284820183814538, 371284820005298204, 371284820363904845, 371284820659623403, 371284821672209687, 371284822685271142]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 37330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 37300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475787462376950, 362475807147541205⟩, ⟨336302508697225271, 336799382623561029⟩, true⟩

def words04 : List Nat := [371284823702880084, 371284823765012247, 371284824450825324, 371284825137248905, 371284825670974763, 371284825672193057, 371284825355412011, 371284824980025815, 371284824604182192, 371284824533956830]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 37340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 37300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362460093934400392, 362460113630557417⟩, ⟨922663997781203132, 923161282343215572⟩, true⟩

def words05 : List Nat := [371284824590083132, 371284824888147619, 371284825183351072, 371284825184571957, 371284824744869473, 371284824483099627, 371284824674244726, 371284824675463231, 371284824175021253, 371284823514988446]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 37350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 37300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362503905694123938, 362503925401187996⟩, ⟨(-714267939666703830), (-713770247562398250)⟩, true⟩

def words06 : List Nat := [371284822909668994, 371284822911017497, 371284823206572101, 371284823713488325, 371284824101410703, 371284824102653942, 371284824223772413, 371284824410568576, 371284825313022707, 371284825825378883]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 37360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 37300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362501864111513970, 362501883829687279⟩, ⟨(-637999098903880589), (-637500991590279239)⟩, true⟩

def words07 : List Nat := [371284826335183551, 371284826845361059, 371284827550142354, 371284827899283539, 371284828274636411, 371284828650446554, 371284829028439422, 371284829029666930, 371284829227000050, 371284829684758297]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 37370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 37300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362467403473070691, 362467423202095217⟩, ⟨650376042341298992, 650874555330344650⟩, true⟩

def words08 : List Nat := [371284830669115030, 371284830700068919, 371284830700983173, 371284830647509924, 371284830752866806, 371284830754223828, 371284830778869249, 371284830929687443, 371284830930605568, 371284830919541870]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 37380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 37300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362526346826437597, 362526366566500646⟩, ⟨(-1553805240508006131), (-1553306314735206469)⟩, true⟩

def words09 : List Nat := [371284830628778280, 371284830804215126, 371284831577375829, 371284831759809867, 371284831834713258, 371284831909971545, 371284832699995148, 371284833199354707, 371284834310700538, 371284835422554356]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 37390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 37300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 37300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk373
