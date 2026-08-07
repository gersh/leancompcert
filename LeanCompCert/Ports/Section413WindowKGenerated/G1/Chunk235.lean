import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk235

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362457655551695830, 362457663048372003⟩, ⟨631516697893025566, 631635819153841474⟩, true⟩

def state01 : KState := ⟨⟨362507357332638957, 362507364835926151⟩, ⟨(-536635150077383518), (-536515873423253830)⟩, true⟩

def words00 : List Nat := [371284540397296547, 371284540398109826, 371284540656986500, 371284541447098174, 371284541948689534, 371284541949442121, 371284541651269512, 371284541962965783, 371284544083420972, 371284545054826953]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 23500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 23500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362501514201445360, 362501521711482057⟩, ⟨(-399244287863932283), (-399124852495727585)⟩, true⟩

def words01 : List Nat := [371284545822161105, 371284546589683216, 371284548089615440, 371284548687937782, 371284549832532948, 371284550977305885, 371284551991617961, 371284551992361943, 371284552116472677, 371284552838879033]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 23510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 23500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473840694768125, 362473848211386210⟩, ⟨251890541752944665, 252010131949896941⟩, true⟩

def words02 : List Nat := [371284555003791411, 371284555313504012, 371284555619341928, 371284555925395570, 371284556758180492, 371284556759002078, 371284557369915973, 371284558042480402, 371284558373471279, 371284558374240010]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 23520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 23500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362576620453101535, 362576627976391685⟩, ⟨(-2167014554141058236), (-2166894806916250292)⟩, true⟩

def words03 : List Nat := [371284559269892337, 371284560620954887, 371284563449581668, 371284564935433630, 371284566139245237, 371284567343188057, 371284570351215048, 371284572458389580, 371284576369491893, 371284580280587928]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 23530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 23500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362526780230062625, 362526787760035875⟩, ⟨(-993726198175190657), (-993606293596962921)⟩, true⟩

def words04 : List Nat := [371284583727101104, 371284585044225107, 371284587551605230, 371284590059166880, 371284592726931582, 371284593289828937, 371284593728491211, 371284594167372468, 371284596409144905, 371284598201477981]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 23540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 23500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362480210448541316, 362480217985181910⟩, ⟨103339233280974406, 103459294908706662⟩, true⟩

def words05 : List Nat := [371284600911589879, 371284603621779562, 371284606319959647, 371284606618758731, 371284607033061359, 371284607447679999, 371284609663919330, 371284609664659775, 371284609482067352, 371284609296510803]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 23550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 23500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362512980962814360, 362512988506095745⟩, ⟨(-668588874179173731), (-668468656060927339)⟩, true⟩

def words06 : List Nat := [371284610725626617, 371284611920281508, 371284614915698337, 371284617911154508, 371284620622109590, 371284620935744306, 371284623049855090, 371284625164178110, 371284627510163418, 371284628714145428]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 23560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 23500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362467250620545088, 362467258170569503⟩, ⟨409619513170938403, 409739890256578461⟩, true⟩

def words07 : List Nat := [371284629760901253, 371284630807804963, 371284632772122813, 371284633839011833, 371284634917310762, 371284635995819533, 371284636941194843, 371284636941935734, 371284635492281760, 371284634756246203]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 23570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 23500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362465384789136147, 362465392345770191⟩, ⟨453701261420128871, 453821794395304405⟩, true⟩

def words08 : List Nat := [371284635081953437, 371284635082697899, 371284634435817413, 371284633461529021, 371284632487025238, 371284631862367924, 371284630341557892, 371284630309203860, 371284630276615429, 371284630234468594]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 23580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 23500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362531339319709949, 362531346883053267⟩, ⟨(-1102481123691103162), (-1102360432410792850)⟩, true⟩

def words09 : List Nat := [371284630091499269, 371284630764336942, 371284633233993934, 371284633677817742, 371284633719036941, 371284633760471408, 371284634530860028, 371284634714563343, 371284636694396291, 371284638674400634]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 23590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 23500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 23500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk235
