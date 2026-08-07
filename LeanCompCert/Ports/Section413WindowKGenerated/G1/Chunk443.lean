import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk443

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362516587478788868, 362516615558432262⟩, ⟨(-1375799439841853666), (-1374958966809119496)⟩, true⟩

def state01 : KState := ⟨⟨362492855784734529, 362492883877615311⟩, ⟨(-324435993643039499), (-323594934127882567)⟩, true⟩

def words00 : List Nat := [371285579511793910, 371285579695597867, 371285580091823605, 371285580488799957, 371285581039349125, 371285581040813802, 371285580912541038, 371285580770801807, 371285580898391326, 371285581064902263]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 44300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 44300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362458691339194167, 362458719445268952⟩, ⟨1189715037145431106, 1190556681354470742⟩, true⟩

def words01 : List Nat := [371285581680776257, 371285582297231936, 371285582912802789, 371285582914267955, 371285582941434010, 371285583033459296, 371285583250554754, 371285583252020018, 371285582790730212, 371285582186274243]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 44310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 44300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480050143009155, 362480078262198989⟩, ⟨242972292515979083, 243814518050814525⟩, true⟩

def words02 : List Nat := [371285581581175689, 371285581190095263, 371285580573000224, 371285580398380918, 371285580223311610, 371285579989098247, 371285579169738884, 371285578722274725, 371285578274059949, 371285578251327138]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 44320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 44300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490203596578369, 362490231729111836⟩, ⟨(-207194968796588029), (-206352151669442303)⟩, true⟩

def words03 : List Nat := [371285578128375683, 371285577903508912, 371285577871165870, 371285577872797346, 371285577903695277, 371285577997429211, 371285578090475355, 371285578091966966, 371285577867330085, 371285577974084448]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 44330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 44300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362463663721550052, 362463691867126720⟩, ⟨969693353888863435, 970536749419739545⟩, true⟩

def words04 : List Nat := [371285578231509350, 371285578232975763, 371285577812838605, 371285577384105674, 371285576954834398, 371285576553109425, 371285575955131649, 371285575785786716, 371285575615968083, 371285575446595035]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 44340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 44300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490751523792558, 362490779682668954⟩, ⟨(-231744185608825512), (-230900200170898482)⟩, true⟩

def words05 : List Nat := [371285574968768350, 371285574985198697, 371285575318508993, 371285575319975923, 371285575049660773, 371285574701798803, 371285574511831456, 371285574513447228, 371285574536730605, 371285574655727026]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 44350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 44300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362468220794329698, 362468248966454074⟩, ⟨767747573736573246, 768592146921911558⟩, true⟩

def words06 : List Nat := [371285574769431885, 371285574770899475, 371285574298469333, 371285573993197979, 371285573687234785, 371285573505297291, 371285572900804058, 371285572258286014, 371285571615185824, 371285571304676340]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 44360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 44300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362461975506314404, 362462003691639549⟩, ⟨1044992559180376564, 1045837718152553976⟩, true⟩

def words07 : List Nat := [371285571032534681, 371285571151368319, 371285571167910968, 371285571169388217, 371285570731032753, 371285570424233107, 371285570265164759, 371285570266632212, 371285569739643807, 371285569210300040]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 44370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 44300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476286480883946, 362476314679344055⟩, ⟨409898394514797722, 410744136482130522⟩, true⟩

def words08 : List Nat := [371285568680313691, 371285568658405598, 371285568732579488, 371285569024472749, 371285569160563180, 371285569162031012, 371285568621631106, 371285568164788132, 371285567755913952, 371285567757435566]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 44380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 44300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482375481065085, 362482403692911602⟩, ⟨139621431804120273, 140467768060102259⟩, true⟩

def words09 : List Nat := [371285567550088174, 371285567343090490, 371285567369405424, 371285567423460004, 371285567581327074, 371285567739740899, 371285567894817067, 371285567896285448, 371285567450796805, 371285567381381425]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 44390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 44300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 44300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk443
