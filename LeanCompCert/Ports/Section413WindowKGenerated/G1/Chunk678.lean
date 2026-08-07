import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk678

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362475198528256241, 362475266578923879⟩, ⟨688151740921472626, 691267868448109636⟩, true⟩

def state01 : KState := ⟨⟨362477552060785615, 362477620132113964⟩, ⟨528633318647754988, 531750847076961312⟩, true⟩

def words00 : List Nat := [371285462188363394, 371285462190721418, 371285462120066520, 371285462026370407, 371285461931790522, 371285461892561670, 371285461811431796, 371285461881298215, 371285461905960333, 371285461908357542]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 67800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 67800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494511249499199, 362494579341715038⟩, ⟨(-621486022611423354), (-618367077694253394)⟩, true⟩

def words01 : List Nat := [371285461801293899, 371285461811042509, 371285461957520961, 371285461959838021, 371285461853487526, 371285461677361754, 371285461514612018, 371285461517164398, 371285461570369236, 371285461707387997]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 67810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 67800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481845495689767, 362481913608855748⟩, ⟨237480513923264301, 240600879780904307⟩, true⟩

def words02 : List Nat := [371285461816405346, 371285461818721779, 371285461637898224, 371285461549139798, 371285461459180687, 371285461436402577, 371285461218198587, 371285460981594952, 371285460744074807, 371285460724877876]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 67820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 67800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362466769494443071, 362466837628466985⟩, ⟨1260240058696527751, 1263361839454732661⟩, true⟩

def words03 : List Nat := [371285460783392860, 371285460895160640, 371285461005457088, 371285461007785419, 371285460910522744, 371285460880484822, 371285460849310511, 371285460841820552, 371285460568965548, 371285460297091023]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 67830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 67800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475110893226964, 362475179047998059⟩, ⟨694378257309994580, 697501445663226910⟩, true⟩

def words04 : List Nat := [371285460024158283, 371285459950319196, 371285459799838467, 371285459834896836, 371285459836690073, 371285459837265964, 371285459547618940, 371285459345433869, 371285459142017744, 371285459098781600]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 67840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 67800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362478404616799056, 362478472792710280⟩, ⟨470896043471368855, 474020666286476797⟩, true⟩

def words05 : List Nat := [371285458949053266, 371285458754249295, 371285458578275413, 371285458580830332, 371285458504865483, 371285458458399672, 371285458411122200, 371285458364559863, 371285458166357681, 371285458066307193]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 67850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 67800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474427118262437, 362474495314790056⟩, ⟨740827914770231145, 743953936722485473⟩, true⟩

def words06 : List Nat := [371285458056527315, 371285458058845518, 371285457862801830, 371285457667686329, 371285457471690228, 371285457288383808, 371285456995648788, 371285456920787786, 371285456845177274, 371285456769581901]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 67860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 67800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362482815058294888, 362482883275824823⟩, ⟨171506776236292291, 174634223719646593⟩, true⟩

def words07 : List Nat := [371285456631317303, 371285456655840376, 371285456760391209, 371285456762709751, 371285456578216611, 371285456363696973, 371285456148261113, 371285456128558572, 371285456001490902, 371285455966215508]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 67870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 67800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476776538503567, 362476844776944033⟩, ⟨581364181651783401, 584493048650924707⟩, true⟩

def words08 : List Nat := [371285455930065197, 371285455830142078, 371285455440297367, 371285455268457275, 371285455095501319, 371285454989293441, 371285454755985868, 371285454513769008, 371285454270586859, 371285454189945225]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 67880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 67800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470227810950592, 362470296070291553⟩, ⟨1026044798641718819, 1029175084679328561⟩, true⟩

def words09 : List Nat := [371285454154657024, 371285454247117958, 371285454293101197, 371285454295420841, 371285454081808730, 371285453904913876, 371285453726771038, 371285453728855601, 371285453508633347, 371285453288033517]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 67890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 67800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 67800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk678
