import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk109

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362412508169298281, 362412509676856931⟩, ⟨804406773865056670, 804417897694807174⟩, true⟩

def state01 : KState := ⟨⟨362539253694394344, 362539255204824921⟩, ⟨(-577637750770711990), (-577626595622344912)⟩, true⟩

def words00 : List Nat := [371286302714201161, 371286300142915292, 371286296810297879, 371286299343797766, 371286300529987052, 371286300530314238, 371286298593918151, 371286300358183459, 371286310511951873, 371286315364698229]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 10900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 10900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362518660886406744, 362518662399773117⟩, ⟨(-352812884785771728), (-352801697593600310)⟩, true⟩

def words01 : List Nat := [371286320210946300, 371286325056420627, 371286333350269566, 371286338362134998, 371286344065119068, 371286349767177380, 371286355416772252, 371286355417093720, 371286354551599884, 371286357510331345]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 10910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 10900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362406250613287740, 362406252129516650⟩, ⟨875482736994192967, 875493955460418897⟩, true⟩

def words02 : List Nat := [371286367009301689, 371286367221266503, 371286367221509040, 371286365721895669, 371286364222438625, 371286363342927940, 371286358350576812, 371286356306543906, 371286354262773366, 371286352216932974]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 10920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 10900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362581466864714238, 362581468383847363⟩, ⟨(-1040651278710773578), (-1040640028486335418)⟩, true⟩

def words03 : List Nat := [371286344889361183, 371286342756677178, 371286342474635313, 371286342474964773, 371286339976346813, 371286336150945696, 371286336846734621, 371286337198656717, 371286345894596619, 371286354589085794]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 10930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 10900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362496539402740829, 362496540924788563⟩, ⟨(-111568493934416463), (-111557211809846463)⟩, true⟩

def words04 : List Nat := [371286361598651206, 371286361598973287, 371286360102921579, 371286362704976752, 371286365905320711, 371286365905644386, 371286361278069904, 371286355757526433, 371286353051196601, 371286353981878341]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 10940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 10900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362421385754658320, 362421387279610170⟩, ⟨712093568379330977, 712104882318953345⟩, true⟩

def words05 : List Nat := [371286361576361917, 371286369169591775, 371286376723198810, 371286376723521226, 371286373193055589, 371286370073698066, 371286372156330395, 371286372156652995, 371286366281189455, 371286360352814455]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 10950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 10900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362413769054126544, 362413770581970713⟩, ⟨796122781466246480, 796134127120562716⟩, true⟩

def words06 : List Nat := [371286355232195790, 371286355232560789, 371286357855076859, 371286362098645373, 371286364221963485, 371286364222286313, 371286355286830795, 371286350501376302, 371286345716629731, 371286344340140318]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 10960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 10900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497403616440485, 362497405147229050⟩, ⟨(-121776723834301857), (-121765345865151461)⟩, true⟩

def words07 : List Nat := [371286337725330818, 371286330413954115, 371286324085543709, 371286324085899549, 371286321607120714, 371286321641285393, 371286321669720199, 371286321670045523, 371286315406769328, 371286316417071037]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 10970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 10900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486529161896232, 362486530695568803⟩, ⟨(-2113789290336532), (-2102379639733458)⟩, true⟩

def words08 : List Nat := [371286324549086558, 371286326082664083, 371286326082910448, 371286325972447625, 371286327337847698, 371286327338203563, 371286330309923199, 371286335931268416, 371286339395898219, 371286339413643616]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 10980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 10900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362598251029882963, 362598252566485192⟩, ⟨(-1230362203086027704), (-1230350761223761322)⟩, true⟩

def words09 : List Nat := [371286345409608154, 371286351404651987, 371286365660794298, 371286371195699085, 371286375446392223, 371286379696409536, 371286387338992885, 371286392327580687, 371286402496914263, 371286412664546845]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 10990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 10900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 10900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk109
