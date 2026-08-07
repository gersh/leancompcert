import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk737

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362500862896169525, 362500943830886671⟩, ⟨(-1157395201901730503), (-1153366958176403339)⟩, true⟩

def state01 : KState := ⟨⟨362489263090095002, 362489344047698883⟩, ⟨(-302497984615378935), (-298468054025564089)⟩, true⟩

def words00 : List Nat := [371285294768332142, 371285294770866066, 371285294833491025, 371285294905525116, 371285295032357131, 371285295034890291, 371285294936721489, 371285294839126204, 371285294824065640, 371285294881983786]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 73700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 73700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362474523119809078, 362474604100219056⟩, ⟨784089160900973447, 788120772645301269⟩, true⟩

def words01 : List Nat := [371285295033651238, 371285295186374899, 371285295338695529, 371285295341228755, 371285295248255127, 371285295179185304, 371285295113880476, 371285295116419207, 371285294974493561, 371285294832349351]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 73710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 73700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486063127410405, 362486144130511583⟩, ⟨(-66653096637430350), (-62619811984007360)⟩, true⟩

def words02 : List Nat := [371285294727825568, 371285294730636309, 371285294776448130, 371285294848319311, 371285294888989188, 371285294891523036, 371285294705565628, 371285294704760524, 371285294815369654, 371285294829512221]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 73720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 73700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488732282274551, 362488813308447298⟩, ⟨(-263482191357014447), (-259447205516078369)⟩, true⟩

def words03 : List Nat := [371285294831439352, 371285294807732714, 371285294851625863, 371285294854418237, 371285294865199833, 371285294900516592, 371285294936138481, 371285294938720646, 371285294900054265, 371285294950878021]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 73730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 73700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476698621485786, 362476779670230463⟩, ⟨623952196482145367, 627988846891996023⟩, true⟩

def words04 : List Nat := [371285295142268713, 371285295144803168, 371285295091375895, 371285295030590840, 371285294968816526, 371285294909725891, 371285294773430580, 371285294775301669, 371285294776350218, 371285294773239169]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 73740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 73700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490559934308150, 362490641006009304⟩, ⟨(-398353082622049136), (-394314739056183830)⟩, true⟩

def words05 : List Nat := [371285294727668118, 371285294798942614, 371285295032185404, 371285295034720137, 371285295023325392, 371285294947384016, 371285294975359354, 371285295013236609, 371285295087464840, 371285295162825831]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 73750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 73700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489125386159528, 362489206480724808⟩, ⟨(-292581313884084004), (-288541283741447360)⟩, true⟩

def words06 : List Nat := [371285295224265044, 371285295226812198, 371285295113074029, 371285295116724372, 371285295175169191, 371285295177766063, 371285295134900602, 371285295075554215, 371285295114355262, 371285295170267563]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 73760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 73700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362472481941672593, 362472563059082870⟩, ⟨935356368602949716, 939398084134153752⟩, true⟩

def words07 : List Nat := [371285295408523662, 371285295647782387, 371285295851831573, 371285295854367088, 371285295813477496, 371285295797789744, 371285295819258054, 371285295821795009, 371285295650624546, 371285295480933428]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 73770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 73700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483118144685855, 362483199284773779⟩, ⟨150607807383981501, 154651196187197917⟩, true⟩

def words08 : List Nat := [371285295310082893, 371285295301853583, 371285295282649911, 371285295366695364, 371285295419380865, 371285295421917102, 371285295253692272, 371285295149769434, 371285295110798793, 371285295113425185]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 73780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 73700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482022847264358, 362482104010507579⟩, ⟨231483266234412524, 235528363779020012⟩, true⟩

def words09 : List Nat := [371285295086938436, 371285295059422197, 371285295172406802, 371285295250404941, 371285295383398007, 371285295517342470, 371285295625695412, 371285295628231960, 371285295491796043, 371285295451751198]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 73790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 73700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 73700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk737
