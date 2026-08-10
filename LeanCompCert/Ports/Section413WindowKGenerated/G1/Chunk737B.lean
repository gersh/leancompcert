import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk737A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk737B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk737A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk737B
