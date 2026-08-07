import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk196

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362444478110183158, 362444483244443087⟩, ⟨803049511222475244, 803117572422687906⟩, true⟩

def state01 : KState := ⟨⟨362479883965403365, 362479889105094710⟩, ⟨109044538048298902, 109112705731678632⟩, true⟩

def words00 : List Nat := [371285456540730214, 371285456095666905, 371285455956738067, 371285457184298197, 371285457984541286, 371285457985148433, 371285455324693948, 371285453766224029, 371285453240403364, 371285453241032073]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 19600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 19600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487112788494083, 362487117933716383⟩, ⟨(-32702729600630269), (-32634453426859103)⟩, true⟩

def words01 : List Nat := [371285452957765104, 371285452660996291, 371285453404024060, 371285453523665374, 371285454443886117, 371285455364253387, 371285456260660950, 371285456261270170, 371285454607102571, 371285454692626385]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 19610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 19600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362444519784831346, 362444524935471259⟩, ⟨803130061450509136, 803198443946230098⟩, true⟩

def words02 : List Nat := [371285455880628436, 371285455881236149, 371285453614714652, 371285451352177445, 371285449089629734, 371285447530676429, 371285444677108664, 371285443728331973, 371285442779446200, 371285441820032963]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 19620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 19600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362491466736809710, 362491471892946478⟩, ⟨(-118657643279253423), (-118589152852367485)⟩, true⟩

def words03 : List Nat := [371285439866139271, 371285439996853371, 371285442081182033, 371285442081790146, 371285440716142552, 371285438092792719, 371285435469469149, 371285435097829049, 371285433748019569, 371285434056133059]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 19630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 19600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478786931841123, 362478792093473968⟩, ⟨130439219491721763, 130507817889706641⟩, true⟩

def words04 : List Nat := [371285434369298760, 371285434369918637, 371285433497654129, 371285433915601801, 371285435134689468, 371285435135303657, 371285434831233761, 371285434127696284, 371285433712010832, 371285433712704997]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 19640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 19600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362438900915743018, 362438906082853219⟩, ⟨914659485715587219, 914728191770814303⟩, true⟩

def words05 : List Nat := [371285435164769164, 371285436954872701, 371285438752022881, 371285438752632198, 371285437678250335, 371285437406100252, 371285438198323172, 371285438198932132, 371285435823859879, 371285433457816130]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 19650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 19600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362452602895937719, 362452608068507157⟩, ⟨645403660149638632, 645472473561223390⟩, true⟩

def words06 : List Nat := [371285431299534785, 371285431300205977, 371285430736091396, 371285430900912235, 371285430901389647, 371285430587491433, 371285426836079572, 371285425298355389, 371285423760478416, 371285423140879360]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 19660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 19600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362434063573157610, 362434068751278342⟩, ⟨1010347035635326660, 1010415958269154774⟩, true⟩

def words07 : List Nat := [371285421473139853, 371285419808668230, 371285418714568106, 371285418715245370, 371285418049898693, 371285418093969549, 371285418094433296, 371285417580794672, 371285413633805744, 371285411025580637]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 19670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 19600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362459548484405404, 362459553667958618⟩, ⟨508745294235844232, 508814323809000804⟩, true⟩

def words08 : List Nat := [371285408417271915, 371285408377718144, 371285405890993880, 371285403404730444, 371285400918479773, 371285399006694742, 371285396057939267, 371285395676974118, 371285395295836102, 371285394923611691]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 19680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 19600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362526447027582777, 362526452216650171⟩, ⟨(-809024127361852915), (-808954989186496073)⟩, true⟩

def words09 : List Nat := [371285393611695257, 371285392609988792, 371285392713925994, 371285392714536608, 371285390873512632, 371285388695932467, 371285386905057570, 371285386905741505, 371285388510935310, 371285390595961552]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 19690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 19600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 19600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk196
