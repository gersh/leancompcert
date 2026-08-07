import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk072

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360550259306877938, 360550259579544075⟩, ⟨256007668861308858, 256009000252706914⟩, true⟩

def state01 : KState := ⟨⟨360602905482942182, 360602905756401333⟩, ⟨(-123965289377836781), (-123963952272715577)⟩, true⟩

def words00 : List Nat := [360585814018063843, 360585814018148279, 360585811872689898, 360585794912959441, 360585777957923610, 360585747642279781, 360585727120832315, 360585725707120946, 360585724293793151, 360585714804761795]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 7200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 7200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360814655119767299, 360814655394020907⟩, ⟨(-1651801757451473130), (-1651800414614306740)⟩, true⟩

def words01 : List Nat := [360585736274665071, 360585757738639571, 360585798277561400, 360585819850998503, 360585823419084638, 360585826986188868, 360585829833215295, 360585842481465428, 360585874173072867, 360585905855921710]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 7210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 7200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360683785915795082, 360683786190851972⟩, ⟨(-707420541357060353), (-707419192716262513)⟩, true⟩

def words02 : List Nat := [360585925347124619, 360585937936718088, 360585960677210195, 360585983411433248, 360585995063368842, 360585995063453228, 360585987820288484, 360585965945606453, 360585944076959996, 360585954743926753]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 7220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 7200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360567983759669760, 360567984035522875⟩, ⟨129943290046420575, 129944644447956539⟩, true⟩

def words03 : List Nat := [360585967584161740, 360585980420861189, 360585983716847900, 360585983716932371, 360585968144732734, 360585947424109438, 360585926709187132, 360585934670039863, 360585934670115347, 360585932190833367]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 7230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 7200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360785789481644997, 360785789758296516⟩, ⟨(-1447850997453261156), (-1447849637267347670)⟩, true⟩

def words04 : List Nat := [360585932012965978, 360585948525810504, 360585983955355468, 360586019375136111, 360586035987182014, 360586035987266654, 360586050446436692, 360586067124614317, 360586086359965039, 360586113901550227]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 7240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 7200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360689414375326260, 360689414652785818⟩, ⟨(-747930689386200426), (-747929323338093426)⟩, true⟩

def words05 : List Nat := [360586131937015308, 360586149967517846, 360586186863942389, 360586236298322527, 360586280611605548, 360586324912689782, 360586355719909453, 360586379892550118, 360586394084735872, 360586408273039490]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 7250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 7200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360607168551040778, 360607168829298812⟩, ⟨(-150689213417814304), (-150687841568645564)⟩, true⟩

def words06 : List Nat := [360586433327021572, 360586439625446784, 360586439625523161, 360586435962410917, 360586432300293358, 360586429470586218, 360586436624331120, 360586443776123652, 360586443776199317, 360586444329014306]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 7260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 7200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360547035762219687, 360547036041280957⟩, ⟨286131703602045020, 286133081294772594⟩, true⟩

def words07 : List Nat := [360586449790110231, 360586455249729432, 360586460044785206, 360586460044870190, 360586446143208127, 360586414843292347, 360586383551962802, 360586359648484360, 360586345435516617, 360586340035964305]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 7270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 7200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360473063453002112, 360473063732873410⟩, ⟨824459214572179883, 824460598165946651⟩, true⟩

def words08 : List Nat := [360586334637881896, 360586319444078337, 360586304387717923, 360586306207499065, 360586306207570405, 360586298638230757, 360586272443936408, 360586231202161321, 360586189971686298, 360586158465132114]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 7280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 7200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360384463026164574, 360384463306838995⟩, ⟨1470978289582914671, 1470979679035545013⟩, true⟩

def words09 : List Nat := [360586142953648321, 360586135346675606, 360586127741780800, 360586103154651891, 360586079664700943, 360586051193204205, 360586022729486262, 360586012889403001, 360585994979450415, 360585967372460303]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 7290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 7200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 7200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk072
