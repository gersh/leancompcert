import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk971

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360593356293041498, 360593418634215845⟩, ⟨(-1075583314374627503), (-1071495867555339589)⟩, true⟩

def state01 : KState := ⟨⟨360591458632515526, 360591520987130103⟩, ⟨(-891377001916663722), (-887288249986778462)⟩, true⟩

def words00 : List Nat := [360582383836903986, 360582383838313941, 360582383922782920, 360582384019058036, 360582384087919885, 360582384107657167, 360582384108912833, 360582384075382831, 360582384045431259, 360582384141149867]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 97100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 97100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360579664046272848, 360579726414166371⟩, ⟨254043787325573384, 258133828841745200⟩, true⟩

def words01 : List Nat := [360582384233877574, 360582384326853942, 360582384366414341, 360582384367824242, 360582384337439720, 360582384280444367, 360582384270507343, 360582384324184354, 360582384325461904, 360582384299553951]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 97110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 97100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580506492479312, 360580568873682984⟩, ⟨172187507055703470, 176278841318076542⟩, true⟩

def words02 : List Nat := [360582384273330813, 360582384260244820, 360582384277751586, 360582384295521902, 360582384296847028, 360582384207984881, 360582384013194351, 360582383924841970, 360582383836061447, 360582383749018288]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 97120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 97100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360575992741870499, 360576055136504576⟩, ⟨610654536915513743, 614747175741432481⟩, true⟩

def words03 : List Nat := [360582383731589381, 360582383661099417, 360582383603395552, 360582383670765408, 360582383710791285, 360582383751053183, 360582383752321462, 360582383727414885, 360582383665926288, 360582383602386205]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 97130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 97100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360570233308824492, 360570295716737547⟩, ⟨1170103710942640325, 1174197639753628163⟩, true⟩

def words04 : List Nat := [360582383538386429, 360582383490868712, 360582383337572573, 360582383131223949, 360582382924649530, 360582382691549070, 360582382541599429, 360582382438586135, 360582382335427763, 360582382156673251]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 97140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 97100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360589800445262060, 360589862866498772⟩, ⟨(-730985323229460753), (-726890099958643543)⟩, true⟩

def words05 : List Nat := [360582382033404291, 360582382016502065, 360582381999193237, 360582381979656524, 360582381896440388, 360582381710300563, 360582381523894196, 360582381443830299, 360582381493050039, 360582381571535169]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 97150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 97100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590730859721018, 360590793294380985⟩, ⟨(-821475947052381545), (-817379419513094469)⟩, true⟩

def words06 : List Nat := [360582381591913693, 360582381629182439, 360582381667509185, 360582381706255996, 360582381717685516, 360582381719098861, 360582381684250546, 360582381569168772, 360582381453819047, 360582381531411446]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 97160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 97100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360585677665678811, 360585740113619728⟩, ⟨(-330365312093447489), (-326267493978824551)⟩, true⟩

def words07 : List Nat := [360582381725017356, 360582381918893537, 360582382041555796, 360582382220128116, 360582382319426606, 360582382419088370, 360582382624223122, 360582382724079342, 360582382759885018, 360582382795893230]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 97170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 97100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360596236356947963, 360596298818226402⟩, ⟨(-1356518800728801129), (-1352419686408993135)⟩, true⟩

def words08 : List Nat := [360582382829136193, 360582382916494329, 360582383089184568, 360582383262141670, 360582383343887161, 360582383345297855, 360582383402104093, 360582383484459302, 360582383602377536, 360582383747011897]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 97180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 97100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592311657415943, 360592374132130418⟩, ⟨(-975047485290285782), (-970947065057042644)⟩, true⟩

def words09 : List Nat := [360582383838592427, 360582383930313268, 360582384103704668, 360582384344664722, 360582384513310195, 360582384682171860, 360582384795318143, 360582384859254754, 360582384963166213, 360582385067562595]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 97190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 97100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 97100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk971
