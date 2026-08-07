import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk640

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496046936820263, 362496107299621973⟩, ⟨(-682868551933809890), (-680259206403610852)⟩, true⟩

def state01 : KState := ⟨⟨362489912857954638, 362489973240253566⟩, ⟨(-290236753107920010), (-287626159657579280)⟩, true⟩

def words00 : List Nat := [371285478626905859, 371285478717528091, 371285478987073602, 371285479257474700, 371285479459989921, 371285479462166091, 371285479458948962, 371285479581455706, 371285479781357700, 371285479853809712]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 64000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 64000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362493170257074240, 362493230659167146⟩, ⟨(-498736508668593444), (-496124648105489826)⟩, true⟩

def words01 : List Nat := [371285479922153615, 371285479991217827, 371285480303689712, 371285480514910022, 371285480719731171, 371285480925379606, 371285481129061507, 371285481131238195, 371285481130577944, 371285481254313966]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 64010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 64000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362494703509561227, 362494763931056405⟩, ⟨(-596845494863037341), (-594232392064736697)⟩, true⟩

def words02 : List Nat := [371285481594225638, 371285481781776448, 371285481967859426, 371285482154691484, 371285482390115562, 371285482504197346, 371285482817422364, 371285483131502837, 371285483397920757, 371285483545117333]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 64020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 64000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362515796280411921, 362515856721612086⟩, ⟨(-1947531218812712503), (-1944916854206054059)⟩, true⟩

def words03 : List Nat := [371285483816075379, 371285484088180977, 371285484603216239, 371285484818440610, 371285484989637699, 371285485161512517, 371285485576561562, 371285485899035486, 371285486374764480, 371285486851463181]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 64030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 64000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362504456493500049, 362504516954375564⟩, ⟨(-1221304786462760363), (-1218689161747620143)⟩, true⟩

def words04 : List Nat := [371285487326487757, 371285487626750607, 371285488026528809, 371285488427399445, 371285488900945975, 371285489101296739, 371285489274420885, 371285489448302429, 371285489798656112, 371285490098249234]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 64040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 64000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362477160582156348, 362477221062594005⟩, ⟨527199882121362550, 529816759893898038⟩, true⟩

def words05 : List Nat := [371285490553929494, 371285491010454897, 371285491420301390, 371285491505818907, 371285491615058308, 371285491725395143, 371285491935164661, 371285491937342784, 371285491822432233, 371285491695748765]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 64050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 64000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362494310237744291, 362494370737691044⟩, ⟨(-571471263801201341), (-568853136181069183)⟩, true⟩

def words06 : List Nat := [371285491593799062, 371285491596221683, 371285491648875806, 371285491798858839, 371285491910981176, 371285491913159652, 371285491783219478, 371285491842026816, 371285492116172086, 371285492257002729]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 64060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 64000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498580759180684, 362498641279047467⟩, ⟨(-845130606069487295), (-842511202076337531)⟩, true⟩

def words07 : List Nat := [371285492356305402, 371285492456314053, 371285492709583147, 371285492851052678, 371285492996761007, 371285493143267433, 371285493284458659, 371285493286678857, 371285493473513768, 371285493681443243]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 64070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 64000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362495767599674117, 362495828138934527⟩, ⟨(-664848741657554662), (-662228094819254672)⟩, true⟩

def words08 : List Nat := [371285494131805162, 371285494272310242, 371285494390198871, 371285494508800223, 371285494638856486, 371285494684702652, 371285494906938325, 371285495130069710, 371285495353154842, 371285495516650287]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 64080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 64000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362510991740741365, 362511052299703269⟩, ⟨(-1640588374512020780), (-1637966464904969300)⟩, true⟩

def words09 : List Nat := [371285495922995270, 371285496330478987, 371285496950957795, 371285497284446375, 371285497580490560, 371285497877234731, 371285498297516836, 371285498598129683, 371285498998288010, 371285499399359984]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 64090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 64000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 64000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk640
