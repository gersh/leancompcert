import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk640A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk640B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk640A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk640B
