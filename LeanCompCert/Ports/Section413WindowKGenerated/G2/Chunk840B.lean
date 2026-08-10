import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk840A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk840B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk840A

def state06 : KState := ⟨⟨360575612855813657, 360575659057669350⟩, ⟨568168877587875858, 570791703387734036⟩, true⟩

def words05 : List Nat := [360582451199721793, 360582450861868365, 360582450523791836, 360582450327492301, 360582450201808765, 360582450040672574, 360582449879384853, 360582449647382145, 360582449426179674, 360582449346788881]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 84050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 84000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360586064408815965, 360586110622045445⟩, ⟨(-310464858602054045), (-307841076663572141)⟩, true⟩

def words06 : List Nat := [360582449327599057, 360582449367851586, 360582449368945294, 360582449300367442, 360582449231598242, 360582449037832394, 360582448931782164, 360582448950163107, 360582448951248289, 360582448942314461]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 84060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 84000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360582117951966402, 360582164176582227⟩, ⟨21267084747062271, 23891823990987093⟩, true⟩

def words07 : List Nat := [360582448970414892, 360582448998864601, 360582449048840619, 360582449050047488, 360582448994412780, 360582448812874994, 360582448631127343, 360582448446085678, 360582448334563966, 360582448332433690]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 84070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 84000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360579553404471137, 360579599640581440⟩, ⟨236812711554134280, 239438417309261464⟩, true⟩

def words08 : List Nat := [360582448330129357, 360582448257136508, 360582448136114644, 360582448112937258, 360582448089401499, 360582448008223847, 360582447785704251, 360582447492432644, 360582447198935024, 360582447047137622]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 84080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 84000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360551315850020867, 360551362097515626⟩, ⟨2611446769310778712, 2614073432442224762⟩, true⟩

def words09 : List Nat := [360582447014269808, 360582446939326611, 360582446864253547, 360582446718511499, 360582446511631845, 360582446207945789, 360582445903904592, 360582445642269913, 360582445384203166, 360582445015856200]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 84090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 84000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 84000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk840B
