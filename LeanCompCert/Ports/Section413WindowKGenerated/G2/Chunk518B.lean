import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk518A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk518B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk518A

def state06 : KState := ⟨⟨360660557747669566, 360660574670011477⟩, ⟨(-4076843271092715517), (-4076250295265220975)⟩, true⟩

def words05 : List Nat := [360581965449974129, 360581966236890866, 360581967394851024, 360581968498215320, 360581969282656869, 360581970067136546, 360581970960759317, 360581972106061401, 360581973622310111, 360581975138662965]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 51850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 51800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360609060088161936, 360609077017351919⟩, ⟨(-1406143810971979047), (-1405550479971382715)⟩, true⟩

def words06 : List Nat := [360581976432788418, 360581977355995316, 360581978177064123, 360581978998301284, 360581979465898584, 360581979562671504, 360581979563319419, 360581979404024011, 360581979455688841, 360581979978930231]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 51860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 51800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360572202821128423, 360572219757072432⟩, ⟨505970875669920340, 506564557036542338⟩, true⟩

def words07 : List Nat := [360581980872971794, 360581981767116467, 360581982474717071, 360581982974434278, 360581983354291075, 360581983734335406, 360581984103827048, 360581984104545182, 360581984103310289, 360581983915843376]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 51870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 51800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360571957367071629, 360571974309793131⟩, ⟨518752528788409484, 519346561805184042⟩, true⟩

def words08 : List Nat := [360581983741842056, 360581983944010448, 360581984234206317, 360581984524540238, 360581984525208542, 360581984500593550, 360581984105191814, 360581983654250368, 360581983203115546, 360581982915725010]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 51880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 51800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360598241187801568, 360598258137372299⟩, ⟨(-845347965012324023), (-844753576555771549)⟩, true⟩

def words09 : List Nat := [360581982723498575, 360581982237841448, 360581981752065464, 360581981726536859, 360581981727138008, 360581981652568131, 360581981577919314, 360581981317223961, 360581981574383523, 360581981888811467]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 51890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 51800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 51800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk518B
