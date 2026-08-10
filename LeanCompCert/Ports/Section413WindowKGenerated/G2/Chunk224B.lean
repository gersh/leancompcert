import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk224A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk224B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk224A

def state06 : KState := ⟨⟨360664506570935892, 360664509529189923⟩, ⟨(-1892691118480466226), (-1892646163965812946)⟩, true⟩

def words05 : List Nat := [360580224298008245, 360580226173684475, 360580230028589797, 360580232550612343, 360580233378770559, 360580234206880254, 360580235689314064, 360580238360571424, 360580242112862309, 360580245864884425]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 22450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 22400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360659498082589458, 360659501043615000⟩, ⟨(-1780600856895205908), (-1780555840118564592)⟩, true⟩

def words06 : List Nat := [360580248615337988, 360580251090791818, 360580253498178326, 360580255905435938, 360580257805316724, 360580258503196331, 360580258503455360, 360580258201369611, 360580259572868025, 360580263099592991]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 22460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 22400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360505769141355860, 360505772105118820⟩, ⟨1674749259194269029, 1674794337494352995⟩, true⟩

def words07 : List Nat := [360580267513174057, 360580271926417592, 360580274754600254, 360580276941380023, 360580278027896973, 360580279114393293, 360580279114634233, 360580279013194589, 360580276946558833, 360580273632587431]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 22470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 22400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360622461308522628, 360622464275030204⟩, ⟨(-949001561838583044), (-948956421825696092)⟩, true⟩

def words08 : List Nat := [360580270318845341, 360580268979448911, 360580270282211998, 360580271920536808, 360580271920804955, 360580271879325309, 360580269873666559, 360580269408412956, 360580269680604797, 360580271556972951]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 22480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 22400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360625420995416698, 360625423964701847⟩, ⟨(-1015727912243147465), (-1015682709749241103)⟩, true⟩

def words09 : List Nat := [360580271664393301, 360580271771828050, 360580273297291877, 360580276171612288, 360580277738590113, 360580279305475226, 360580279874903292, 360580280503988658, 360580282510600265, 360580284517132884]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 22490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 22400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 22400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk224B
