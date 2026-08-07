import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk664

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360556778241351091, 360556806538525135⟩, ⟨1734154190424146879, 1735423406898457549⟩, true⟩

def state01 : KState := ⟨⟨360570509890045492, 360570538196076192⟩, ⟨822389643357027681, 823659447955080025⟩, true⟩

def words00 : List Nat := [360582942040358576, 360582941755231636, 360582941805903025, 360582941944952936, 360582941945818438, 360582941895447865, 360582941618595955, 360582941376877490, 360582941134905038, 360582940837966798]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 66400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 66400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360569325009883587, 360569353324840896⟩, ⟨901090162547832100, 902360560005235634⟩, true⟩

def words01 : List Nat := [360582940652053535, 360582940327839128, 360582940003455187, 360582939920432785, 360582939921217123, 360582939826007273, 360582939730685913, 360582939484370815, 360582939203705197, 360582939000239952]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 66410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 66400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360570930909634977, 360570959233426859⟩, ⟨794348763577899957, 795619747871525721⟩, true⟩

def words02 : List Nat := [360582938796458496, 360582938770792967, 360582938518839139, 360582938090551839, 360582937662122277, 360582937174089204, 360582936799432892, 360582936611106376, 360582936422697063, 360582936047334304]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 66420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 66400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360584837258347554, 360584865590976063⟩, ⟨(-129495784599782235), (-128224213244396895)⟩, true⟩

def words03 : List Nat := [360582935913636123, 360582935960500971, 360582936144803506, 360582936184340893, 360582936185205343, 360582936021922638, 360582935858476151, 360582935690477396, 360582935665056165, 360582935695079789]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 66430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 66400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360559682728023884, 360559711069569353⟩, ⟨1541738304964121737, 1543010468806153081⟩, true⟩

def words04 : List Nat := [360582935695914655, 360582935612857899, 360582935358566449, 360582935070792499, 360582934782760771, 360582934390089347, 360582933771331796, 360582933003426090, 360582932235364090, 360582931693629642]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 66440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 66400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360538794205609398, 360538822555992420⟩, ⟨2929808099115611327, 2931080850257648675⟩, true⟩

def words05 : List Nat := [360582931344966004, 360582930878010393, 360582930410968470, 360582929786146949, 360582929000527374, 360582928158561512, 360582927316331419, 360582926700271941, 360582926150475901, 360582925487834997]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 66450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 66400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580403689652935, 360580432048885447⟩, ⟨164240549391837124, 165513888712443742⟩, true⟩

def words06 : List Nat := [360582924825002042, 360582924298793694, 360582923957213233, 360582923841726820, 360582923726193348, 360582923395001074, 360582922885632109, 360582922602437469, 360582922318979019, 360582922102875405]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 66460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 66400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360561687268952318, 360561715637117272⟩, ⟨1408440684701695780, 1409714617807324306⟩, true⟩

def words07 : List Nat := [360582922066249884, 360582921916797130, 360582921767158175, 360582921652597721, 360582921652788963, 360582921593507556, 360582921534125740, 360582921361946912, 360582921048551295, 360582920730646264]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 66470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 66400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360564303174635194, 360564331551629344⟩, ⟨1234505504646301759, 1235780024761441229⟩, true⟩

def words08 : List Nat := [360582920412441208, 360582920193035201, 360582919907595363, 360582919493921634, 360582919080101167, 360582918610005526, 360582918313587019, 360582918094134244, 360582917874586307, 360582917504776606]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 66480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 66400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360574464705885638, 360574493091746823⟩, ⟨558746577705688630, 560021687432320802⟩, true⟩

def words09 : List Nat := [360582917226008894, 360582917173218814, 360582917120160283, 360582916966070195, 360582916586259528, 360582915999357906, 360582915412295039, 360582914947678640, 360582914596153334, 360582914470505204]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 66490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 66400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 66400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk664
