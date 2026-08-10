import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk781A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk781B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk781A

def state06 : KState := ⟨⟨360566823866655027, 360566863584833421⟩, ⟨1199339427653073593, 1201436113867492471⟩, true⟩

def words05 : List Nat := [360582235178187526, 360582235392546530, 360582235518339565, 360582235567608187, 360582235568566191, 360582235454733382, 360582235388946432, 360582235390062480, 360582235276175012, 360582235080660795]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 78150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 78100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360605436653080072, 360605476381811036⟩, ⟨(-1818766858404515996), (-1816669347349709276)⟩, true⟩

def words06 : List Nat := [360582234884899005, 360582234845330003, 360582235052742787, 360582235260363946, 360582235329718668, 360582235491700440, 360582235816872610, 360582236142363944, 360582236399238806, 360582236697690970]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 78160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 78100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360601126721303097, 360601166460656780⟩, ⟨(-1481826101149450157), (-1479727759664135121)⟩, true⟩

def words07 : List Nat := [360582236898236368, 360582237098898091, 360582237462747854, 360582237932795670, 360582238317823837, 360582238703042011, 360582238945962591, 360582239025798470, 360582239268801852, 360582239512169755]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 78170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 78100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360608521507306421, 360608561257193163⟩, ⟨(-2060012116554999873), (-2057912951543793057)⟩, true⟩

def words08 : List Nat := [360582239850306912, 360582240209935583, 360582240421393832, 360582240632939512, 360582240765318116, 360582240992664090, 360582241317163933, 360582241641876388, 360582241867968321, 360582242205748064]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 78180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 78100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360618559385442673, 360618599145867067⟩, ⟨(-2844887566391792651), (-2842787577389043349)⟩, true⟩

def words09 : List Nat := [360582242706581546, 360582243207742513, 360582243871881711, 360582244373064523, 360582244735415326, 360582245097838690, 360582245456212064, 360582245896600973, 360582246362385347, 360582246828410909]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 78190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 78100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 78100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk781B
