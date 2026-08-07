import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk781

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360554312379542485, 360554352034371856⟩, ⟨2175520468211328010, 2177612204970007910⟩, true⟩

def state01 : KState := ⟨⟨360590431696422643, 360590471361773369⟩, ⟨(-645553465264787381), (-643460906736509793)⟩, true⟩

def words00 : List Nat := [360582234036848153, 360582233844806359, 360582233750139796, 360582233766662315, 360582233767691672, 360582233632300904, 360582233504660780, 360582233472531156, 360582233479339059, 360582233585957716]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 78100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 78100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360572123213868298, 360572162889869227⟩, ⟨784584616312318721, 786678006777977115⟩, true⟩

def words01 : List Nat := [360582233586968763, 360582233565771182, 360582233544376434, 360582233588283951, 360582233589220255, 360582233561613631, 360582233533890818, 360582233401807559, 360582233140443616, 360582233012843856]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 78110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 78100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586156514165878, 360586196200667913⟩, ⟨(-311739983271812992), (-309645772406218004)⟩, true⟩

def words02 : List Nat := [360582232919557385, 360582232986185557, 360582232987179742, 360582232971938361, 360582232956516745, 360582232944942856, 360582232986553021, 360582233028362375, 360582233029365918, 360582233039151918]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 78120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 78100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360610256502985463, 360610296200014972⟩, ⟨(-2194883357779868246), (-2192788324349341976)⟩, true⟩

def words03 : List Nat := [360582233097774690, 360582233156724930, 360582233241059741, 360582233329816676, 360582233330845972, 360582233279622561, 360582233339399805, 360582233536234868, 360582233896270269, 360582234256549323]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 78130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 78100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360591147459699228, 360591187167372801⟩, ⟨(-701719508185300656), (-699623642974978038)⟩, true⟩

def words04 : List Nat := [360582234483586720, 360582234589818611, 360582234744518512, 360582234899546489, 360582235013308170, 360582235032581601, 360582235033587498, 360582234953735350, 360582234873654685, 360582234964035992]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 78140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 78100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk781
