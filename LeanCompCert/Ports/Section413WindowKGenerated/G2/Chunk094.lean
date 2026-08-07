import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk094

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360492783426638209, 360492783904332803⟩, ⟨774846167388435303, 774849211493095139⟩, true⟩

def state01 : KState := ⟨⟨360550118694689213, 360550119173450999⟩, ⟨235317391438114142, 235320445579745540⟩, true⟩

def words00 : List Nat := [360575205903308456, 360575191563353129, 360575185578251639, 360575188208299514, 360575188208405355, 360575180229593898, 360575161071628836, 360575146707070057, 360575132345529910, 360575126659697519]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 9400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 9400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360591194183134906, 360591194662972587⟩, ⟨(-151559917740021272), (-151556853468798824)⟩, true⟩

def words01 : List Nat := [360575124002536921, 360575115629373161, 360575110107027430, 360575118750480163, 360575119335154595, 360575119919722370, 360575119919823227, 360575113620927226, 360575105824896159, 360575107532788021]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 9410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 9400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360631603828318348, 360631604309223296⟩, ⟨(-532216326985989625), (-532213252655800307)⟩, true⟩

def words02 : List Nat := [360575120448269884, 360575133771503893, 360575141117772493, 360575148462493844, 360575148462589253, 360575153824504339, 360575160773427840, 360575167720898292, 360575167721000875, 360575171984691879]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 9420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 9400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360974456967036564, 360974457449011125⟩, ⟨(-3767354129093626734), (-3767351044671693904)⟩, true⟩

def words03 : List Nat := [360575189153853111, 360575206319407988, 360575234664928435, 360575257041464487, 360575267723911524, 360575278404105188, 360575300257184840, 360575331371392116, 360575373651788839, 360575415923254141]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 9430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 9400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360683511445523578, 360683511928580476⟩, ⟨(-1020306433564358363), (-1020303338919927637)⟩, true⟩

def words04 : List Nat := [360575452553780498, 360575478093138195, 360575498717322096, 360575519337169872, 360575537055929387, 360575543692173184, 360575543692274403, 360575543089582767, 360575543321154769, 360575554745327918]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 9440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 9400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360378454435680863, 360378454919807449⟩, ⟨1864478291541693173, 1864481396300078561⟩, true⟩

def words05 : List Nat := [360575569173225485, 360575583598091894, 360575590626810215, 360575592901078166, 360575592901173486, 360575589591962403, 360575586283419919, 360575582073075930, 360575566812732841, 360575545976498790]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 9450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 9400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360624625058760044, 360624625543959536⟩, ⟨(-465068056132089096), (-465064941218552976)⟩, true⟩

def words06 : List Nat := [360575525144643303, 360575515441394832, 360575521038084212, 360575529395939028, 360575529396043836, 360575528282682697, 360575516129289575, 360575515094759238, 360575516257546388, 360575521442891164]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 9460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 9400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360688431860190146, 360688432346475554⟩, ⟨(-1070099919907771447), (-1070096794705216709)⟩, true⟩

def words07 : List Nat := [360575521442995056, 360575515343740324, 360575514249896560, 360575524884705149, 360575532327142037, 360575539768026817, 360575540209746573, 360575541029162710, 360575552937621863, 360575564843606109]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 9470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 9400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360731310043375843, 360731310530735160⟩, ⟨(-1477099569676209174), (-1477096434287653470)⟩, true⟩

def words08 : List Nat := [360575581256428530, 360575596425681505, 360575604852847989, 360575613278249849, 360575613887421377, 360575622496807737, 360575637842976391, 360575653185932118, 360575662855770759, 360575679255391398]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 9480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 9400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360815858872178559, 360815859360616492⟩, ⟨(-2279677148141561340), (-2279674002511578584)⟩, true⟩

def words09 : List Nat := [360575706712213619, 360575734163286287, 360575763063375468, 360575786293340759, 360575799911717479, 360575813527234319, 360575838186772216, 360575868413723958, 360575893676023152, 360575918933028704]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 9490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 9400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 9400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk094
