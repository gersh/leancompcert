import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk068

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362555008186701468, 362555008747706237⟩, ⟨(-490381863770033102), (-490379280122837838)⟩, true⟩

def state01 : KState := ⟨⟨362474360602852807, 362474361165591834⟩, ⟨58324891165022521, 58327486613983525⟩, true⟩

def words00 : List Nat := [371282915165124058, 371282915165316793, 371282914645138340, 371282925175485581, 371282941971279718, 371282941971472260, 371282935430966035, 371282928718291977, 371282926141380696, 371282926141599762]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 6800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 6800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362327549562557678, 362327550127032341⟩, ⟨1059062882207622025, 1059065489485120959⟩, true⟩

def words01 : List Nat := [371282932061756374, 371282939237401678, 371282946393887763, 371282946394080491, 371282924951263117, 371282906875443418, 371282888804825957, 371282883721116286, 371282861094624748, 371282838321971509]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 6810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 6800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488627924618907, 362488628490817586⟩, ⟨(-40032567304626111), (-40029948260292361)⟩, true⟩

def words02 : List Nat := [371282815555911114, 371282807924972566, 371282792960359559, 371282796198392052, 371282796198544803, 371282796135345026, 371282767578912915, 371282760444880044, 371282767590433253, 371282768448618744]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 6820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 6800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362503773268631881, 362503773836596921⟩, ⟨(-143265467405502417), (-143262836288142913)⟩, true⟩

def words03 : List Nat := [371282768448765804, 371282764229600121, 371282777187044117, 371282786312384378, 371282801633857624, 371282816950920721, 371282831388706389, 371282831388900742, 371282828977247642, 371282832039156760]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 6830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 6800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362509255546249495, 362509256115938359⟩, ⟨(-180300584755488986), (-180297941838159996)⟩, true⟩

def words04 : List Nat := [371282856443454973, 371282862116390959, 371282867641374682, 371282873164807554, 371282882650639093, 371282884627413098, 371282901503471699, 371282918374683020, 371282935248316018, 371282939090418266]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 6840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 6800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362584656125441710, 362584656696882746⟩, ⟨(-697609654242875987), (-697606999314175135)⟩, true⟩

def words05 : List Nat := [371282950536807877, 371282961979953205, 371282975090356567, 371282975090550836, 371282966013848593, 371282953848452591, 371282950786542607, 371282950786758132, 371282964714256115, 371282979536218969]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 6850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 6800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362506153364050103, 362506153937241464⟩, ⟨(-159008643744487687), (-159005976799652203)⟩, true⟩

def words06 : List Nat := [371282994197583070, 371282994197777300, 371283000172943966, 371283013771302944, 371283033514223141, 371283033514417379, 371283025072929195, 371283012636915126, 371283008962231495, 371283012330954221]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 6860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 6800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362449557584108512, 362449558159052100⟩, ⟨230843762843830372, 230846441835470456⟩, true⟩

def words07 : List Nat := [371283036876653176, 371283061415289551, 371283084689364441, 371283090715998111, 371283097711163456, 371283104704388432, 371283121029209852, 371283121029404852, 371283116298362545, 371283111420946791]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 6870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 6800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362608601391885205, 362608601968574391⟩, ⟨(-864159407601108925), (-864156716590849343)⟩, true⟩

def words08 : List Nat := [371283110073738936, 371283110073953390, 371283120485118056, 371283136241739330, 371283146498419795, 371283146498615952, 371283145768983966, 371283153222526013, 371283180093685096, 371283198294711259]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 6880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 6800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362589232365744785, 362589232944206782⟩, ⟨(-730392849697355420), (-730390146463312292)⟩, true⟩

def words09 : List Nat := [371283216376387104, 371283234452880278, 371283269703635838, 371283294571302894, 371283320965430424, 371283347351978391, 371283369616430023, 371283369616625251, 371283379299552687, 371283394638676669]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 6890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 6800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 6800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk068
