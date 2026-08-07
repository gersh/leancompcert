import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk062

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362516776624075847, 362516777086313931⟩, ⟨(-239818214921683894), (-239816273771861460)⟩, true⟩

def state01 : KState := ⟨⟨362416164687891386, 362416165151699381⟩, ⟨384466957152956584, 384468908044191422⟩, true⟩

def words00 : List Nat := [371278108660115199, 371278108660291661, 371278102734107936, 371278112711171352, 371278124696171364, 371278124696345312, 371278110106640019, 371278095352008457, 371278080602059001, 371278076409033390]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 6200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 6200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362381939012346786, 362381939477718196⟩, ⟨597978019777298821, 597979980385460529⟩, true⟩

def words01 : List Nat := [371278082297671134, 371278098149274799, 371278113526873002, 371278113527047790, 371278104732115173, 371278097529754161, 371278108928815907, 371278108928990008, 371278093196834033, 371278077738230328]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 6210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 6200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362578164066805652, 362578164533738637⟩, ⟨(-623342090433360639), (-623340120104185555)⟩, true⟩

def words02 : List Nat := [371278072602412210, 371278072849146280, 371278082549393450, 371278092246594691, 371278098372675479, 371278098372850945, 371278082879109198, 371278083558317569, 371278109939637965, 371278125997371411]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 6220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 6200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362453338086115088, 362453338554639719⟩, ⟨155419914581799554, 155421894834813930⟩, true⟩

def words03 : List Nat := [371278140862282389, 371278155722484200, 371278188176215598, 371278207929515332, 371278231322698181, 371278254708444482, 371278269364636302, 371278269364811081, 371278249901565258, 371278245909581196]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 6230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 6200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362410182692349959, 362410183162430541⟩, ⟨425145768908134234, 425147758878476416⟩, true⟩

def words04 : List Nat := [371278261360583515, 371278261360758349, 371278246730606377, 371278231891933284, 371278217057944260, 371278209914538429, 371278195679185717, 371278201330890573, 371278206803669951, 371278206803851098]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 6240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 6200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362501551970090517, 362501552441753231⟩, ⟨(-146698733097447600), (-146696733230710142)⟩, true⟩

def words05 : List Nat := [371278195921930842, 371278190677108872, 371278192752737233, 371278192752912402, 371278171974434847, 371278147229792074, 371278123232113413, 371278123232309289, 371278118458614124, 371278122201658884]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 6250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 6200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487536205362623, 362487536678606933⟩, ⟨(-59502536881024496), (-59500527105471104)⟩, true⟩

def words06 : List Nat := [371278125811414299, 371278125811589838, 371278103329782275, 371278104800203401, 371278107229094879, 371278107229271217, 371278085901230713, 371278064454472919, 371278046961163724, 371278048474635402]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 6260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 6200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362407688582402340, 362407689057232750⟩, ⟨442209441804255842, 442211461532775828⟩, true⟩

def words07 : List Nat := [371278075362349807, 371278102241568423, 371278123954837566, 371278123955013496, 371278111932358329, 371278107072119366, 371278122685014758, 371278122685190880, 371278116109356251, 371278104895056441]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 6270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 6200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362572776178746731, 362572776655153630⟩, ⟨(-595337426601465826), (-595335396964413006)⟩, true⟩

def words08 : List Nat := [371278094675245981, 371278094675441470, 371278091207051173, 371278099217148351, 371278102978058938, 371278102978238184, 371278094434867554, 371278102789133894, 371278128738124129, 371278143783278823]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 6280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 6200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362560775831358341, 362560776309374928⟩, ⟨(-519954553283548866), (-519952513513426962)⟩, true⟩

def words09 : List Nat := [371278158253555827, 371278172719292511, 371278192352641804, 371278199464222961, 371278214055906918, 371278228643025095, 371278243117640828, 371278243117817615, 371278244164151056, 371278257262634185]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 6290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 6200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 6200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk062
