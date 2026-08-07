import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk526

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360562853874824081, 360562871303653543⟩, ⟨1007530056144312408, 1008149486252304946⟩, true⟩

def state01 : KState := ⟨⟨360604755751440069, 360604773187142782⟩, ⟨(-1196730782502968536), (-1196110990827477684)⟩, true⟩

def words00 : List Nat := [360582037279914331, 360582037163939173, 360582037456438162, 360582037749065370, 360582037749755434, 360582037698031513, 360582037458327012, 360582037437705808, 360582037756036163, 360582038188932760]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 52600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 52600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360566408951515109, 360566426394168872⟩, ⟨820926797938835683, 821546955343772245⟩, true⟩

def words01 : List Nat := [360582038357731498, 360582038526611506, 360582038749636441, 360582039219412131, 360582039473993873, 360582039728683249, 360582039802666946, 360582039803396069, 360582039517025540, 360582039221142338]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 52610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 52600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360582754545027858, 360582771994548914⟩, ⟨(-39319642747325364), (-38699123951916912)⟩, true⟩

def words02 : List Nat := [360582038925028593, 360582038893260418, 360582038595201730, 360582038112827879, 360582037630344796, 360582037044921805, 360582036792371859, 360582036846689070, 360582036847338887, 360582036703105622]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 52620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 52600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360594016166811595, 360594033623226473⟩, ⟨(-632146651652714309), (-631525770001774989)⟩, true⟩

def words03 : List Nat := [360582037077942415, 360582037452988716, 360582037735229462, 360582037735958773, 360582037658161749, 360582037221788770, 360582036785295574, 360582036456130328, 360582036552359476, 360582036781031193]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 52630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 52600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360568760000243416, 360568777463611735⟩, ⟨697361088916437516, 697982336629013542⟩, true⟩

def words04 : List Nat := [360582036828835303, 360582036829564670, 360582036517258506, 360582036457303306, 360582036397156852, 360582036246857653, 360582036042120944, 360582035544937771, 360582035047636712, 360582034488049134]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 52640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 52600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360544560860008305, 360544578330238139⟩, ⟨1971666216267613359, 1972287825274984973⟩, true⟩

def words05 : List Nat := [360582034236848795, 360582034187920692, 360582034138914887, 360582033909646375, 360582033689864634, 360582033380124947, 360582033070187119, 360582032814701420, 360582032284652509, 360582031574166643]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 52650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 52600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580365242242242, 360580382719374162⟩, ⟨85941787902897719, 86563760406847655⟩, true⟩

def words06 : List Nat := [360582030863552807, 360582030143531546, 360582029650181241, 360582029264221430, 360582028878218810, 360582028183614772, 360582027370837217, 360582026918059141, 360582026465056044, 360582026231058363]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 52660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 52600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360557034513039440, 360557051997115091⟩, ⟨1314953904479042653, 1315576242744402673⟩, true⟩

def words07 : List Nat := [360582026200505288, 360582025952386214, 360582025814961236, 360582026108240935, 360582026123720415, 360582026139310130, 360582026139967024, 360582025971706237, 360582025443818697, 360582024970591637]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 52670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 52600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360561579595160142, 360561597086122290⟩, ⟨1075538478078210642, 1076161179158319646⟩, true⟩

def words08 : List Nat := [360582024497140480, 360582024307872639, 360582024233703400, 360582023909623836, 360582023585437784, 360582023083647174, 360582022760537067, 360582022430177871, 360582022099765567, 360582021477451923]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 52680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 52600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360587462492508975, 360587479990356003⟩, ⟨(-288431403600235360), (-287808339721227134)⟩, true⟩

def words09 : List Nat := [360582021090416563, 360582021063031390, 360582021035434631, 360582020988421250, 360582020582008557, 360582019868248060, 360582019154362219, 360582018800083322, 360582018730778390, 360582018835164997]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 52690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 52600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 52600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk526
