import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk171

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362504704158602972, 362504708019718974⟩, ⟨(-329335001735383189), (-329290341905785393)⟩, true⟩

def state01 : KState := ⟨⟨362472014661573815, 362472018527360255⟩, ⟨229778642802198406, 229823382520649814⟩, true⟩

def words00 : List Nat := [371285454816153028, 371285454816678076, 371285453785379114, 371285452742798287, 371285451700135795, 371285450800099185, 371285449008799797, 371285449821599150, 371285450635673194, 371285450636215933]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 17100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 17100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362540486053556410, 362540489924084329⟩, ⟨(-941994925511797760), (-941950104643171718)⟩, true⟩

def words01 : List Nat := [371285451927925791, 371285454004666958, 371285459045953184, 371285460215731097, 371285460438887334, 371285460662172268, 371285464296663785, 371285466259094001, 371285469473451171, 371285472687670383]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 17110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 17100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484943586682661, 362484947461941212⟩, ⟨9219265097305838, 9264166979443692⟩, true⟩

def words02 : List Nat := [371285475890719557, 371285476265559287, 371285480050490051, 371285483835243119, 371285488477493446, 371285488582276463, 371285488582675075, 371285488007691130, 371285488276695680, 371285488277293194]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 17120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 17100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362499817406181080, 362499821286166229⟩, ⟨(-245520139093630247), (-245475156221463747)⟩, true⟩

def words03 : List Nat := [371285490842942247, 371285493440065025, 371285496025648450, 371285496026175780, 371285495382245931, 371285495024731196, 371285497713118083, 371285498678489481, 371285499514507301, 371285500350618626]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 17130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 17100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494005716294152, 362494009600981417⟩, ⟨(-145725268649495440), (-145680205158445856)⟩, true⟩

def words04 : List Nat := [371285504012725887, 371285505978664733, 371285509077861468, 371285512176907325, 371285514707545284, 371285514708070649, 371285512941036970, 371285513170750776, 371285515127823710, 371285515623653072]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 17140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 17100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362498713608045950, 362498717497525905⟩, ⟨(-226469417080722064), (-226424271371626960)⟩, true⟩

def words05 : List Nat := [371285516107715120, 371285516591904769, 371285519172235840, 371285520066838700, 371285521775962265, 371285523485081974, 371285524465500821, 371285524466027257, 371285522609255360, 371285523378804874]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 17150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 17100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485001146173693, 362485005040331635⟩, ⟨8975958959226595, 9021184967211857⟩, true⟩

def words06 : List Nat := [371285527302051707, 371285527302577479, 371285526708016874, 371285526115804019, 371285525930857381, 371285525931436193, 371285526753751182, 371285528860944771, 371285530443686149, 371285530444231881]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 17160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 17100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362523627731605614, 362523631630519391⟩, ⟨(-654617568808720701), (-654572261118902525)⟩, true⟩

def words07 : List Nat := [371285530592721073, 371285530772050753, 371285533174801317, 371285533175327942, 371285531874003417, 371285529885985893, 371285528836554772, 371285528837143962, 371285530799833675, 371285533018033570]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 17170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 17100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362513498749224467, 362513502652890598⟩, ⟨(-480685796808532579), (-480640407448919989)⟩, true⟩

def words08 : List Nat := [371285534987410138, 371285534987940217, 371285536745545559, 371285539317072967, 371285542063060566, 371285542063589614, 371285541593351028, 371285540663246378, 371285542186465198, 371285543813529949]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 17180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 17100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362451674049680793, 362451677958099924⟩, ⟨582707947495601041, 582753418583731527⟩, true⟩

def words09 : List Nat := [371285548823642595, 371285553833399933, 371285558184540329, 371285558185067117, 371285558685885505, 371285559338265877, 371285562388839164, 371285562389366094, 371285560940150261, 371285558970808281]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 17190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 17100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 17100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk171
