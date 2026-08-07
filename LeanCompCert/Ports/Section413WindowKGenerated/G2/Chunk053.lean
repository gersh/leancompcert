import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk053

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360857255531556453, 360857255674685395⟩, ⟨(-1474782057345102253), (-1474781542382167693)⟩, true⟩

def state01 : KState := ⟨⟨361098845028826494, 361098845172529570⟩, ⟨(-2757922264547607380), (-2757921746538947206)⟩, true⟩

def words00 : List Nat := [360579077828575713, 360579104739199172, 360579166769281650, 360579228775996308, 360579281484206162, 360579336273491728, 360579366688433694, 360579397091924249, 360579462545993711, 360579560339816532]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 5300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 5300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360568350870163642, 360568351014436601⟩, ⟨62382432949267091, 62382953986869429⟩, true⟩

def words01 : List Nat := [360579678678844649, 360579796973337123, 360579881781157268, 360579931958534731, 360579972941429781, 360580013908924705, 360580063919441077, 360580079338061100, 360580079338115594, 360580077133607066]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 5310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 5300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360822709440283004, 360822709585127167⟩, ⟨(-1292243083838288713), (-1292242559759007827)⟩, true⟩

def words02 : List Nat := [360580082884134470, 360580108587386903, 360580169115742836, 360580229621376851, 360580259167294582, 360580259167355079, 360580254226193227, 360580247892694391, 360580262575728679, 360580308054502705]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 5320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 5300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360852320592989292, 360852320738410566⟩, ⟨(-1450036040523005724), (-1450035513364855248)⟩, true⟩

def words03 : List Nat := [360580335999415510, 360580363933854910, 360580426553869252, 360580517052933757, 360580581120919394, 360580645164905627, 360580690569432247, 360580727647195713, 360580778507374499, 360580829348527613]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 5330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 5300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360769223895171021, 360769224041165216⟩, ⟨(-1007185345105856215), (-1007184814885438359)⟩, true⟩

def words04 : List Nat := [360580876782630126, 360580889890580325, 360580889890634731, 360580879667073871, 360580869447328745, 360580857447323030, 360580899191237325, 360580940919555919, 360580965197198529, 360581000379254277]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 5340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 5300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360894841150371392, 360894841296939879⟩, ⟨(-1679827087316397108), (-1679826554020707004)⟩, true⟩

def words05 : List Nat := [360581070023234858, 360581139641212301, 360581227507620139, 360581281160324159, 360581298513174660, 360581315859550031, 360581337707662396, 360581382339182240, 360581440820380566, 360581499279775040]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 5350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 5300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360577801493094132, 360577801640243995⟩, ⟨20922703270985744, 20923239685775520⟩, true⟩

def words06 : List Nat := [360581540396953430, 360581583618428527, 360581644901199441, 360581706161142988, 360581745832722446, 360581751439919735, 360581751439974197, 360581739803890907, 360581728172131407, 360581697960483432]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 5360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 5300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360059221806484079, 360059221954209535⟩, ⟨2809276255453166520, 2809276794961870286⟩, true⟩

def words07 : List Nat := [360581713018478710, 360581728796047169, 360581728796102226, 360581727501391834, 360581692217027159, 360581643042641685, 360581593886528387, 360581558638299874, 360581489437872279, 360581392362195013]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 5370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 5300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360434285260511895, 360434285408816484⟩, ⟨789439441234306202, 789439983861584440⟩, true⟩

def words08 : List Nat := [360581295322585170, 360581232359949690, 360581194748312128, 360581155755193442, 360581116776552182, 360581047906771678, 360580945172449861, 360580876450985748, 360580807755008602, 360580749227714738]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 5380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 5300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360383834317623643, 360383834466512664⟩, ⟨1061824783593525841, 1061825329373799165⟩, true⟩

def words09 : List Nat := [360580722059560165, 360580676755675168, 360580631468579706, 360580630952815665, 360580630952867380, 360580621495428836, 360580612041489244, 360580575509050758, 360580505207204166, 360580468786767072]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 5390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 5300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 5300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk053
