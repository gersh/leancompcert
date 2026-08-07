import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk874

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362466549208289991, 362466664535645547⟩, ⟨1611853404012528312, 1618659162434239188⟩, true⟩

def state01 : KState := ⟨⟨362482993407586620, 362483108762204467⟩, ⟨174598499939162917, 181406641226898127⟩, true⟩

def words00 : List Nat := [371285184453527086, 371285184359309127, 371285184215759917, 371285184204193559, 371285184191707425, 371285184158891217, 371285184041316475, 371285184050595800, 371285184112460545, 371285184115610564]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 87400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 87400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362481712190736988, 362481827573035868⟩, ⟨286628547360417686, 293439108386699216⟩, true⟩

def words01 : List Nat := [371285184094142310, 371285184073712196, 371285184138217230, 371285184173748668, 371285184248135455, 371285184323772874, 371285184372900072, 371285184375943275, 371285184266448403, 371285184231791150]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 87410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 87400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478210031873706, 362478325441324120⟩, ⟨592805653995526601, 599618588749705593⟩, true⟩

def words02 : List Nat := [371285184287777814, 371285184290821134, 371285184211117239, 371285184104881822, 371285183997451504, 371285183914623604, 371285183765863928, 371285183749038023, 371285183731189699, 371285183711811936]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 87420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 87400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362484351678861940, 362484467115834336⟩, ⟨55811877178411483, 62627218320247939⟩, true⟩

def words03 : List Nat := [371285183635440544, 371285183616574597, 371285183704253276, 371285183707297012, 371285183643527158, 371285183552903259, 371285183461105825, 371285183424799048, 371285183351331771, 371285183346601951]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 87430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 87400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480188228992573, 362480303693423569⟩, ⟨419838956107429247, 426656698367179763⟩, true⟩

def words04 : List Nat := [371285183340686114, 371285183335568186, 371285183155210123, 371285183107147314, 371285183057515256, 371285183048879582, 371285182898144159, 371285182746397775, 371285182593379167, 371285182557898895]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 87440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 87400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362470837428496061, 362470952920320415⟩, ⟨1237617737996066343, 1244437875947801771⟩, true⟩

def words05 : List Nat := [371285182504221419, 371285182481677922, 371285182458158889, 371285182426116431, 371285182237783599, 371285182091098499, 371285181942797467, 371285181891747476, 371285181731297914, 371285181572000587]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 87450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 87400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474197798451261, 362474313317504978⟩, ⟨943728259339870871, 950550778908143391⟩, true⟩

def words06 : List Nat := [371285181411393526, 371285181319457401, 371285181172125571, 371285181138889330, 371285181104707896, 371285181024946927, 371285180782175398, 371285180651115012, 371285180518512366, 371285180480862794]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 87460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 87400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474104854578955, 362474220401475745⟩, ⟨951897573922766326, 958722529057661604⟩, true⟩

def words07 : List Nat := [371285180358922666, 371285180238472800, 371285180123341431, 371285180126697834, 371285180074515500, 371285180062189760, 371285180048866953, 371285180034166901, 371285179856808856, 371285179735369866]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 87470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 87400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478460143800644, 362478575717820958⟩, ⟨570896365883896486, 577723693926706822⟩, true⟩

def words08 : List Nat := [371285179617411304, 371285179620467670, 371285179524134753, 371285179403542770, 371285179281814112, 371285179201429836, 371285179071870234, 371285179057858563, 371285179042795943, 371285179028987111]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 87480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 87400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493619660354646, 362493735261906880⟩, ⟨(-755476000966651809), (-748646264016662813)⟩, true⟩

def words09 : List Nat := [371285179010595927, 371285179069229759, 371285179155514730, 371285179158582987, 371285179148632321, 371285179126175307, 371285179182871070, 371285179201292056, 371285179301146730, 371285179402385085]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 87490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 87400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 87400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk874
