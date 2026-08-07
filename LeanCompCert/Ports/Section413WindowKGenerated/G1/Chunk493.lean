import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk493

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362471319583154887, 362471354662743921⟩, ⟨670732553310630528, 671900961368607180⟩, true⟩

def state01 : KState := ⟨⟨362484964942217428, 362485000036535460⟩, ⟨(-2009169572074794), (-840035299236920)⟩, true⟩

def words00 : List Nat := [371284983210183463, 371284983108875278, 371284982982525430, 371284983094205194, 371284983166860134, 371284983168503989, 371284982750304809, 371284982743177843, 371284982999033851, 371284983001080912]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 49300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 49300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362473233530045452, 362473268639354198⟩, ⟨576551931562178139, 577721805102908837⟩, true⟩

def words01 : List Nat := [371284983002321637, 371284983002231008, 371284983211524456, 371284983217385339, 371284983232903069, 371284983249013923, 371284983250246671, 371284983207928816, 371284982617801427, 371284982382361151]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 49310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 49300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362465995292221154, 362466030416201727⟩, ⟨933640282485715286, 934810879716736422⟩, true⟩

def words02 : List Nat := [371284982145978843, 371284982123920136, 371284981867691920, 371284981570046852, 371284981271785301, 371284981093976103, 371284980709636234, 371284980697619056, 371284980685062015, 371284980565800688]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 49320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 49300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362507645675904181, 362507680814729732⟩, ⟨(-1121168285712355131), (-1119996956101412451)⟩, true⟩

def words03 : List Nat := [371284980208456087, 371284980236086385, 371284980672675231, 371284980688644194, 371284980689933882, 371284980581076454, 371284980726022933, 371284980778215612, 371284981239405740, 371284981701292603]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 49330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 49300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485536286860627, 362485571440553444⟩, ⟨(-30286432848685087), (-29114369612726497)⟩, true⟩

def words04 : List Nat := [371284982163802046, 371284982165447169, 371284982090341069, 371284982101593770, 371284982203998506, 371284982205654802, 371284981940368786, 371284981673548105, 371284981481810910, 371284981495676690]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 49340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 49300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362464679232009242, 362464714400518897⟩, ⟨999179439156860283, 1000352233680080595⟩, true⟩

def words05 : List Nat := [371284981771482161, 371284982047957642, 371284982325120887, 371284982326766224, 371284982057363575, 371284981916382769, 371284981774581517, 371284981675257478, 371284981264543272, 371284980855820358]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 49350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 49300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488250829807899, 362488286013047739⟩, ⟨(-164391477639726684), (-163217955960759140)⟩, true⟩

def words06 : List Nat := [371284980446366298, 371284980310230703, 371284980132564674, 371284980249591562, 371284980308435398, 371284980310081264, 371284979822547122, 371284979745085528, 371284979996436972, 371284980065103384]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 49360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 49300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362490361249117873, 362490396447354023⟩, ⟨(-268565908750239552), (-267391646625995028)⟩, true⟩

def words07 : List Nat := [371284980066355587, 371284980051771765, 371284980365150325, 371284980544420612, 371284980839094139, 371284981134406535, 371284981415792721, 371284981417467424, 371284981466666543, 371284981578343149]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 49370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 49300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362459157572137544, 362459192785023552⟩, ⟨1272422065456698802, 1273597051068005914⟩, true⟩

def words08 : List Nat := [371284981885675246, 371284981887321575, 371284981648875210, 371284981388378559, 371284981127272045, 371284980835622944, 371284980337951812, 371284980012681557, 371284979686884517, 371284979321793506]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 49380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 49300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483194225788827, 362483229453599801⟩, ⟨85187097462083422, 86362820287628256⟩, true⟩

def words09 : List Nat := [371284978800821369, 371284978689647020, 371284978873171185, 371284978874817984, 371284978626046293, 371284978278407489, 371284977930128712, 371284977929183453, 371284977722338921, 371284977688828296]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 49390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 49300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 49300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk493
