import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk566

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362494269480174712, 362494316233802406⟩, ⟨(-534352194814414753), (-532564590621126199)⟩, true⟩

def state01 : KState := ⟨⟨362491164206566040, 362491210977446081⟩, ⟨(-358587724955459346), (-356799144194303784)⟩, true⟩

def words00 : List Nat := [371284907285014905, 371284907286964230, 371284907431090139, 371284907606009270, 371284907874774451, 371284907928908985, 371284907981919073, 371284908035599794, 371284908216999602, 371284908330536571]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 56600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 56600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362472867813956383, 362472914601980341⟩, ⟨677362389692870115, 679151941059183245⟩, true⟩

def words01 : List Nat := [371284908755153470, 371284909180513531, 371284909601751505, 371284909607704257, 371284909660067093, 371284909713420520, 371284909925595296, 371284909927502734, 371284909724121834, 371284909514397494]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 56610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 56600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483341404855456, 362483388209985646⟩, ⟨84300003348318613, 86090523355542167⟩, true⟩

def words02 : List Nat := [371284909326460424, 371284909328562330, 371284909196954866, 371284909194655781, 371284909191740148, 371284909131362007, 371284908733916300, 371284908531849322, 371284908436183526, 371284908438192525]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 56620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 56600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362474326079383708, 362474372901891313⟩, ⟨594961671297890294, 596753175475996932⟩, true⟩

def words03 : List Nat := [371284908412774927, 371284908379355758, 371284908621381588, 371284908744261493, 371284908937831879, 371284909132108040, 371284909263870604, 371284909265778717, 371284908981977219, 371284908798350989]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 56630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 56600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362466565731827335, 362466612571333390⟩, ⟨1034547575647034451, 1036340042703539607⟩, true⟩

def words04 : List Nat := [371284908634312960, 371284908636221291, 371284908280229929, 371284907919746429, 371284907558520717, 371284907292770220, 371284906871664818, 371284906692232257, 371284906512147126, 371284906305538219]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 56640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 56600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362498441086158840, 362498487942903963⟩, ⟨(-771393505280930463), (-769600061542025595)⟩, true⟩

def words05 : List Nat := [371284905983935681, 371284905791776057, 371284905691923654, 371284905693841273, 371284905490652887, 371284905236764347, 371284904993808636, 371284904995953212, 371284905165248041, 371284905407093758]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 56650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 56600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481332343902016, 362481379217853407⟩, ⟨198004417951809015, 199798836687168459⟩, true⟩

def words06 : List Nat := [371284905536743136, 371284905538653032, 371284905388374050, 371284905470621194, 371284905569666125, 371284905571577005, 371284905334796774, 371284905093981151, 371284904870108362, 371284904872285862]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 56660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 56600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474179039194620, 362474225930390827⟩, ⟨603510486759985453, 605305882844706715⟩, true⟩

def words07 : List Nat := [371284905060510399, 371284905311795656, 371284905561030885, 371284905562941163, 371284905449801871, 371284905430015548, 371284905597639502, 371284905599554349, 371284905472367931, 371284905286122033]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 56670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 56600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362499308729459659, 362499355637736929⟩, ⟨(-820928236625004157), (-819131872296955473)⟩, true⟩

def words08 : List Nat := [371284905221875790, 371284905226414333, 371284905389656135, 371284905553643638, 371284905668565864, 371284905670508987, 371284905693985252, 371284905862994148, 371284906317144796, 371284906574000235]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 56680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 56600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482462422840736, 362482509348548593⟩, ⟨134194955369983280, 135992307922394522⟩, true⟩

def words09 : List Nat := [371284906831031460, 371284907088667313, 371284907406463983, 371284907614818336, 371284907774954034, 371284907935829752, 371284908095206056, 371284908097116393, 371284907841840769, 371284907801951105]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 56690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 56600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 56600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk566
