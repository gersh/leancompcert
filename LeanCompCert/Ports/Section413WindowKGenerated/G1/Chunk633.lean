import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk633

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485773238694892, 362485832237343093⟩, ⟨(-28643897700705577), (-26121381639023311)⟩, true⟩

def state01 : KState := ⟨⟨362466391174218632, 362466450192051844⟩, ⟨1198341044213497161, 1200864774784884645⟩, true⟩

def words00 : List Nat := [371285419695075694, 371285419697228029, 371285419528046884, 371285419358794626, 371285419188714269, 371285419031011801, 371285418747097332, 371285418568390456, 371285418388930874, 371285418203026175]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 63300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 63300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492333996755715, 362492393034030456⟩, ⟨(-444212363421948366), (-441687401907355574)⟩, true⟩

def words01 : List Nat := [371285417904884821, 371285417857367906, 371285418008056127, 371285418010207169, 371285417878872871, 371285417672783047, 371285417506856393, 371285417509227225, 371285417551463204, 371285417664059872]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 63310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 63300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362466794333836391, 362466853390544533⟩, ⟨1173093009774216850, 1175619201912982408⟩, true⟩

def words02 : List Nat := [371285417775015736, 371285417777204580, 371285417746548900, 371285417814748870, 371285417892133815, 371285417894285217, 371285417639522094, 371285417321479115, 371285417002566624, 371285416776016079]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 63320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 63300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362465669320787115, 362465728396845453⟩, ⟨1244397611786581972, 1246925029470074742⟩, true⟩

def words03 : List Nat := [371285416484358916, 371285416442872413, 371285416400696548, 371285416348557954, 371285415963606483, 371285415635324719, 371285415305859408, 371285415226378365, 371285414922961252, 371285414614551012]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 63330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 63300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473956106644462, 362474015202000474⟩, ⟨719517411575533661, 722046051669760293⟩, true⟩

def words04 : List Nat := [371285414305213627, 371285414207177475, 371285414020641386, 371285413938073828, 371285413854810280, 371285413710411547, 371285413308492445, 371285413156870293, 371285413004178250, 371285412929730068]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 63340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 63300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362474666446548733, 362474725561541331⟩, ⟨674559738368846084, 677089622534490888⟩, true⟩

def words05 : List Nat := [371285412751440300, 371285412575206073, 371285412468664948, 371285412471036588, 371285412441259321, 371285412465784164, 371285412467421919, 371285412441627853, 371285412116707504, 371285411950785878]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 63350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 63300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362473655290273395, 362473714424419904⟩, ⟨738674726193078935, 741205824050498055⟩, true⟩

def words06 : List Nat := [371285411864033842, 371285411866196733, 371285411711011009, 371285411555780266, 371285411399714102, 371285411242753911, 371285410970836510, 371285410948872852, 371285410926180396, 371285410902628055]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 63360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 63300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362490713394794345, 362490772548407865⟩, ⟨(-342438190013066474), (-339905858431572548)⟩, true⟩

def words07 : List Nat := [371285410719552826, 371285410564738194, 371285410475450245, 371285410477603444, 371285410214128563, 371285409928302631, 371285409641575261, 371285409604809606, 371285409563074315, 371285409650087682]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 63370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 63300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362486241592846323, 362486300765870253⟩, ⟨(-59031505939957374), (-56497944027936694)⟩, true⟩

def words08 : List Nat := [371285409708234882, 371285409710404004, 371285409693391680, 371285409799065515, 371285409916488556, 371285409918643057, 371285409748008211, 371285409579462612, 371285409488070331, 371285409504586665]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 63380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 63300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476325438446563, 362476384630912086⟩, ⟨569682855803712554, 572217650216037430⟩, true⟩

def words09 : List Nat := [371285409768983053, 371285410034318890, 371285410230691076, 371285410232846966, 371285410160207551, 371285410150694472, 371285410376813260, 371285410378967352, 371285410285817955, 371285410145899721]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 63390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 63300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 63300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk633
