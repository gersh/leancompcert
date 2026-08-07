import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk769

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360562980228817699, 360563018627483684⟩, ⟨1470688967874925676, 1472683349942498270⟩, true⟩

def state01 : KState := ⟨⟨360575994100670908, 360576032509703109⟩, ⟨469884325418021810, 471879504699109646⟩, true⟩

def words00 : List Nat := [360582169008084553, 360582168787098457, 360582168720093147, 360582168745225648, 360582168746246638, 360582168628744334, 360582168342370232, 360582168225099244, 360582168107514878, 360582167986295219]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 76900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 76900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360578320471521058, 360578358890992860⟩, ⟨290953615047168428, 292949597290349622⟩, true⟩

def words01 : List Nat := [360582167907499505, 360582167732902204, 360582167558088058, 360582167629517043, 360582167665283685, 360582167701248004, 360582167702225329, 360582167653703629, 360582167436359472, 360582167388097519]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 76910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 76900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360561752565000229, 360561790994816891⟩, ⟨1565326524987766207, 1567323303008003463⟩, true⟩

def words02 : List Nat := [360582167339477029, 360582167281171629, 360582167054177853, 360582166659579481, 360582166264816134, 360582165768447941, 360582165356453880, 360582165053842202, 360582164751118885, 360582164364152755]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 76920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 76900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360581022313531242, 360581060753700018⟩, ⟨82808939595955163, 84806514055739249⟩, true⟩

def words03 : List Nat := [360582164100215077, 360582163911331808, 360582163722120331, 360582163672120082, 360582163673133457, 360582163513666621, 360582163354009914, 360582163139385123, 360582163009079848, 360582162995889461]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 76930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 76900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360584852439798276, 360584890890430478⟩, ⟨(-211980636760448186), (-209982257196300486)⟩, true⟩

def words04 : List Nat := [360582162982550647, 360582162872687425, 360582162849948566, 360582162923663107, 360582162924587697, 360582162885620786, 360582162722259403, 360582162450709194, 360582162178955938, 360582162111633630]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 76940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 76900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360567399669988441, 360567438130970540⟩, ⟨1131077084108378753, 1133076260148418457⟩, true⟩

def words05 : List Nat := [360582162144129968, 360582162176820148, 360582162177798068, 360582162116303745, 360582161923288626, 360582161688343259, 360582161453073880, 360582161318584971, 360582161245515343, 360582161055348768]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 76950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 76900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595562900360505, 360595601371693942⟩, ⟨(-1036454460501630672), (-1034454487771003390)⟩, true⟩

def words06 : List Nat := [360582160864932431, 360582160922868200, 360582161171774063, 360582161420883825, 360582161510677523, 360582161511776163, 360582161534751170, 360582161560399113, 360582161660439324, 360582161836183542]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 76960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 76900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360582712678932362, 360582751160732787⟩, ⟨(-47309903294068704), (-45309124866122026)⟩, true⟩

def words07 : List Nat := [360582161927460851, 360582162018874553, 360582162100839134, 360582162267672214, 360582162390640558, 360582162513786634, 360582162553171501, 360582162567859439, 360582162576408798, 360582162585306824]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 76970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 76900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581094459424723, 360581132951565732⟩, ⟨77241085420572307, 79242659917021869⟩, true⟩

def words08 : List Nat := [360582162672377920, 360582162673475973, 360582162644184219, 360582162512012294, 360582162379664930, 360582162179837120, 360582162189916135, 360582162264413151, 360582162265398105, 360582162210689216]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 76980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 76900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360585877274931362, 360585915777452340⟩, ⟨(-291037075784716973), (-289034702084464375)⟩, true⟩

def words09 : List Nat := [360582162353232856, 360582162509463256, 360582162593496929, 360582162594595068, 360582162548294130, 360582162343502530, 360582162138506471, 360582162031137083, 360582162078856953, 360582162128771356]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 76990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 76900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 76900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk769
