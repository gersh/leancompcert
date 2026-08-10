import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk769A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk769B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk769A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk769B
