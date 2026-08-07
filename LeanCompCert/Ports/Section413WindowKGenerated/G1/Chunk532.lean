import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk532

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362478242825950348, 362478283926568177⟩, ⟨356129314863148856, 357606461926863622⟩, true⟩

def state01 : KState := ⟨⟨362485791582789804, 362485832699362155⟩, ⟨(-45410812827998561), (-43932816900532355)⟩, true⟩

def words00 : List Nat := [371285005953936166, 371285006005961955, 371285006374909973, 371285006744553609, 371285007055759817, 371285007057545241, 371285006963644815, 371285006914343708, 371285007047878257, 371285007065247019]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 53200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 53200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362499512706479416, 362499553839286272⟩, ⟨(-775571003946655340), (-774092144098410242)⟩, true⟩

def words01 : List Nat := [371285007082094110, 371285007099526684, 371285007425886430, 371285007627232915, 371285007887211673, 371285008147887241, 371285008414158159, 371285008426459130, 371285008700980215, 371285008976467114]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 53210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 53200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482181279358228, 362482222428084468⟩, ⟨146950623395356773, 148430330556826191⟩, true⟩

def words02 : List Nat := [371285009397797048, 371285009564157989, 371285009725682845, 371285009887819283, 371285010153985738, 371285010244116735, 371285010483363549, 371285010723339739, 371285010897597585, 371285010899445671]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 53220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 53200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362523770849773477, 362523812014646521⟩, ⟨(-2067068356716214300), (-2065587789979063064)⟩, true⟩

def words03 : List Nat := [371285011148369723, 371285011450615102, 371285012104366938, 371285012348306954, 371285012537625606, 371285012727432291, 371285013237332822, 371285013615674988, 371285014345631978, 371285015076385049]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 53230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 53200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362505541236926163, 362505582417933183⟩, ⟨(-1096437635891103650), (-1094956210101674486)⟩, true⟩

def words04 : List Nat := [371285015806407280, 371285016243567417, 371285016950239452, 371285017657818703, 371285018408646683, 371285018734515982, 371285019059948028, 371285019386004911, 371285019857957464, 371285020246141073]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 53240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 53200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362481168698444624, 362481209895500410⟩, ⟨201558507207392976, 203040787677570836⟩, true⟩

def words05 : List Nat := [371285020753438174, 371285021261417138, 371285021718799512, 371285021720585661, 371285021802934895, 371285021899820648, 371285022258507642, 371285022260295257, 371285022221712643, 371285022152122220]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 53250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 53200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362490978141736496, 362491019354805629⟩, ⟨(-320964058563488235), (-319480925140756843)⟩, true⟩

def words06 : List Nat := [371285022148639714, 371285022150639790, 371285022195432788, 371285022291861500, 371285022319973927, 371285022321760455, 371285021880297291, 371285021791766069, 371285021963678085, 371285022078142140]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 53260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 53200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489406665431165, 362489447894814304⟩, ⟨(-237249273344056588), (-235765270794729710)⟩, true⟩

def words07 : List Nat := [371285022188946332, 371285022300350874, 371285022510401772, 371285022590628902, 371285022774825190, 371285022959684573, 371285023051473144, 371285023053265164, 371285022868701670, 371285022954013743]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 53270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 53200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482893237626595, 362482934482915170⟩, ⟨109852943003295479, 111337793077995283⟩, true⟩

def words08 : List Nat := [371285023390134689, 371285023391921921, 371285023358991016, 371285023326794229, 371285023367961075, 371285023369930860, 371285023443285969, 371285023598690247, 371285023762225917, 371285023764076326]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 53280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 53200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362501874491464364, 362501915752926792⟩, ⟨(-901817582982578423), (-900331870922747191)⟩, true⟩

def words09 : List Nat := [371285023770137306, 371285023816284835, 371285024176034943, 371285024177822612, 371285024068821656, 371285023841289983, 371285023685464448, 371285023687489898, 371285023970981070, 371285024289897529]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 53290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 53200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 53200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk532
