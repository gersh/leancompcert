import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk175

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482550913786698, 362482554965972694⟩, ⟨54848641423039890, 54896606948904818⟩, true⟩

def state01 : KState := ⟨⟨362464361275031237, 362464365332018688⟩, ⟨373271596752855070, 373319646329199988⟩, true⟩

def words00 : List Nat := [371285692389217976, 371285692389809176, 371285692744261451, 371285694073414122, 371285694883774693, 371285694884311963, 371285691350871104, 371285688379763559, 371285685699612435, 371285685700169985]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 17500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 17500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362508208017678537, 362508212079569041⟩, ⟨(-394679091302431991), (-394630955849129571)⟩, true⟩

def words01 : List Nat := [371285684483032492, 371285683268575992, 371285683678410668, 371285684120034838, 371285685472555830, 371285686825122670, 371285688167388554, 371285688167927413, 371285687480960822, 371285688767209637]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 17510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 17500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362434968480723157, 362434972547408699⟩, ⟨888811426595853487, 888859646083407689⟩, true⟩

def words02 : List Nat := [371285691388980622, 371285691389518447, 371285689674866640, 371285687107480827, 371285684540185689, 371285682967461303, 371285680101876050, 371285679271944710, 371285678441912569, 371285677604230343]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 17520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 17500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362521299521423291, 362521303592966340⟩, ⟨(-624968891822972230), (-624920587158546740)⟩, true⟩

def words03 : List Nat := [371285674712287847, 371285674481433569, 371285676858139625, 371285676858681420, 371285676581076093, 371285675420821965, 371285674466868083, 371285674467461079, 371285675280670672, 371285677312414573]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 17530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 17500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362460084012298059, 362460088088710920⟩, ⟨449076119548525601, 449124509653472025⟩, true⟩

def words04 : List Nat := [371285679325635621, 371285679326183587, 371285680836220684, 371285682922570319, 371285684877155535, 371285684877694588, 371285683273316331, 371285681663004738, 371285680052670139, 371285679228862115]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 17540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 17500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362438891121614745, 362438895202882217⟩, ⟨821416152233021754, 821464627561112416⟩, true⟩

def words05 : List Nat := [371285679558795618, 371285681346851811, 371285683128829270, 371285683129368246, 371285681209095891, 371285680249657197, 371285680959360703, 371285680959899868, 371285678312219716, 371285675648643101]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 17550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 17500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362437797902797980, 362437801988898420⟩, ⟨840615191195046379, 840663751414964249⟩, true⟩

def words06 : List Nat := [371285672985127602, 371285672356524321, 371285670108616442, 371285668676151783, 371285667243687663, 371285665313471457, 371285659069897596, 371285654477278007, 371285649884889999, 371285648531380775]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 17560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 17500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362494952059396487, 362494956150404397⟩, ⟨(-163891310723401046), (-163842664254362208)⟩, true⟩

def words07 : List Nat := [371285645808743927, 371285643080376792, 371285640860373275, 371285640860967809, 371285640075772627, 371285639699753243, 371285639323599067, 371285638490710118, 371285636316736848, 371285636847506134]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 17570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 17500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362469952795719645, 362469956891536357⟩, ⟨275919000249450243, 275967731282491645⟩, true⟩

def words08 : List Nat := [371285640611922717, 371285640612462926, 371285640585914245, 371285640554314810, 371285641450548793, 371285641451148663, 371285642711723231, 371285644637347831, 371285645789856403, 371285645790415408]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 17580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 17500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362558255293804976, 362558259394517477⟩, ⟨(-1277913859258345745), (-1277865042084148371)⟩, true⟩

def words09 : List Nat := [371285645272627678, 371285645646944580, 371285648816305003, 371285648816846557, 371285648702344705, 371285647525977899, 371285648400487115, 371285649299657514, 371285653425598337, 371285657551321969]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 17590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 17500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 17500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk175
