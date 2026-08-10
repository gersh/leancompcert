import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk796A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk796B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk796A

def state06 : KState := ⟨⟨362475118082951358, 362475213206881828⟩, ⟨790699083485959478, 795815944092225110⟩, true⟩

def words05 : List Nat := [371285203470950810, 371285203615089191, 371285203727824959, 371285203730577488, 371285203633160583, 371285203571088114, 371285203599676985, 371285203602429601, 371285203486643542, 371285203364352231]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 79650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 79600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479378563874893, 362479473712449365⟩, ⟨451317748946832402, 456436572818842214⟩, true⟩

def words06 : List Nat := [371285203240811660, 371285203241302222, 371285203220434790, 371285203246390218, 371285203252274441, 371285203255028164, 371285203072174020, 371285202930284804, 371285202799251791, 371285202802104428]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 79660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 79600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473595885076744, 362473691058764714⟩, ⟨912087288415471074, 917208113203598450⟩, true⟩

def words07 : List Nat := [371285202732253243, 371285202663253632, 371285202602029271, 371285202605117340, 371285202562357358, 371285202566424945, 371285202568514462, 371285202562519643, 371285202345778483, 371285202204763756]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 79670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 79600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362467123007675737, 362467218205919213⟩, ⟨1427858253676133019, 1432981035175667865⟩, true⟩

def words08 : List Nat := [371285202062198525, 371285201985656914, 371285201698576505, 371285201412337831, 371285201125056159, 371285200887235682, 371285200586603309, 371285200444548309, 371285200301489812, 371285200148887913]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 79680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 79600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489660934525784, 362489756157612863⟩, ⟨(-368303114767327732), (-363178353356472012)⟩, true⟩

def words09 : List Nat := [371285199925109791, 371285199860099329, 371285199882769935, 371285199885523993, 371285199767021329, 371285199585342528, 371285199402502566, 371285199378178520, 371285199337058185, 371285199397304254]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 79690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 79600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 79600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk796B
