import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk842A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362498252086500000, 362498358815794479⟩, ⟨(-1104604868668206467), (-1098536916606857117)⟩, true⟩

def state01 : KState := ⟨⟨362478841020551806, 362478947776251084⟩, ⟨529839938245400713, 535910113726652235⟩, true⟩

def words00 : List Nat := [371285312358735580, 371285312361657862, 371285312318235928, 371285312312466574, 371285312305265024, 371285312304490909, 371285312133263662, 371285311963077900, 371285311791661184, 371285311748626416]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 84200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 84200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362475374164923114, 362475480946891809⟩, ⟨821870954919185965, 827943342680721763⟩, true⟩

def words01 : List Nat := [371285311740399768, 371285311808908416, 371285311875853982, 371285311878792481, 371285311837045450, 371285311839947661, 371285311881001220, 371285311883932334, 371285311781601335, 371285311668130004]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 84210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 84200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485165039209914, 362485271847346473⟩, ⟨(-2715374149883998), 3359217601223554⟩, true⟩

def words02 : List Nat := [371285311577570038, 371285311580821651, 371285311631485857, 371285311729547845, 371285311806481340, 371285311809408868, 371285311733917864, 371285311685901571, 371285311725806342, 371285311728832894]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 84220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 84200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362493983951057238, 362494090785930704⟩, ⟨(-745598227241168408), (-739521383313053612)⟩, true⟩

def words03 : List Nat := [371285311730604386, 371285311707890585, 371285311786327865, 371285311823957303, 371285311871986255, 371285311921102237, 371285311965798306, 371285311968793411, 371285312038345150, 371285312146274088]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 84230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 84200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485958743229067, 362486065604102951⟩, ⟨(-69486876358642412), (-63407842018710602)⟩, true⟩

def words04 : List Nat := [371285312371363344, 371285312429669481, 371285312487228662, 371285312545747807, 371285312599702304, 371285312602931741, 371285312742880262, 371285312885471365, 371285312985736300, 371285312997700432]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 84240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 84200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk842A
