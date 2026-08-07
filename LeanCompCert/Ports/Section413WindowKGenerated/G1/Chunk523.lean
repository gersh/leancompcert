import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk523

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362474034392186965, 362474074059427643⟩, ⟨572819202281495769, 574220736585171037⟩, true⟩

def state01 : KState := ⟨⟨362485308930776417, 362485348613694079⟩, ⟨(-16796332239013674), (-15393977947667942)⟩, true⟩

def words00 : List Nat := [371285053370039033, 371285053374754977, 371285053717266628, 371285054060532877, 371285054297056090, 371285054298807961, 371285054067097745, 371285054088050871, 371285054328226556, 371285054335665602]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 52300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 52300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362500984449687102, 362501024148606508⟩, ⟨(-836879196153010042), (-835476004731771960)⟩, true⟩

def words01 : List Nat := [371285054336999409, 371285054270332164, 371285054499417667, 371285054615291432, 371285054842793298, 371285055070955746, 371285055297393399, 371285055299177212, 371285055568338560, 371285055875738410]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 52310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 52300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362480156400935312, 362480196115456079⟩, ⟨252999069429734197, 254403077193391545⟩, true⟩

def words02 : List Nat := [371285056547069676, 371285056732340489, 371285056895151206, 371285057058530654, 371285057188197482, 371285057203831997, 371285057345056253, 371285057486995635, 371285057628589255, 371285057630403402]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 52320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 52300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362506559018046037, 362506598748414014⟩, ⟨(-1128765785041627443), (-1127360947913655035)⟩, true⟩

def words03 : List Nat := [371285057746142277, 371285057955696777, 371285058461224584, 371285058523299950, 371285058529627794, 371285058536510297, 371285058885198933, 371285059148623286, 371285059561366058, 371285059974834724]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 52330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 52300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485266040215062, 362485305786392592⟩, ⟨(-14237268434106564), (-12831603751885052)⟩, true⟩

def words04 : List Nat := [371285060385702631, 371285060387455893, 371285060465978029, 371285060622097989, 371285060836242041, 371285060838025804, 371285060749962465, 371285060662788896, 371285060672571118, 371285060679255157]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 52340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 52300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362464754972904901, 362464794734913947⟩, ⟨1059674549815635077, 1061081043355954267⟩, true⟩

def words05 : List Nat := [371285060927866762, 371285061177200500, 371285061354595619, 371285061356349122, 371285061047672405, 371285060810659620, 371285060608393081, 371285060610147314, 371285060227696691, 371285059842693855]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 52350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 52300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479512682893269, 362479552460583486⟩, ⟨286966526044886051, 288373840732973557⟩, true⟩

def words06 : List Nat := [371285059456857329, 371285059436141543, 371285059392608146, 371285059554310497, 371285059654829629, 371285059656583562, 371285059271195477, 371285059036688440, 371285058928898419, 371285058930713961]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 52360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 52300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485009114627865, 362485048908293938⟩, ⟨(-896902528647928), 511248894260416⟩, true⟩

def words07 : List Nat := [371285058826905256, 371285058637263754, 371285058583909876, 371285058622980034, 371285058763905180, 371285058905509803, 371285059028050391, 371285059029804895, 371285058666689367, 371285058668677563]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 52370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 52300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482942150271046, 362482981959586928⟩, ⟨107368569341101520, 108777540582558652⟩, true⟩

def words08 : List Nat := [371285058821973773, 371285058823740173, 371285058651303126, 371285058464371673, 371285058276751958, 371285058201705492, 371285058048949104, 371285058155908206, 371285058261264705, 371285058263091081]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 52380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 52300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362517160764938668, 362517200590125443⟩, ⟨(-1685508662164953752), (-1684098859369333586)⟩, true⟩

def words09 : List Nat := [371285058549002492, 371285058875457494, 371285059383118637, 371285059617766129, 371285059764992839, 371285059912720000, 371285060374794772, 371285060682370952, 371285061296919281, 371285061912249652]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 52390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 52300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 52300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk523
