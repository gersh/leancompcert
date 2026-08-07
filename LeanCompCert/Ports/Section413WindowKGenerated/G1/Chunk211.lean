import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk211

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362455115378497625, 362455121366869814⟩, ⟨616775178724554842, 616860629673377908⟩, true⟩

def state01 : KState := ⟨⟨362478090061490121, 362478096055736957⟩, ⟨132156413749355954, 132241988684063118⟩, true⟩

def words00 : List Nat := [371284355933478618, 371284355934202448, 371284357268915493, 371284358880658814, 371284359813663864, 371284359814321463, 371284358754501960, 371284359342692548, 371284360478963859, 371284360479644303]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 21100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 21100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362459551510318410, 362459557510577504⟩, ⟨523764445206299768, 523850147088242726⟩, true⟩

def words01 : List Nat := [371284360183399254, 371284359793010220, 371284360855757560, 371284361521522581, 371284362429132798, 371284363336901778, 371284364256242720, 371284364256900568, 371284362194965653, 371284361021329789]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 21110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 21100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362448895556439761, 362448901562551795⟩, ⟨748989260828555607, 749075086355629349⟩, true⟩

def words02 : List Nat := [371284360905595904, 371284360906253946, 371284359346195863, 371284357773328817, 371284356200368529, 371284355056902988, 371284353115763417, 371284352855617706, 371284352595268206, 371284352347518934]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 21120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 21100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362471875471788155, 362471881483852247⟩, ⟨263125402105441072, 263211353430069076⟩, true⟩

def words03 : List Nat := [371284350670303131, 371284349517992182, 371284348365458823, 371284348147339126, 371284344952556183, 371284341361574725, 371284337770658766, 371284335757422161, 371284332940291827, 371284332352037208]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 21130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 21100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362468627241881930, 362468633259888536⟩, ⟨331712998206667464, 331799075186218586⟩, true⟩

def words04 : List Nat := [371284331763591242, 371284331017794419, 371284328581583111, 371284328373627311, 371284328644854484, 371284328645513263, 371284326515471868, 371284323987801736, 371284321460107955, 371284321159424528]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 21140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 21100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362457288589250958, 362457294613192785⟩, ⟨571724021091333488, 571810223631373842⟩, true⟩

def words05 : List Nat := [371284321173706998, 371284321929901388, 371284322233771291, 371284322234441611, 371284320683543431, 371284319821473172, 371284320321347585, 371284320322006871, 371284319057062382, 371284317780661187]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 21150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 21100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362505991385175262, 362505997415034653⟩, ⟨(-459081943018703834), (-458995615234347920)⟩, true⟩

def words06 : List Nat := [371284316504089763, 371284316160709638, 371284315456424009, 371284316216718375, 371284316482815022, 371284316483475949, 371284314448255937, 371284314223840975, 371284315996532179, 371284317021324656]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 21160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 21100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362501035964202531, 362501042000053872⟩, ⟨(-354093682658591995), (-354007227993421809)⟩, true⟩

def words07 : List Nat := [371284318057809112, 371284319094411831, 371284322016716065, 371284323819239395, 371284325351756107, 371284326884373866, 371284328417861211, 371284328418521135, 371284327776960676, 371284328566882945]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 21170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 21100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362515125622444498, 362515131664188238⟩, ⟨(-652466307025591075), (-652379727529121017)⟩, true⟩

def words08 : List Nat := [371284331124816214, 371284332336496002, 371284333349873525, 371284334363386050, 371284335756166125, 371284336398117342, 371284339258498050, 371284342118870341, 371284344512603673, 371284345966131086]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 21180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 21100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362540922180753874, 362540928228470264⟩, ⟨(-1199017874069970835), (-1198931167982684181)⟩, true⟩

def words09 : List Nat := [371284349637466269, 371284353308801129, 371284359197417760, 371284362125399179, 371284364653766291, 371284367182100936, 371284370250473218, 371284372202551385, 371284374870738967, 371284377538975303]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 21190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 21100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 21100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk211
