import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk937A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362478080646544505, 362478213913731459⟩, ⟨642267594911493276, 650698514586417800⟩, true⟩

def state01 : KState := ⟨⟨362484490415803673, 362484623712392107⟩, ⟨41715167812508382, 50148842553253642⟩, true⟩

def words00 : List Nat := [371285158369539607, 371285158377790419, 371285158498506859, 371285158620614140, 371285158723741978, 371285158727022389, 371285158731622758, 371285158789148578, 371285158858313468, 371285158861709718]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 93700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 93700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362489461853924438, 362489595180423513⟩, ⟨(-424178802793017633), (-415742324975114317)⟩, true⟩

def words01 : List Nat := [371285158858450534, 371285158856088223, 371285158941996115, 371285158978470738, 371285159048290356, 371285159119398089, 371285159185694424, 371285159188976276, 371285159171978672, 371285159223434417]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 93710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 93700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478528795363798, 362478662151126756⟩, ⟨600493833281758217, 608933053859977243⟩, true⟩

def words02 : List Nat := [371285159318134951, 371285159321415850, 371285159264627775, 371285159186892488, 371285159107936936, 371285159040158258, 371285158922621731, 371285158889649073, 371285158855518416, 371285158822991261]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 93720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 93700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487594150867410, 362487727536196235⟩, ⟨(-249263055958226593), (-240821064017815377)⟩, true⟩

def words03 : List Nat := [371285158755919199, 371285158748315036, 371285158822997188, 371285158826278681, 371285158761084916, 371285158677900594, 371285158593391713, 371285158557292322, 371285158500491995, 371285158531555600]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 93730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 93700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484393347911286, 362484526762875381⟩, ⟨50764234619469634, 59209004713768464⟩, true⟩

def words04 : List Nat := [371285158561155919, 371285158564460070, 371285158492800854, 371285158497606813, 371285158535282703, 371285158538571756, 371285158458770480, 371285158379807106, 371285158321843187, 371285158325592328]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 93740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 93700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk937A
