import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk882A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360585045077460448, 360585096131806853⟩, ⟨(-260468379868631677), (-257427522687375859)⟩, true⟩

def state01 : KState := ⟨⟨360568738014464900, 360568789080767877⟩, ⟨1177900962486395121, 1180942874297122135⟩, true⟩

def words00 : List Nat := [360582177626570456, 360582177639447665, 360582177640579806, 360582177589146061, 360582177537513056, 360582177377171444, 360582177293707190, 360582177207492388, 360582177121159834, 360582176937862279]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 88200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 88200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360595248100307391, 360595299178608966⟩, ⟨(-1160698848249344020), (-1157655877982537426)⟩, true⟩

def words01 : List Nat := [360582176787118766, 360582176765075360, 360582176762779429, 360582176787514031, 360582176788686234, 360582176704382456, 360582176619839231, 360582176653013352, 360582176802788827, 360582176952857926]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 88210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 88200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591214454878197, 360591265545288616⟩, ⟨(-804950341571927928), (-801906303002515818)⟩, true⟩

def words02 : List Nat := [360582177004000069, 360582177005271174, 360582176977818703, 360582177029122688, 360582177046798624, 360582177048070720, 360582176991103433, 360582176870186985, 360582176749005706, 360582176831537185]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 88220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 88200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360558301092918701, 360558352195293819⟩, ⟨2099162943579940198, 2102208037854470878⟩, true⟩

def words03 : List Nat := [360582176893769385, 360582176956232487, 360582176957365038, 360582176955552256, 360582176853003445, 360582176662357747, 360582176471324912, 360582176408788558, 360582176217797652, 360582175949122633]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 88230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 88200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360569004292921583, 360569055407317799⟩, ⟨1154750613835386486, 1157796768908218778⟩, true⟩

def words04 : List Nat := [360582175680165240, 360582175539863396, 360582175597544968, 360582175676093215, 360582175677277741, 360582175635183382, 360582175464553469, 360582175283635597, 360582175102366544, 360582174917447071]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 88240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 88200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk882A
