import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk899A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588093429726055, 360588146549493148⟩, ⟨(-555355067104396150), (-552130278303162878)⟩, true⟩

def state01 : KState := ⟨⟨360573379007757575, 360573432139907311⟩, ⟨767416319501888234, 770642221560768338⟩, true⟩

def words00 : List Nat := [360582005014119649, 360582004986010427, 360582004868449305, 360582004767911472, 360582004667031689, 360582004535276676, 360582004279832990, 360582003946237934, 360582003612369807, 360582003402520600]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 89900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 89900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360558835408231842, 360558888552584869⟩, ⟨2075156623185050748, 2078383622502375110⟩, true⟩

def words01 : List Nat := [360582003308238895, 360582003299016937, 360582003289657798, 360582003174897899, 360582003085556248, 360582002909759051, 360582002733584216, 360582002681202111, 360582002505161466, 360582002249454335]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 89910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 89900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360570358550176368, 360570411706798305⟩, ⟨1038969514373561628, 1042197616971426828⟩, true⟩

def words02 : List Nat := [360582001993463466, 360582001774897691, 360582001651180294, 360582001651238196, 360582001651204827, 360582001533757804, 360582001292550587, 360582001106272241, 360582000919622658, 360582000693976905]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 89920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 89900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574016739453302, 360574069908425120⟩, ⟨709962391794630387, 713191605079252663⟩, true⟩

def words03 : List Nat := [360582000566268397, 360582000368604397, 360582000170696070, 360582000074585190, 360582000055717660, 360582000006029797, 360581999956181684, 360581999843306132, 360581999632704148, 360581999546017729]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 89930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 89900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360560008895889001, 360560062077101208⟩, ⟨1969870824144442681, 1973101138390916603⟩, true⟩

def words04 : List Nat := [360581999458901906, 360581999458647576, 360581999334795595, 360581999116532852, 360581998898063153, 360581998648913980, 360581998476327562, 360581998208065779, 360581997939668311, 360581997609490213]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 89940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 89900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk899A
