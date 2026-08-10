import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk642A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485902207691486, 362485962963334031⟩, ⟨(-31618975671980668), (-28984448978890918)⟩, true⟩

def state01 : KState := ⟨⟨362469483348572104, 362469544123667678⟩, ⟨1022590800887988279, 1025226576566804967⟩, true⟩

def words00 : List Nat := [371285511655841535, 371285511658025525, 371285511537774836, 371285511417617984, 371285511296607934, 371285511250020131, 371285511113616336, 371285511052095185, 371285510989815001, 371285510897948426]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 64200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 64200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362492929152153289, 362492989946986398⟩, ⟨(-483021433808730217), (-480384390683100005)⟩, true⟩

def words01 : List Nat := [371285510650794676, 371285510504903738, 371285510425733862, 371285510427917703, 371285510199356616, 371285509928786236, 371285509657313337, 371285509629447869, 371285509651938324, 371285509770865144]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 64210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 64200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477991709266166, 362478052523787647⟩, ⟨476312762952501448, 478951070566932168⟩, true⟩

def words02 : List Nat := [371285509888311196, 371285509890495368, 371285509774662427, 371285509839962105, 371285509912270808, 371285509914460906, 371285509738589095, 371285509563435810, 371285509387429579, 371285509336345127]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 64220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 64200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362466577416522129, 362466638250765179⟩, ⟨1209593307651676484, 1212232882078826424⟩, true⟩

def words03 : List Nat := [371285509348163361, 371285509477023852, 371285509592528963, 371285509594713426, 371285509387102613, 371285509229652301, 371285509153550013, 371285509155734655, 371285508916894045, 371285508625641874]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 64230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 64200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487307642690892, 362487368496472577⟩, ⟨(-122183549979323586), (-119542720289158050)⟩, true⟩

def words04 : List Nat := [371285508333380544, 371285508258634931, 371285508080358282, 371285508056209748, 371285508031401930, 371285507970043014, 371285507766198522, 371285507747280133, 371285507907121999, 371285507938344468]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 64240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 64200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk642A
