import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk548A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360630716280592044, 360630735260879188⟩, ⟨(-2684875641004273193), (-2684172885187911095)⟩, true⟩

def state01 : KState := ⟨⟨360621790431241689, 360621809418803266⟩, ⟨(-2195812874438513304), (-2195109719949397650)⟩, true⟩

def words00 : List Nat := [360581755624415390, 360581756419307600, 360581757205867397, 360581757992611266, 360581758639224739, 360581759059992699, 360581759314489095, 360581759569065634, 360581759979487068, 360581760711063043]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 54800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 54800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360558621999210959, 360558640993936960⟩, ⟨1266869553008839767, 1267573100216927661⟩, true⟩

def words01 : List Nat := [360581761662936171, 360581762614920522, 360581763303416601, 360581763660105409, 360581763853345872, 360581764046779842, 360581764124940126, 360581764125702106, 360581763872081091, 360581763451073351]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 54810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 54800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593726287977628, 360593745289894995⟩, ⟨(-657760094136958169), (-657056152662768749)⟩, true⟩

def words02 : List Nat := [360581763029911305, 360581762708161860, 360581762643627498, 360581762734609234, 360581762735314839, 360581762500749341, 360581762034803596, 360581761837458785, 360581761773646382, 360581761992988815]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 54820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 54800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360592266957639666, 360592285966825176⟩, ⟨(-577729993958007134), (-577025653936782116)⟩, true⟩

def words03 : List Nat := [360581761993679672, 360581761952501114, 360581762201136238, 360581762758199813, 360581763096189413, 360581763434286822, 360581763607016162, 360581763788531371, 360581763981019158, 360581764173751805]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 54830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 54800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360591363797141343, 360591382813502412⟩, ⟨(-528183135865086704), (-527478402300447836)⟩, true⟩

def words04 : List Nat := [360581764635049649, 360581764985030016, 360581765142897590, 360581765300842658, 360581765301491680, 360581765413231654, 360581765695560142, 360581765978021486, 360581766068823554, 360581766244938477]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 54840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 54800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk548A
