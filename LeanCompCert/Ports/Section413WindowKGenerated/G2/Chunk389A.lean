import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk389A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360592605701202254, 360592615000949105⟩, ⟨(-398237998805843686), (-397993479251045914)⟩, true⟩

def state01 : KState := ⟨⟨360577735791445098, 360577745096195906⟩, ⟨180167066143954558, 180411780377729540⟩, true⟩

def words00 : List Nat := [360582384069584115, 360582384002730957, 360582383669316039, 360582383832529662, 360582383832970150, 360582383703753646, 360582383618722375, 360582383020540745, 360582382422291391, 360582381739227974]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 38900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 38900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360559281411617970, 360559290721330209⟩, ⟨898302328183574693, 898547235490779205⟩, true⟩

def words01 : List Nat := [360582382009008385, 360582382398030799, 360582382398508762, 360582382206042695, 360582381356930229, 360582380220897348, 360582379084762511, 360582378607481543, 360582378344700044, 360582377752046828]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 38910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 38900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360592371116937184, 360592380431613092⟩, ⟨(-389568534839163682), (-389323434321435170)⟩, true⟩

def words02 : List Nat := [360582377224713227, 360582377711045339, 360582378855725791, 360582380000448442, 360582380580065621, 360582380580591886, 360582380503782046, 360582380246288551, 360582379988657092, 360582380086532785]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 38920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 38900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360581980456811620, 360581989776500627⟩, ⟨15056300722233536, 15301596423975258⟩, true⟩

def words03 : List Nat := [360582380087002616, 360582379948854720, 360582380330200773, 360582381375485095, 360582382045186743, 360582382714938228, 360582383054842909, 360582383055369389, 360582382739157555, 360582382729670221]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 38930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 38900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360548679182168752, 360548688506819588⟩, ⟨1311834674100775927, 1312080163040986737⟩, true⟩

def words04 : List Nat := [360582382720012346, 360582382693321466, 360582382010589348, 360582380997131209, 360582379983639289, 360582378803692387, 360582377952966364, 360582377003591650, 360582376054196599, 360582374775447085]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 38940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 38900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk389A
