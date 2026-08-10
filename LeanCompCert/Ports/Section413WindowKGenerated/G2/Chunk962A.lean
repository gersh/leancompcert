import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk962A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360605467825201280, 360605528972029832⟩, ⟨(-2240818042941351066), (-2236846030433565320)⟩, true⟩

def state01 : KState := ⟨⟨360591633526900121, 360591694687043277⟩, ⟨(-909974823507687256), (-906001530069485300)⟩, true⟩

def words00 : List Nat := [360582277335819706, 360582277412788988, 360582277526014958, 360582277639645530, 360582277709567552, 360582277762976310, 360582277764219318, 360582277763286171, 360582277769002761, 360582277868487504]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 96200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 96200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360566794061769055, 360566855235045570⟩, ⟨1480022606278452723, 1483997163344666385⟩, true⟩

def words01 : List Nat := [360582278075545148, 360582278282866395, 360582278422674196, 360582278482359934, 360582278483548156, 360582278469927335, 360582278457155724, 360582278458551431, 360582278353389526, 360582278194548217]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 96210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 96200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590369826655846, 360590431013129367⟩, ⟨(-788479523628594212), (-784503696683366016)⟩, true⟩

def words02 : List Nat := [360582278035389411, 360582278022980297, 360582278170413174, 360582278318111909, 360582278373138031, 360582278396272292, 360582278483427680, 360582278571017485, 360582278629925152, 360582278716087007]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 96220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 96200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360575073435104688, 360575134634866754⟩, ⟨683634260289455448, 687611366057596576⟩, true⟩

def words03 : List Nat := [360582278747706038, 360582278779479036, 360582278918992178, 360582279124939066, 360582279279610249, 360582279434528468, 360582279502447205, 360582279503843160, 360582279464019064, 360582279391371925]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 96230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 96200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580386526892179, 360580447739811688⟩, ⟨172212093588322786, 176190465694663178⟩, true⟩

def words04 : List Nat := [360582279330530169, 360582279331926200, 360582279237840102, 360582279060872706, 360582278883681075, 360582278679348134, 360582278529287536, 360582278467686898, 360582278405934617, 360582278290104620]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 96240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 96200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk962A
