import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk720A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360594655305928246, 360594688792299822⟩, ⟨(-890678283824524270), (-889049763511985660)⟩, true⟩

def state01 : KState := ⟨⟨360603991533362573, 360604025029371675⟩, ⟨(-1562890140457069208), (-1561260926195053246)⟩, true⟩

def words00 : List Nat := [360582341367570232, 360582341747773411, 360582342031632121, 360582342315594661, 360582342550365312, 360582342930624235, 360582343291387828, 360582343652332437, 360582343860054420, 360582344162195896]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 72000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 72000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360612689543963754, 360612723049619837⟩, ⟨(-2189327411186824457), (-2187697502197301603)⟩, true⟩

def words01 : List Nat := [360582344619059638, 360582345076213595, 360582345536575428, 360582345804629340, 360582345908509802, 360582346012484635, 360582346145835205, 360582346376265874, 360582346798873384, 360582347221705794]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 72010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 72000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360573245240655500, 360573278756056971⟩, ⟨651551958444721379, 653182569344864295⟩, true⟩

def words02 : List Nat := [360582347548220436, 360582347682380481, 360582347812378870, 360582347942659168, 360582347974589604, 360582347975611823, 360582347815157689, 360582347540064094, 360582347264779595, 360582346957769381]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 72020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 72000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360531950944790282, 360531984469814703⟩, ⟨3626304772143744935, 3627936076232677465⟩, true⟩

def words03 : List Nat := [360582346899244268, 360582346966806068, 360582346967721305, 360582346912677092, 360582346665053545, 360582346368765484, 360582346072186345, 360582345709878695, 360582345191090502, 360582344493082786]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 72030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 72000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360589131927909502, 360589165462587630⟩, ⟨(-493337101295756409), (-491705101706938529)⟩, true⟩

def words04 : List Nat := [360582343794863002, 360582343232444202, 360582342766714355, 360582342493579118, 360582342220362231, 360582341783943028, 360582341395013138, 360582341198747813, 360582341002185476, 360582341059016453]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 72040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 72000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk720A
