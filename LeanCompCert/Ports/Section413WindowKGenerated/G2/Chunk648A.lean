import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk648A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586529883779010, 360586556781186560⟩, ⟨(-232944210399931037), (-231766823396002123)⟩, true⟩

def state01 : KState := ⟨⟨360570785136903596, 360570812042900638⟩, ⟨787302199301830769, 788480142948734853⟩, true⟩

def words00 : List Nat := [360582980198715855, 360582980199628158, 360582979973268645, 360582979627768569, 360582979282131580, 360582978804681656, 360582978511622500, 360582978413545242, 360582978315380852, 360582978068868062]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 64800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 64800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360597872246946236, 360597899161569261⟩, ⟨(-968403839936428078), (-967225337197395886)⟩, true⟩

def words01 : List Nat := [360582977931815044, 360582977982750334, 360582977983501174, 360582977984091401, 360582977878289452, 360582977556855006, 360582977235255768, 360582977218198813, 360582977449142700, 360582977680302428]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 64810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 64800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360562196912952750, 360562223836261804⟩, ⟨1344072758081363013, 1345251823891494469⟩, true⟩

def words02 : List Nat := [360582977719981857, 360582977720894573, 360582977523374714, 360582977292476164, 360582977061343200, 360582976768046176, 360582976237571237, 360582975524269024, 360582974810812164, 360582974288581587]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 64820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 64800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360557955776848871, 360557982708752759⟩, ⟨1619089087470074141, 1620268710527692799⟩, true⟩

def words03 : List Nat := [360582973969253244, 360582973720298249, 360582973471251439, 360582973103266303, 360582972864074158, 360582972565488468, 360582972266635966, 360582972080412371, 360582971814834872, 360582971430383353]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 64830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 64800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360569073502319053, 360569100442853546⟩, ⟨898111684325312957, 899291867033298967⟩, true⟩

def words04 : List Nat := [360582971045749969, 360582970593747725, 360582970283741450, 360582970142131430, 360582970000462846, 360582969621256602, 360582969004892231, 360582968492165469, 360582967979169247, 360582967703717591]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 64840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 64800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk648A
