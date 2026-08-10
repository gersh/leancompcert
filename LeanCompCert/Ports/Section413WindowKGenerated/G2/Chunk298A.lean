import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk298A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360478478745365950, 360478484083433837⟩, ⟨3129056120995215635, 3129163701866174591⟩, true⟩

def state01 : KState := ⟨⟨360563905448735835, 360563910790533151⟩, ⟨582883958518545783, 582991650545393177⟩, true⟩

def words00 : List Nat := [360583486053549546, 360583482910554731, 360583480334751356, 360583478880564929, 360583477426445384, 360583474999258498, 360583472609194343, 360583470866034940, 360583469122873623, 360583467706016056]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 29800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 29800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360549577834645069, 360549583180207910⟩, ⟨1009926577739605367, 1010034382035623299⟩, true⟩

def words01 : List Nat := [360583467050338873, 360583465698755500, 360583464347192584, 360583462971723750, 360583462162416903, 360583460837271248, 360583459512174767, 360583457610518769, 360583455354605948, 360583454219176241]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 29810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 29800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360549148097394582, 360549153446679215⟩, ⟨1022737471757383875, 1022845387056073037⟩, true⟩

def words02 : List Nat := [360583453083686632, 360583452118003613, 360583451420583580, 360583450165396801, 360583448910230257, 360583447356177588, 360583446363750192, 360583445347893221, 360583444332061493, 360583442598105835]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 29820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 29800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360640647493841636, 360640652846859167⟩, ⟨(-1707223189712372250), (-1707115163043100918)⟩, true⟩

def words03 : List Nat := [360583441448979389, 360583440816411991, 360583440669857211, 360583441192330095, 360583441192701158, 360583440687848486, 360583440796558546, 360583441975690297, 360583443893264828, 360583445810799950]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 29830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 29800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360575305083529390, 360575310440319685⟩, ⟨242631006296438175, 242739145563380681⟩, true⟩

def words04 : List Nat := [360583446781001742, 360583447104785213, 360583447598762850, 360583448092824838, 360583448093156187, 360583448086463545, 360583446962588078, 360583445281936758, 360583443601314476, 360583442404995176]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 29840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 29800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk298A
