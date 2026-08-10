import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk565A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk565B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk565A

def state06 : KState := ⟨⟨360591677361407520, 360591697632167843⟩, ⟨(-562074955192292441), (-561300339524466779)⟩, true⟩

def words05 : List Nat := [360581768505166324, 360581769691711984, 360581770637749024, 360581771272210471, 360581771827130769, 360581772382248196, 360581773084172926, 360581773474628761, 360581773650794955, 360581773827080867]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 56550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 56500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360604448664937465, 360604468943129304⟩, ⟨(-1284470450775872293), (-1283695414743870425)⟩, true⟩

def words06 : List Nat := [360581774240348033, 360581774893246133, 360581775493252860, 360581776093385027, 360581776423370287, 360581776441854711, 360581776451678565, 360581776461722092, 360581776783665211, 360581777185607891]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 56560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 56500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360579597502242828, 360579617787941470⟩, ⟨121485426688869317, 122260887417283799⟩, true⟩

def words07 : List Nat := [360581777422235576, 360581777658940935, 360581777831031890, 360581778244127993, 360581778507909229, 360581778771814225, 360581778878821534, 360581778879609684, 360581778675134166, 360581778637842801]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 56570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 56500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360568344119148683, 360568364412277518⟩, ⟨758186586650999158, 758962467817410742⟩, true⟩

def words08 : List Nat := [360581778600300914, 360581778476244742, 360581778218765907, 360581777804950898, 360581777391016674, 360581776898094133, 360581776561070956, 360581776444850984, 360581776328538195, 360581776012698395]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 56580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 56500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360599972463620766, 360599992764185373⟩, ⟨(-1031887702680520287), (-1031111400686956183)⟩, true⟩

def words09 : List Nat := [360581775851256070, 360581775927042888, 360581776105740964, 360581776106529337, 360581775974121778, 360581775517110787, 360581775059965010, 360581774924947867, 360581775247455224, 360581775570130729]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 56590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 56500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 56500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk565B
