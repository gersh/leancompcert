import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk539A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk539B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk539A

def state06 : KState := ⟨⟨360615587125025496, 360615605504852666⟩, ⟨(-1819585969311262118), (-1818915867159001848)⟩, true⟩

def words05 : List Nat := [360581896059242368, 360581896105761588, 360581896412646659, 360581896489713585, 360581896490415264, 360581896241092429, 360581895999532771, 360581896282262102, 360581896907575290, 360581897533036744]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 53950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 53900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588734664394075, 360588753051362973⟩, ⟨(-370710752465048618), (-370040264909676340)⟩, true⟩

def words06 : List Nat := [360581897986528901, 360581898097268032, 360581898097887109, 360581898058387972, 360581898018684531, 360581897824997534, 360581897612778152, 360581897228873006, 360581896844839178, 360581896771788578]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 53960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 53900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360525161793875327, 360525180187896663⟩, ⟨3060748703608292737, 3061419571819296739⟩, true⟩

def words07 : List Nat := [360581897107255924, 360581897442853991, 360581897602692610, 360581897603441907, 360581897420552605, 360581897018889538, 360581896617032446, 360581896036755829, 360581895197992276, 360581894148100800]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 53970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 53900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360546397098529305, 360546415499622208⟩, ⟨1914379364156912419, 1915050614126677895⟩, true⟩

def words08 : List Nat := [360581893098079356, 360581892207917573, 360581891489318519, 360581890966574016, 360581890443777727, 360581889596819923, 360581888407224770, 360581887560337514, 360581886713259247, 360581885968489159]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 53980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 53900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360555942603672119, 360555961011919055⟩, ⟨1398941435275861479, 1399613071526456799⟩, true⟩

def words09 : List Nat := [360581885312204726, 360581884389688621, 360581883467061147, 360581882887050979, 360581882479473340, 360581881985902861, 360581881492269129, 360581880782008013, 360581880251624293, 360581879772502879]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 53990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 53900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 53900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk539B
