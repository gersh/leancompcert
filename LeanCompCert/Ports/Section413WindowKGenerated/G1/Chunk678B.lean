import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk678A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk678B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk678A

def state06 : KState := ⟨⟨362478404616799056, 362478472792710280⟩, ⟨470896043471368855, 474020666286476797⟩, true⟩

def words05 : List Nat := [371285458949053266, 371285458754249295, 371285458578275413, 371285458580830332, 371285458504865483, 371285458458399672, 371285458411122200, 371285458364559863, 371285458166357681, 371285458066307193]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 67850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 67800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362474427118262437, 362474495314790056⟩, ⟨740827914770231145, 743953936722485473⟩, true⟩

def words06 : List Nat := [371285458056527315, 371285458058845518, 371285457862801830, 371285457667686329, 371285457471690228, 371285457288383808, 371285456995648788, 371285456920787786, 371285456845177274, 371285456769581901]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 67860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 67800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362482815058294888, 362482883275824823⟩, ⟨171506776236292291, 174634223719646593⟩, true⟩

def words07 : List Nat := [371285456631317303, 371285456655840376, 371285456760391209, 371285456762709751, 371285456578216611, 371285456363696973, 371285456148261113, 371285456128558572, 371285456001490902, 371285455966215508]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 67870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 67800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476776538503567, 362476844776944033⟩, ⟨581364181651783401, 584493048650924707⟩, true⟩

def words08 : List Nat := [371285455930065197, 371285455830142078, 371285455440297367, 371285455268457275, 371285455095501319, 371285454989293441, 371285454755985868, 371285454513769008, 371285454270586859, 371285454189945225]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 67880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 67800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362470227810950592, 362470296070291553⟩, ⟨1026044798641718819, 1029175084679328561⟩, true⟩

def words09 : List Nat := [371285454154657024, 371285454247117958, 371285454293101197, 371285454295420841, 371285454081808730, 371285453904913876, 371285453726771038, 371285453728855601, 371285453508633347, 371285453288033517]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 67890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 67800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 67800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk678B
