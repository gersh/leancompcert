import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk923A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk923B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk923A

def state06 : KState := ⟨⟨360594376773690209, 360594432958363491⟩, ⟨(-1153568708619279305), (-1150064596633741233)⟩, true⟩

def words05 : List Nat := [360581981072301990, 360581981018932419, 360581981027418690, 360581981028754682, 360581981010930570, 360581980888439862, 360581980765686679, 360581980844067020, 360581980979970626, 360581981116172158]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 92350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 92300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360578006375296034, 360578062572684039⟩, ⟨358379154864669126, 361884441244149198⟩, true⟩

def words06 : List Nat := [360581981171078994, 360581981172414917, 360581981164112282, 360581981219433149, 360581981220577384, 360581981168863921, 360581981000087410, 360581980742044077, 360581980483748326, 360581980342969242]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 92360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 92300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360576255566545466, 360576311776539138⟩, ⟨520102713419904267, 523609164245693813⟩, true⟩

def words07 : List Nat := [360581980344126894, 360581980387976301, 360581980389167028, 360581980360084395, 360581980213858893, 360581980036308191, 360581979858355083, 360581979827984189, 360581979829195661, 360581979769224197]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 92370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 92300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360606274112809246, 360606330335399544⟩, ⟨(-2253105203007357600), (-2249597588440443098)⟩, true⟩

def words08 : List Nat := [360581979764635681, 360581979888099780, 360581980128205201, 360581980368561632, 360581980508096161, 360581980650638054, 360581980909926467, 360581981169601870, 360581981404603432, 360581981669529054]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 92380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 92300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360590334338889778, 360590390574235077⟩, ⟨(-780379411998147927), (-776870618936435851)⟩, true⟩

def words09 : List Nat := [360581981844657239, 360581982019920050, 360581982168211437, 360581982399080691, 360581982560710811, 360581982722552504, 360581982814595161, 360581982815931696, 360581982881990355, 360581982974545286]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 92390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 92300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 92300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk923B
