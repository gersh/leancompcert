import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk949A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk949B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk949A

def state06 : KState := ⟨⟨360592233487272821, 360592293008201840⟩, ⟨(-967103377339185935), (-963286770499939151)⟩, true⟩

def words05 : List Nat := [360582147118415264, 360582147499820881, 360582147819357644, 360582148049142718, 360582148203170527, 360582148357540753, 360582148602309290, 360582148766756882, 360582148874821720, 360582148983070471]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 94950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 94900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601140721900227, 360601200255841104⟩, ⟨(-1812926426598647706), (-1809108584090415730)⟩, true⟩

def words06 : List Nat := [360582149201878728, 360582149522013743, 360582149825481821, 360582150129199720, 360582150337756391, 360582150462450664, 360582150639268227, 360582150816499026, 360582150990605756, 360582151192610324]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 94960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 94900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360596769309339110, 360596828856383545⟩, ⟨(-1397726327668961087), (-1393907240650558437)⟩, true⟩

def words07 : List Nat := [360582151338709268, 360582151484955523, 360582151714169393, 360582152029512826, 360582152287813266, 360582152546354941, 360582152737853524, 360582152901743144, 360582153057375461, 360582153213458639]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 94970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 94900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360589221309585086, 360589280869606046⟩, ⟨(-680850537299812155), (-677030217706876669)⟩, true⟩

def words08 : List Nat := [360582153417805286, 360582153511956005, 360582153520903926, 360582153529981724, 360582153531141373, 360582153462687403, 360582153478295443, 360582153509076157, 360582153510302259, 360582153560516692]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 94980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 94900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360597121930177919, 360597181503186204⟩, ⟨(-1431403417335614952), (-1427581864012166164)⟩, true⟩

def words09 : List Nat := [360582153669514752, 360582153778909666, 360582153998689610, 360582154108302209, 360582154123067428, 360582154137940814, 360582154139073327, 360582154164945245, 360582154324240333, 360582154483849438]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 94990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 94900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 94900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk949B
