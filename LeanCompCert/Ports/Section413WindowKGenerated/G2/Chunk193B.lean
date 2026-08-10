import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk193A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk193B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk193A

def state06 : KState := ⟨⟨360406316300011641, 360406318469252461⟩, ⟨3439303683474036776, 3439332106883719066⟩, true⟩

def words05 : List Nat := [360584008891611958, 360584008928905750, 360584008929126187, 360584007635453454, 360584003684318391, 360583997820963294, 360583991958142975, 360583986856067629, 360583979097481998, 360583969921054306]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 19350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 19300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360477180544528770, 360477182716108396⟩, ⟨2067032347265512812, 2067060815966173896⟩, true⟩

def words06 : List Nat := [360583960745517661, 360583952704379852, 360583946701145137, 360583941066097336, 360583935431612043, 360583927515898138, 360583918489458753, 360583911434057880, 360583904379314454, 360583897265203191]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 19360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 19300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360467707148727787, 360467709322664317⟩, ⟨2250547610695380500, 2250576125061033078⟩, true⟩

def words07 : List Nat := [360583891756440215, 360583884162604122, 360583876569504590, 360583871623649412, 360583868032748946, 360583863385650276, 360583858739002034, 360583852752134246, 360583844113911123, 360583838121687075]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 19370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 19300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360536869007094266, 360536871183367607⟩, ⟨909767668854214859, 909796228518991755⟩, true⟩

def words08 : List Nat := [360583832129998670, 360583828783731110, 360583825095715474, 360583819172365197, 360583813249585760, 360583806656403088, 360583801454132554, 360583798895443927, 360583796336992392, 360583792082208195]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 19380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 19300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360503498475006754, 360503500653619441⟩, ⟨1556973011244778176, 1557001616281093110⟩, true⟩

def words09 : List Nat := [360583789885585644, 360583790108737851, 360583790108940034, 360583789415962173, 360583786075041380, 360583780447570094, 360583774820634619, 360583767876133908, 360583762605848800, 360583758468891663]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 19390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 19300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 19300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk193B
