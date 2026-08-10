import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk834A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk834B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk834A

def state06 : KState := ⟨⟨362492590739325318, 362492695529799256⟩, ⟨(-621835347658877226), (-615929928250550250)⟩, true⟩

def words05 : List Nat := [371285314693581583, 371285314778837440, 371285314952872927, 371285315075750122, 371285315241327791, 371285315408052583, 371285315546463475, 371285315549358400, 371285315584600224, 371285315676595358]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 83450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 83400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481804348697495, 362481909164985598⟩, ⟨278451979588925914, 284359553583417562⟩, true⟩

def words06 : List Nat := [371285315826100009, 371285315828997791, 371285315822502858, 371285315813312146, 371285315834549245, 371285315837769983, 371285315827967763, 371285315859371683, 371285315889589526, 371285315892595320]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 83460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 83400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495223671520472, 362495328513983071⟩, ⟨(-841710924293693984), (-835801165382603534)⟩, true⟩

def words07 : List Nat := [371285315956465060, 371285316062689935, 371285316262837059, 371285316272621117, 371285316274925717, 371285316252381017, 371285316346530896, 371285316395914470, 371285316517825826, 371285316641037340]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 83470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 83400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362492522387787154, 362492627256430879⟩, ⟨(-616203115023826678), (-610291170381085118)⟩, true⟩

def words08 : List Nat := [371285316762978628, 371285316784464987, 371285316924883768, 371285317066803790, 371285317235788938, 371285317299459564, 371285317346794715, 371285317395142097, 371285317501388184, 371285317592270897]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 83480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 83400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488092087213092, 362488196981875419⟩, ⟨(-246255867686608886), (-240341750617975622)⟩, true⟩

def words09 : List Nat := [371285317790027259, 371285317988929977, 371285318186819289, 371285318211273844, 371285318278772864, 371285318347791330, 371285318558650726, 371285318597678922, 371285318634325855, 371285318672027418]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 83490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 83400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 83400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk834B
