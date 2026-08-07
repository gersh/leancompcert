import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk272

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360653012051342514, 360653016463734094⟩, ⟨(-1910701597854243165), (-1910620418555707215)⟩, true⟩

def state01 : KState := ⟨⟨360615114292078382, 360615118707878408⟩, ⟨(-879717147637538187), (-879635875612037489)⟩, true⟩

def words00 : List Nat := [360582777552538756, 360582780042648710, 360582782737367102, 360582785431989904, 360582787780461382, 360582789308028742, 360582790159389433, 360582791010724355, 360582791038392996, 360582792226837211]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 27200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 27200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584881429632120, 360584885848799795⟩, ⟨(-56703937166817058), (-56622573490471774)⟩, true⟩

def words01 : List Nat := [360582794762014485, 360582797297073743, 360582799046869303, 360582800605872859, 360582801819449386, 360582803033041936, 360582804693971023, 360582805588972147, 360582805665715022, 360582805742503536]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 27210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 27200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360628444100058519, 360628448522608283⟩, ⟨(-1242746980696984476), (-1242665524943637654)⟩, true⟩

def words02 : List Nat := [360582806792055731, 360582808723166574, 360582810618189690, 360582812513137161, 360582813080071060, 360582813080428960, 360582812305183099, 360582812093665747, 360582812623408877, 360582814299665915]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 27220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 27200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360611044949382368, 360611049375340695⟩, ⟨(-768870135795038378), (-768788587209748056)⟩, true⟩

def words03 : List Nat := [360582815135304500, 360582815970921184, 360582817838247078, 360582820681718029, 360582822755945269, 360582824830079512, 360582825863848791, 360582825864206918, 360582826592729734, 360582827629178302]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 27230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 27200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360615650316922731, 360615654746253067⟩, ⟨(-894310715539319782), (-894229075083689140)⟩, true⟩

def words04 : List Nat := [360582830009311957, 360582831545451067, 360582832390272593, 360582833235074171, 360582833735427196, 360582835083376083, 360582836636560032, 360582838189698150, 360582839000007338, 360582840204581801]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 27240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 27200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360662055679823621, 360662060112540917⟩, ⟨(-2159426997509976809), (-2159345264743143835)⟩, true⟩

def words05 : List Nat := [360582840774308433, 360582841344095750, 360582843256508013, 360582843829025539, 360582843829356420, 360582843134322470, 360582842682523695, 360582844246853559, 360582847153081441, 360582850059177389]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 27250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 27200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360574016715757305, 360574021151891117⟩, ⟨240811960043230828, 240893785960922368⟩, true⟩

def words06 : List Nat := [360582852088406803, 360582853318857580, 360582855576900449, 360582857834882453, 360582858886760688, 360582858887119321, 360582858600401812, 360582857466005571, 360582856331625275, 360582854807408570]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 27260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 27200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360564729485525534, 360564733925041932⟩, ⟨494307924633352304, 494389842811403278⟩, true⟩

def words07 : List Nat := [360582855500919666, 360582856518351972, 360582856860022506, 360582856860382925, 360582856822635944, 360582856434757217, 360582856999059658, 360582857383514026, 360582857383842156, 360582856719866397]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 27270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 27200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360661503342471845, 360661507785373037⟩, ⟨(-2146037932235695817), (-2145955921703297695)⟩, true⟩

def words08 : List Nat := [360582856731783185, 360582858082772171, 360582860773639117, 360582863464378090, 360582864865819613, 360582866316773040, 360582868156152611, 360582869995504464, 360582872536863014, 360582875418596324]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 27280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 27200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360613349249163815, 360613353695487994⟩, ⟨(-831769076453141205), (-831686972490780623)⟩, true⟩

def words09 : List Nat := [360582877269251885, 360582879119808854, 360582880882888803, 360582883319220318, 360582885141808476, 360582886964321486, 360582888076752657, 360582888077111736, 360582888970802554, 360582890087104024]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 27290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 27200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 27200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk272
