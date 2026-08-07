import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk031

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360664178974084256, 360664179020142109⟩, ⟨(-232624909576312489), (-232624812578955625)⟩, true⟩

def state01 : KState := ⟨⟨360907113098269284, 360907113144641618⟩, ⟨(-987526484501782230), (-987526386527991820)⟩, true⟩

def words00 : List Nat := [360589181955318791, 360589283420401047, 360589428436801118, 360589573359799199, 360589621455211476, 360589621455244787, 360589568276194757, 360589538481090777, 360589580544437404, 360589682612167176]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 3100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 3100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360470185292537862, 360470185339228236⟩, ⟨372768709151209142, 372768808115709822⟩, true⟩

def words01 : List Nat := [360589705835617791, 360589729044151758, 360589764525247280, 360589853828106604, 360589866491539950, 360589879146852995, 360589879146882795, 360589840218869921, 360589700827524725, 360589662521316605]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 3110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 3100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360709044030382863, 360709044077389265⟩, ⟨(-372514882902922326), (-372514782950797892)⟩, true⟩

def words02 : List Nat := [360589686914631401, 360589760830286084, 360589779715451003, 360589798588533072, 360589798588561182, 360589838048726310, 360589929516069386, 360590020924954689, 360590029769702533, 360590067781333437]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 3120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 3100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360936245892004135, 360936245939328566⟩, ⟨(-1086106851692126758), (-1086106750742976490)⟩, true⟩

def words03 : List Nat := [360590150160322607, 360590232486733875, 360590338477014292, 360590345123190243, 360590345123221484, 360590256310754813, 360590178648196243, 360590241877226419, 360590352069630289, 360590462191877762]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 3130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 3100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360590224682498458, 360590224730145806⟩, ⟨(-1387028562707414), (-1386926598030422)⟩, true⟩

def words04 : List Nat := [360590518488309603, 360590518488343406, 360590475944765575, 360590428303672923, 360590380692868007, 360590258059842193, 360590165637470334, 360590022596826684, 360589879647024983, 360589784575719266]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 3140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 3100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨359635619190893454, 359635619238860624⟩, ⟨3012601049327668844, 3012601152301411420⟩, true⟩

def words05 : List Nat := [360589820462949557, 360589856327422362, 360589856327452614, 360589841967597079, 360589797723246855, 360589726865223909, 360589656052081389, 360589514800226669, 360589275823916122, 360588974033892717]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 3150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 3100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360438372449788772, 360438372498077751⟩, ⟨471752804840426150, 471752908832705336⟩, true⟩

def words06 : List Nat := [360588672434807756, 360588415154229700, 360588230023968430, 360588142884979120, 360588055801050693, 360587882330151515, 360587611435852465, 360587438441933253, 360587265557182630, 360587190450390908]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 3160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 3100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360167690541574845, 360167690590190095⟩, ⟨1331176116024046678, 1331176221052226336⟩, true⟩

def words07 : List Nat := [360587143519500283, 360587017285145331, 360586891130351687, 360586799401457774, 360586770311069685, 360586708947936521, 360586647623429506, 360586534308843511, 360586431144115467, 360586299464734821]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 3170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 3100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360544138854570668, 360544138903508703⟩, ⟨131443887220324812, 131443993276581548⟩, true⟩

def words08 : List Nat := [360586167868134350, 360586133331874366, 360586069323519634, 360585955729821989, 360585842207449825, 360585647262688558, 360585511197599011, 360585471846266971, 360585432519610624, 360585343917075030]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 3180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 3100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360737395952696365, 360737396001959269⟩, ⟨(-485641849160011604), (-485641742065807042)⟩, true⟩

def words09 : List Nat := [360585414501203143, 360585497945925970, 360585625986730295, 360585658229581271, 360585658229613173, 360585604526958144, 360585550857892244, 360585585516723082, 360585632957528088, 360585680368699099]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 3190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 3100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 3100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk031
