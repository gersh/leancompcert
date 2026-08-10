import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk972A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk972B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk972A

def state06 : KState := ⟨⟨360586857760125377, 360586920314976712⟩, ⟨(-444680335501863553), (-440572123561991163)⟩, true⟩

def words05 : List Nat := [360582390517774179, 360582390489557542, 360582390462551592, 360582390518420378, 360582390531492962, 360582390544795405, 360582390546056526, 360582390485951910, 360582390474546780, 360582390522731496]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 97250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 97200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588308496085198, 360588371064225873⟩, ⟨(-585805912505363521), (-581696407978428473)⟩, true⟩

def words06 : List Nat := [360582390617061427, 360582390695495920, 360582390710554623, 360582390725755186, 360582390726957690, 360582390685895566, 360582390754344644, 360582390823061394, 360582390838563436, 360582390901505449]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 97260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 97200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360592275531094581, 360592338112587092⟩, ⟨(-971690031223653320), (-967579227898809902)⟩, true⟩

def words07 : List Nat := [360582391052848087, 360582391204644461, 360582391336218798, 360582391431807215, 360582391436965300, 360582391442231787, 360582391528541681, 360582391675186032, 360582391778598397, 360582391882306783]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 97270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 97200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360600180314581085, 360600242909524752⟩, ⟨(-1740805171647943598), (-1736693059730377910)⟩, true⟩

def words08 : List Nat := [360582391932117741, 360582391933529959, 360582391974741433, 360582392049161832, 360582392096341908, 360582392146155477, 360582392147413457, 360582392144168539, 360582392223758249, 360582392408864564]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 97280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 97200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360563289449207146, 360563352057472515⟩, ⟨1848499811163379269, 1852613219214054241⟩, true⟩

def words09 : List Nat := [360582392586019653, 360582392763445251, 360582392851544561, 360582392852956943, 360582392835679484, 360582392728341819, 360582392620591508, 360582392597881385, 360582392469750922, 360582392275552824]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 97290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 97200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 97200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk972B
