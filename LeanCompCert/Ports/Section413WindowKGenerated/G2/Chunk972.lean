import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk972

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360592311657415943, 360592374132130418⟩, ⟨(-975047485290285782), (-970947065057042644)⟩, true⟩

def state01 : KState := ⟨⟨360593720294281999, 360593782782301533⟩, ⟨(-1111956823806740886), (-1107855110254626496)⟩, true⟩

def words00 : List Nat := [360582385202567321, 360582385365671916, 360582385475430776, 360582385585344487, 360582385668111389, 360582385826406987, 360582386000497371, 360582386174848186, 360582386267002130, 360582386385697707]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 97200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 97200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360621889428457874, 360621951929793142⟩, ⟨(-3850450273729860513), (-3846347265688643463)⟩, true⟩

def words01 : List Nat := [360582386567106045, 360582386748924700, 360582387036128476, 360582387292125600, 360582387458463214, 360582387624933371, 360582387866070499, 360582388186917700, 360582388595008972, 360582389003412128]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 97210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 97200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590977832676984, 360591040347472885⟩, ⟨(-845177042463940538), (-841072725714650210)⟩, true⟩

def words02 : List Nat := [360582389343118258, 360582389577517191, 360582389732818970, 360582389888506041, 360582390017092406, 360582390060348775, 360582390061625120, 360582390037602175, 360582390013316897, 360582390094716926]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 97220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 97200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360567756604089634, 360567819132172293⟩, ⟨1412819289987424696, 1416924898673893374⟩, true⟩

def words03 : List Nat := [360582390290584097, 360582390486718227, 360582390629569625, 360582390699323763, 360582390741951362, 360582390784968107, 360582390794798957, 360582390796210452, 360582390700725455, 360582390552356106]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 97230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 97200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360589146629299920, 360589209170689330⟩, ⟨(-667227842635195881), (-663120939934566703)⟩, true⟩

def words04 : List Nat := [360582390403648492, 360582390382576116, 360582390477309999, 360582390572339006, 360582390576936574, 360582390578348148, 360582390477372227, 360582390440653794, 360582390444908092, 360582390516485933]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 97240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 97200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk972
