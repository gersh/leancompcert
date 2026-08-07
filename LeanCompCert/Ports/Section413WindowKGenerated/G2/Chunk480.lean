import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk480

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360566891346476073, 360566905752312161⟩, ⟨751969820124575336, 752437079290470682⟩, true⟩

def state01 : KState := ⟨⟨360563226607785091, 360563241019842505⟩, ⟨927831604156009026, 928299161977023798⟩, true⟩

def words00 : List Nat := [360582581198760462, 360582581073947188, 360582580515509563, 360582579741044953, 360582578966500498, 360582578083639943, 360582577545135486, 360582577308104592, 360582577071012444, 360582576557480019]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 48000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 48000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360571676072524123, 360571690490821749⟩, ⟨522016265368989900, 522484122813115208⟩, true⟩

def words01 : List Nat := [360582576155283077, 360582576006704594, 360582575857949180, 360582575571883391, 360582574852441004, 360582573675799634, 360582572499080823, 360582571755046269, 360582571269042813, 360582571043150219]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 48010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 48000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360592529104059420, 360592543528648699⟩, ⟨(-479614110019829778), (-479145950419284610)⟩, true⟩

def words02 : List Nat := [360582570817159784, 360582570375299763, 360582569810546963, 360582569678340151, 360582569545957708, 360582569152988025, 360582568898052308, 360582568306717779, 360582567715281370, 360582567764029614]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 48020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 48000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360557574776949330, 360557589207759074⟩, ⟨1199563821665791733, 1200032280066627307⟩, true⟩

def words03 : List Nat := [360582568250250313, 360582568736578611, 360582568992960306, 360582569371891497, 360582569509479584, 360582569647234331, 360582569831289255, 360582569831950269, 360582569583020815, 360582569063713834]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 48030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 48000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360588600516353648, 360588614953415268⟩, ⟨(-291114651697686407), (-290645892926394359)⟩, true⟩

def words04 : List Nat := [360582568544288047, 360582568015030512, 360582567928164218, 360582568054377602, 360582568054987094, 360582567809557223, 360582567131092330, 360582566654011641, 360582566176736148, 360582566257385500]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 48040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 48000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360543850532108459, 360543864975466839⟩, ⟨1859442933187511995, 1859911994549302071⟩, true⟩

def words05 : List Nat := [360582566257981187, 360582566123526863, 360582566089011485, 360582566407980499, 360582566425705086, 360582566443527261, 360582566444116371, 360582566224357707, 360582565571774364, 360582564767280183]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 48050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 48000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360560753693455191, 360560768143050243⟩, ⟨1046918696535374281, 1047388057662534209⟩, true⟩

def words06 : List Nat := [360582563962595122, 360582563286016421, 360582562625042342, 360582561680841984, 360582560736573085, 360582559684190935, 360582558849630403, 360582558327208940, 360582557804752785, 360582556952238147]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 48060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 48000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360623900413419133, 360623914869253422⟩, ⟨(-1988910214669714606), (-1988440553591209220)⟩, true⟩

def words07 : List Nat := [360582556499510093, 360582556340938344, 360582556454320164, 360582556698453751, 360582556699064346, 360582556575675579, 360582556661555449, 360582557091174978, 360582557951896630, 360582558812732318]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 48070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 48000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581045933638669, 360581060395782014⟩, ⟨71559952583175373, 72029917032015293⟩, true⟩

def words08 : List Nat := [360582559336107986, 360582559635195827, 360582559924181915, 360582560213340631, 360582560293494563, 360582560294156344, 360582559942225038, 360582559302341157, 360582558662358372, 360582558210650636]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 48080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 48000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360531407671998670, 360531422140373394⟩, ⟨2459047724761258290, 2459517988908438372⟩, true⟩

def words09 : List Nat := [360582558579989615, 360582558980588543, 360582559003446930, 360582559004108929, 360582558706553076, 360582558301103571, 360582557895479488, 360582557480159983, 360582556632893852, 360582555570496231]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 48090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 48000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 48000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk480
