import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk142

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360492607830727274, 360492608964920979⟩, ⟨1258703854504586956, 1258714761090287460⟩, true⟩

def state01 : KState := ⟨⟨360552807575923969, 360552808711788115⟩, ⟨403280703173676622, 403291633487908358⟩, true⟩

def words00 : List Nat := [360581244607702204, 360581239061831652, 360581236118440349, 360581233005386471, 360581229892756990, 360581222525671611, 360581210229887771, 360581202863096234, 360581195497290881, 360581189544545885]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 14200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 14200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360510871888014976, 360510873025564096⟩, ⟨999536655404597083, 999547609670706685⟩, true⟩

def words01 : List Nat := [360581187547601786, 360581183047939433, 360581178548874740, 360581179187219624, 360581179916068784, 360581180644844196, 360581180645004524, 360581177605810781, 360581169643243383, 360581164699943190]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 14210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 14200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360530785052438209, 360530786191654245⟩, ⟨716385572271852370, 716396550249968068⟩, true⟩

def words02 : List Nat := [360581159757278423, 360581159731421155, 360581158475997570, 360581153420157393, 360581148364996504, 360581141883445276, 360581137908156398, 360581136554578898, 360581135201174498, 360581130292163730]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 14220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 14200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360596176242288811, 360596177383180200⟩, ⟨(-214860751293821843), (-214849749467184091)⟩, true⟩

def words03 : List Nat := [360581126754673711, 360581121318770659, 360581115883580127, 360581113290355121, 360581110052122522, 360581102653864934, 360581095256613188, 360581090047752931, 360581089619691541, 360581090679334460]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 14230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 14200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360554569691456531, 360554570834036679⟩, ⟨377099479860882759, 377110505743756689⟩, true⟩

def words04 : List Nat := [360581090679492594, 360581088639384171, 360581081695700109, 360581079653112067, 360581077610767858, 360581070652032153, 360581062302831484, 360581051478035507, 360581040654724430, 360581034729176592]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 14240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 14200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360416119957111652, 360416121101365658⟩, ⟨2351199178152804568, 2351210227896553480⟩, true⟩

def words05 : List Nat := [360581035911112979, 360581038949644754, 360581039512062665, 360581039512240196, 360581035178914211, 360581029613090547, 360581024047993041, 360581021554558334, 360581014167167795, 360581002604023201]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 14250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 14200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360495748407827921, 360495749553758209⟩, ⟨1215293981163266599, 1215305054819343333⟩, true⟩

def words06 : List Nat := [360580991042460799, 360580980900684958, 360580973246538634, 360580967142607345, 360580961039519446, 360580950750122315, 360580940670208355, 360580931291191357, 360580921913437528, 360580914589134477]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 14260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 14200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360493655616283984, 360493656763909918⟩, ⟨1244886223910763411, 1244897321771912601⟩, true⟩

def words07 : List Nat := [360580908621593746, 360580899411370111, 360580890202405766, 360580880833748077, 360580874825403493, 360580867410839830, 360580859997295505, 360580850122116177, 360580840552608565, 360580834447507391]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 14270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 14200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360434597814236481, 360434598963536488⟩, ⟨2088761404739337890, 2088772526514815120⟩, true⟩

def words08 : List Nat := [360580828343199153, 360580827109804751, 360580823434726315, 360580816669016179, 360580809904224485, 360580801916221753, 360580796397512004, 360580788579243779, 360580780762051213, 360580769189324789]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 14280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 14200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360569715841528582, 360569716992509182⟩, ⟨157255315340084319, 157266461139597303⟩, true⟩

def words09 : List Nat := [360580758961337705, 360580751550123068, 360580744139892147, 360580741593061714, 360580739240201579, 360580732678554350, 360580726117791763, 360580719537381823, 360580715416068491, 360580714647134329]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 14290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 14200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 14200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk142
