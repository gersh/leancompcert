import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk198

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362464862679047955, 362464867923307177⟩, ⟨402491685037955920, 402561913260529984⟩, true⟩

def state01 : KState := ⟨⟨362428930387249172, 362428935636979869⟩, ⟨1114154255531358113, 1114224592118026673⟩, true⟩

def words00 : List Nat := [371285199818842057, 371285199819456150, 371285197940437532, 371285195347120450, 371285192753837518, 371285190308405628, 371285186588859913, 371285184794637979, 371285183000386614, 371285181199429038]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 19800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 19800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362465494724930432, 362465499980202143⟩, ⟨389622301011867670, 389692747394861056⟩, true⟩

def words01 : List Nat := [371285178360741434, 371285176837320130, 371285176325297218, 371285176325911852, 371285173950593823, 371285171154373937, 371285168358189908, 371285166089593201, 371285162563270854, 371285161571897142]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 19810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 19800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362460831191200553, 362460836452020511⟩, ⟨482011994493546472, 482082550871018022⟩, true⟩

def words02 : List Nat := [371285160580399206, 371285159600357343, 371285157070046788, 371285156634783859, 371285156199244003, 371285156142559289, 371285153379217975, 371285150589793245, 371285147800406163, 371285147221101249]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 19820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 19800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362440359171594106, 362440364437968864⟩, ⟨888103421907771453, 888174088464396845⟩, true⟩

def words03 : List Nat := [371285145995628908, 371285145849646026, 371285145703468025, 371285145010994580, 371285141477350680, 371285138731150268, 371285135984907376, 371285135451488045, 371285133532911991, 371285131277105175]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 19830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 19800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362481616206880785, 362481621478757123⟩, ⟨69580758206392340, 69651533942865554⟩, true⟩

def words04 : List Nat := [371285129293071246, 371285129293749005, 371285129827724635, 371285131358942982, 371285132261425810, 371285132262041504, 371285129787950581, 371285129381856190, 371285130371516997, 371285130372154749]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 19840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 19800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362462075354968884, 362462080632454396⟩, ⟨457752812642789647, 457823699750191359⟩, true⟩

def words05 : List Nat := [371285130195855819, 371285129999273673, 371285132130214478, 371285133205806243, 371285134328544811, 371285135451411351, 371285136584237985, 371285136584853877, 371285134345368820, 371285133185311909]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 19850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 19800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362451591148885410, 362451596431855418⟩, ⟨666113433303143715, 666184429361416443⟩, true⟩

def words06 : List Nat := [371285133387069429, 371285133387685482, 371285131379220944, 371285129346563518, 371285127313867492, 371285125632041309, 371285123472458886, 371285123653959317, 371285123654420485, 371285123579785032]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 19860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 19800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362472816506284581, 362472821794844719⟩, ⟨244257999700003723, 244329106861586431⟩, true⟩

def words07 : List Nat := [371285122294352064, 371285122696453649, 371285123417367661, 371285123417985612, 371285121542203043, 371285119275580620, 371285117008946709, 371285115440567051, 371285112608907591, 371285111991366932]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 19870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 19800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362419598766819622, 362419604060947098⟩, ⟨1302284050055428411, 1302355267923760587⟩, true⟩

def words08 : List Nat := [371285111373644495, 371285110659797202, 371285106581395501, 371285104484580509, 371285102387679788, 371285100453217383, 371285095600166095, 371285090211622851, 371285084823359000, 371285081952748193]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 19880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 19800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362401453381003440, 362401458680675514⟩, ⟨1663612565655928416, 1663683893835076986⟩, true⟩

def words09 : List Nat := [371285078661332201, 371285077887055653, 371285077112655798, 371285076202222583, 371285073580273671, 371285071216452823, 371285068852546023, 371285068649618375, 371285065087035271, 371285060886395870]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 19890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 19800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 19800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk198
