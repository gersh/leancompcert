import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk153

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360529851708582261, 360529853034496263⟩, ⟨771174373477847668, 771188109364303824⟩, true⟩

def state01 : KState := ⟨⟨360523549925377583, 360523551253099350⟩, ⟨867419866028010379, 867433629582541691⟩, true⟩

def words00 : List Nat := [360580254192052439, 360580249327206718, 360580244613135758, 360580237750120294, 360580230887970563, 360580222934510030, 360580217138945983, 360580215595809060, 360580214052857423, 360580209230211208]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 15300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 15300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360715449531113516, 360715450860647413⟩, ⟨(-2071630690061698276), (-2071616898754620302)⟩, true⟩

def words01 : List Nat := [360580205529891332, 360580204542751267, 360580206816901726, 360580211299609757, 360580212151623037, 360580213003543389, 360580214415915290, 360580218997981620, 360580227825282138, 360580236651473429]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 15310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 15300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360639701256468060, 360639702587831953⟩, ⟨(-911538905094923013), (-911525085743288735)⟩, true⟩

def words02 : List Nat := [360580243331735589, 360580247606735173, 360580249683098029, 360580251759242020, 360580252651989569, 360580252652181645, 360580251149592226, 360580246810018379, 360580242470974223, 360580246251928015]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 15320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 15300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360579189638993777, 360579190972166862⟩, ⟨16952903878430437, 16966750974076839⟩, true⟩

def words03 : List Nat := [360580254370391377, 360580262487832372, 360580267955274995, 360580275610483218, 360580282172848394, 360580288734410461, 360580295022597313, 360580297090250401, 360580297090421647, 360580297018514586]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 15330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 15300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360661210315673685, 360661211650659763⟩, ⟨(-1241822679029153518), (-1241808804113181332)⟩, true⟩

def words04 : List Nat := [360580297302388769, 360580299797059753, 360580304971274219, 360580310144854154, 360580311388446688, 360580311388638952, 360580308416418366, 360580308219233582, 360580312054101506, 360580317324289287]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 15340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 15300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360652807399098999, 360652808735919935⟩, ⟨(-1113170354987553209), (-1113156451897199855)⟩, true⟩

def words05 : List Nat := [360580318619545821, 360580319914651639, 360580322390636497, 360580327057004809, 360580329548504085, 360580332039711354, 360580332398812485, 360580332893895363, 360580337612530513, 360580342330614474]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 15350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 15300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360615524242152323, 360615525580785681⟩, ⟨(-540391236706289172), (-540377305768001604)⟩, true⟩

def words06 : List Nat := [360580351271129639, 360580356003527879, 360580358503878202, 360580361003922592, 360580361004086565, 360580362766773794, 360580365201021696, 360580367634988964, 360580367655682668, 360580369943171473]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 15360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 15300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360671855279907110, 360671856620361734⟩, ⟨(-1406486241536071591), (-1406472282595989735)⟩, true⟩

def words07 : List Nat := [360580373962805940, 360580377981978697, 360580386217915231, 360580390249657471, 360580390397876574, 360580390546091411, 360580394909954667, 360580402540895438, 360580408487353853, 360580414433078984]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 15370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 15300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360625330895215026, 360625332237505617⟩, ⟨(-691123002790621541), (-691109015604427545)⟩, true⟩

def words08 : List Nat := [360580418266602194, 360580418266794905, 360580421744386842, 360580425589323974, 360580426886287955, 360580428662886749, 360580428663058769, 360580427550717347, 360580426438484833, 360580428786423529]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 15380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 15300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360521436517882174, 360521437861991541⟩, ⟨908741501555184822, 908755516741413144⟩, true⟩

def words09 : List Nat := [360580435913359754, 360580443039407673, 360580446912323176, 360580448449982328, 360580448898202250, 360580449346414687, 360580452665466407, 360580452665659347, 360580451792350214, 360580447960481244]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 15390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 15300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 15300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk153
