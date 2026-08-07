import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk227

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360672584952362144, 360672587976992092⟩, ⟨(-2096627971640900892), (-2096581518346623522)⟩, true⟩

def state01 : KState := ⟨⟨360611502823338458, 360611505850771154⟩, ⟨(-710242373095990958), (-710195856165490076)⟩, true⟩

def words00 : List Nat := [360580234072431877, 360580234591276412, 360580236457508097, 360580238323663319, 360580239216265788, 360580239216559863, 360580238182283544, 360580235965292536, 360580233748435769, 360580234843058351]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 22700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 22700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360529314235607226, 360529317265809245⟩, ⟨1156715778739669611, 1156762358575486541⟩, true⟩

def words01 : List Nat := [360580236785173641, 360580238727173680, 360580239517434841, 360580239517729146, 360580239258196000, 360580237064701046, 360580234871310521, 360580234611048801, 360580233342734135, 360580231102014152]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 22710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 22700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360622938119475159, 360622941152460733⟩, ⟨(-970612328868584967), (-970565685776603147)⟩, true⟩

def words02 : List Nat := [360580228861425138, 360580229780235041, 360580232131314837, 360580234482246042, 360580235104101701, 360580235451088822, 360580237729214503, 360580240007225554, 360580241385953879, 360580243264740149]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 22720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 22700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360607681310154584, 360607684345943599⟩, ⟨(-623721128512334519), (-623674421684141299)⟩, true⟩

def words03 : List Nat := [360580244172060184, 360580245079332476, 360580247388861427, 360580250704710857, 360580253526253066, 360580256347600330, 360580257546005851, 360580257546300472, 360580258029790825, 360580259236155809]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 22730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 22700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360632207217909947, 360632210256479088⟩, ⟨(-1181689412730995861), (-1181642642669339211)⟩, true⟩

def words04 : List Nat := [360580262371104128, 360580264226529658, 360580264535957951, 360580264845383653, 360580264845630428, 360580265925550183, 360580267580128190, 360580269234618527, 360580269920225726, 360580272203528918]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 22740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 22700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360663672466323161, 360663675507671573⟩, ⟨(-1897559989118144830), (-1897513155813851054)⟩, true⟩

def words05 : List Nat := [360580276413550400, 360580280623290707, 360580286113796235, 360580290530741746, 360580293019640069, 360580295508342469, 360580297930818510, 360580301318637507, 360580304982067092, 360580308645239613]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 22750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 22700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360613883332053354, 360613886376214361⟩, ⟨(-764591606864763194), (-764544709532507184)⟩, true⟩

def words06 : List Nat := [360580311328712312, 360580313245180143, 360580314634843955, 360580316024475399, 360580316453445178, 360580316453740194, 360580314967149445, 360580312514473302, 360580310061956415, 360580311008003369]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 22760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 22700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360574826973036334, 360574830019977916⟩, ⟨124838971948173409, 124885932608244781⟩, true⟩

def words07 : List Nat := [360580312417823054, 360580313827571087, 360580314271916231, 360580314272211388, 360580313559413257, 360580312327403597, 360580311785539670, 360580312522264592, 360580312522530004, 360580312282164407]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 22770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 22700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360624628033999632, 360624631083726473⟩, ⟨(-1009980502936838935), (-1009933478814790529)⟩, true⟩

def words08 : List Nat := [360580312041754761, 360580311451073272, 360580313558637566, 360580315666073145, 360580316060803638, 360580316061098829, 360580314948079283, 360580315352330347, 360580316319102520, 360580318263805681]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 22780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 22700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360547351516151654, 360547354568694220⟩, ⟨751700827314210014, 751747915620455240⟩, true⟩

def words09 : List Nat := [360580319049607091, 360580319835378815, 360580321483303791, 360580324381752246, 360580326324212026, 360580328266549473, 360580328795569975, 360580328795865358, 360580327414342112, 360580325968502135]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 22790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 22700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 22700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk227
