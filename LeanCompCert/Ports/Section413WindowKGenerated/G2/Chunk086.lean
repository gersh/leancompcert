import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk086

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360387832121884789, 360387832518090343⟩, ⟨1621023564189791992, 1621025874368653832⟩, true⟩

def state01 : KState := ⟨⟨360475510231890540, 360475510629073112⟩, ⟨865563826895660670, 865566145481621546⟩, true⟩

def words00 : List Nat := [360576301983868005, 360576271319481862, 360576248190313108, 360576224570733204, 360576200956615379, 360576173935980444, 360576143854400832, 360576105096634573, 360576066347852966, 360576040959558783]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 8600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 8600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360220283276368500, 360220283674516489⟩, ⟨3064922297967944949, 3064924624871070613⟩, true⟩

def words01 : List Nat := [360576029285001295, 360576026397916018, 360576023511491516, 360576009402669020, 360575988669219620, 360575964550228895, 360575940436807993, 360575915859213911, 360575884628682467, 360575843375777635]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 8610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 8600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360564829702935838, 360564830102052279⟩, ⟨93045229284503634, 93047564540562634⟩, true⟩

def words02 : List Nat := [360575802132420292, 360575767773840153, 360575740131987632, 360575725796417499, 360575711464161294, 360575684595891692, 360575653142186746, 360575634986438243, 360575616834868226, 360575611975116076]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 8620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 8600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360535022634976728, 360535023035073503⟩, ⟨350086560090925896, 350088903812183128⟩, true⟩

def words03 : List Nat := [360575610726006668, 360575598913102085, 360575587102914292, 360575585938123220, 360575585938209880, 360575579420516031, 360575572904319971, 360575559744815538, 360575547274313360, 360575542584125840]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 8630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 8600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360599029212064544, 360599029613130539⟩, ⟨(-203331638804017440), (-203329286703934278)⟩, true⟩

def words04 : List Nat := [360575546454637373, 360575549459291664, 360575549459383358, 360575543410277002, 360575537362555480, 360575519776300890, 360575518629096482, 360575524671361983, 360575524671454640, 360575526054385431]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 8640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 8600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360578586504532442, 360578586906572940⟩, ⟨(-26476505741246701), (-26474145206836719)⟩, true⟩

def words05 : List Nat := [360575535743932147, 360575545431270861, 360575559290908935, 360575559920544781, 360575559920639743, 360575548922921166, 360575537927724391, 360575529492683703, 360575529845818828, 360575530198894054]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 8650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 8600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360718368925778394, 360718369328801137⟩, ⟨(-1238759657565114992), (-1238757288519542950)⟩, true⟩

def words06 : List Nat := [360575530198985999, 360575523944235958, 360575511310579443, 360575511582852329, 360575511582938872, 360575508511331572, 360575506077692956, 360575496580047226, 360575490748692815, 360575507226561541]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 8660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 8600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360342095067539971, 360342095471537029⟩, ⟨2025417109598818393, 2025419487096565755⟩, true⟩

def words07 : List Nat := [360575518846752256, 360575530464282379, 360575531116478318, 360575531116581641, 360575518607893337, 360575502074256771, 360575485544400374, 360575482157310126, 360575465616271788, 360575438730419122]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 8670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 8600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360547403673031726, 360547404078004582⟩, ⟨242349188492737375, 242351574465314577⟩, true⟩

def words08 : List Nat := [360575411850735774, 360575398109257885, 360575391205217554, 360575389679404190, 360575388153934413, 360575375436961454, 360575356552798904, 360575330871357912, 360575305195798377, 360575292636631201]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 8680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 8600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360554370973278428, 360554371379236849⟩, ⟨181906315620177825, 181908710162132465⟩, true⟩

def words09 : List Nat := [360575289427822416, 360575279652834676, 360575273208641798, 360575287368115122, 360575294048466493, 360575300727298353, 360575300727391084, 360575298325629586, 360575282829878996, 360575280426381922]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 8690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 8600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 8600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk086
