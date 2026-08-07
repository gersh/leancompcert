import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk130

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360452044177288302, 360452045120082208⟩, ⟨1668509983672524579, 1668518285362006587⟩, true⟩

def state01 : KState := ⟨⟨360765735440904556, 360765736385211194⟩, ⟨(-2410976792304303016), (-2410968470941647828)⟩, true⟩

def words00 : List Nat := [360580382808494707, 360580379276684993, 360580385614467010, 360580391951304866, 360580392591615826, 360580393508635470, 360580400317461479, 360580407125287291, 360580419823097432, 360580434066331658]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 13000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 13000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360646658444329197, 360646659390166116⟩, ⟨(-861436346910582975), (-861428005631499287)⟩, true⟩

def words01 : List Nat := [360580445339588771, 360580456611130767, 360580463468681999, 360580473417374507, 360580480274500742, 360580487130599253, 360580491022781943, 360580492402705929, 360580497484785872, 360580502566140965]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 13010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 13000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360620380303281580, 360620381250630313⟩, ⟨(-519100555578303399), (-519092194607729729)⟩, true⟩

def words02 : List Nat := [360580510619925387, 360580516962313618, 360580520266127151, 360580523569450700, 360580525253967605, 360580530814116903, 360580536152561795, 360580541490215614, 360580543016035301, 360580546073390828]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 13020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 13000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360799395319943052, 360799396268809350⟩, ⟨(-2852385386634541198), (-2852377005882612316)⟩, true⟩

def words03 : List Nat := [360580553071145612, 360580560067874813, 360580572930367141, 360580587655701021, 360580596560736141, 360580605464416869, 360580620230378787, 360580638924705993, 360580655700707171, 360580672474170702]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 13030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 13000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360813355626869054, 360813356577270463⟩, ⟨(-3035379076290369379), (-3035370675513076613)⟩, true⟩

def words04 : List Nat := [360580684430833423, 360580690552783920, 360580702533728375, 360580714512882693, 360580724945687833, 360580734739897892, 360580741583969028, 360580748427011429, 360580761123023041, 360580778945248927]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 13040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 13000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360603908368370310, 360603909320287693⟩, ⟨(-300654013760464043), (-300645593191858347)⟩, true⟩

def words05 : List Nat := [360580800018295525, 360580821088144541, 360580838387770330, 360580852264269483, 360580862057812839, 360580871849896600, 360580882444647295, 360580887220796156, 360580888983735784, 360580890746427204]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 13050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 13000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360735680534296483, 360735681487738033⟩, ⟨(-2021910763654641944), (-2021902323173069796)⟩, true⟩

def words06 : List Nat := [360580895581368098, 360580904978844603, 360580920215969932, 360580935450793648, 360580945471838385, 360580952119309182, 360580962663398737, 360580973205924408, 360580983528644412, 360580995364015819]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 13060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 13000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360649672667681110, 360649673622658946⟩, ⟨(-897165144199096540), (-897156683630528098)⟩, true⟩

def words07 : List Nat := [360581004261259370, 360581013157159729, 360581023892266386, 360581037584810787, 360581049686047034, 360581061785461280, 360581070883326169, 360581078417539600, 360581083661953074, 360581088905616631]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 13070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 13000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360692896946291005, 360692897902791531⟩, ⟨(-1463154331317429451), (-1463145850824480779)⟩, true⟩

def words08 : List Nat := [360581097957645155, 360581103922235140, 360581105259610135, 360581106596795862, 360581106596931130, 360581109187978817, 360581114452852372, 360581119716951998, 360581122054581598, 360581130593126534]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 13080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 13000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360732179214143774, 360732180172167916⟩, ⟨(-1978020927678445401), (-1978012427233652947)⟩, true⟩

def words09 : List Nat := [360581137653368198, 360581144712577442, 360581157580681201, 360581164667883784, 360581166382651796, 360581168097169212, 360581169606397806, 360581175329726393, 360581186856944515, 360581198382439373]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 13090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 13000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 13000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk130
