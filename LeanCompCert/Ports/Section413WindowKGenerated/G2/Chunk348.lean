import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk348

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360569624019485650, 360569631394630641⟩, ⟨425005373394009882, 425178892544666636⟩, true⟩

def state01 : KState := ⟨⟨360564721836933939, 360564729216468476⟩, ⟨595482834505331528, 595656506434543738⟩, true⟩

def words00 : List Nat := [360581848828202352, 360581848714299059, 360581847777913889, 360581846421229777, 360581845064536242, 360581843499632614, 360581842349002449, 360581842023147465, 360581841697259369, 360581840865604775]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 34800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 34800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360615246212702061, 360615253596646533⟩, ⟨(-1163710887727075460), (-1163537062265858574)⟩, true⟩

def words01 : List Nat := [360581840374429805, 360581839859630464, 360581839344719687, 360581839324404343, 360581839176199362, 360581838206673183, 360581837237112349, 360581836867498065, 360581837827574690, 360581838787701763]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 34810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 34800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360601331579779082, 360601338968170648⟩, ⟨(-679340789489262221), (-679166809158992333)⟩, true⟩

def words02 : List Nat := [360581839258447958, 360581839362859191, 360581840039560316, 360581840716359248, 360581840837964942, 360581840840276967, 360581840840695637, 360581840245613828, 360581839650477162, 360581840050276847]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 34820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 34800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360518576905204943, 360518584297997817⟩, ⟨2203593993758545837, 2203768127408662221⟩, true⟩

def words03 : List Nat := [360581841167114700, 360581842283985805, 360581842835745745, 360581842836212703, 360581842567075032, 360581842090710594, 360581841614239347, 360581841256373011, 360581840077741575, 360581838262619191]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 34830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 34800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360652474542588023, 360652481939788758⟩, ⟨(-2462144297403123603), (-2461970010161552297)⟩, true⟩

def words04 : List Nat := [360581836447493098, 360581835455368230, 360581835120203168, 360581835364258401, 360581835364689492, 360581834811356802, 360581835170811649, 360581835762117375, 360581837175740586, 360581839203277280]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 34840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 34800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360613359374718022, 360613366776371482⟩, ⟨(-1098792087035305831), (-1098617644594282899)⟩, true⟩

def words05 : List Nat := [360581840815943998, 360581842428569287, 360581843690398141, 360581845514887901, 360581847132301664, 360581848749698960, 360581849949429556, 360581850735270570, 360581851639725537, 360581852544289951]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 34850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 34800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585423672002087, 360585431078055370⟩, ⟨(-124869845728470736), (-124695249887611734)⟩, true⟩

def words06 : List Nat := [360581854026840866, 360581854689701057, 360581854938282899, 360581855186901633, 360581855187293533, 360581855425545635, 360581855470309814, 360581855515154061, 360581855515570517, 360581855176879964]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 34860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 34800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360668462732254295, 360668470142714735⟩, ⟨(-3020831534759466240), (-3020656785218955952)⟩, true⟩

def words07 : List Nat := [360581856101256877, 360581857025717652, 360581858457924884, 360581860150903987, 360581861164608807, 360581862178287404, 360581864012992158, 360581866260282726, 360581868743572038, 360581871226823019]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 34870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 34800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360642385124437956, 360642392539357242⟩, ⟨(-2111371616500665671), (-2111196711414222441)⟩, true⟩

def words08 : List Nat := [360581872919987342, 360581874044823066, 360581875990371293, 360581877935952566, 360581879674834785, 360581880595044187, 360581881008676363, 360581881422343899, 360581882458244779, 360581884193038300]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 34880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 34800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360570641264090817, 360570648683412763⟩, ⟨392153249641069112, 392328308358492748⟩, true⟩

def words09 : List Nat := [360581885819518028, 360581887445998634, 360581888661197393, 360581889321716358, 360581889411519783, 360581889501435174, 360581890411489017, 360581890503433203, 360581890503849998, 360581890182219597]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 34890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 34800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 34800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk348
