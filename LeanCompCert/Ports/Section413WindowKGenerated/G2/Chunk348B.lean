import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk348A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk348B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk348A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk348B
