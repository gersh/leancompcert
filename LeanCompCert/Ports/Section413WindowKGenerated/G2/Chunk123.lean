import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk123

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360651985712688910, 360651986552356494⟩, ⟨(-867032373794602432), (-867025377008116096)⟩, true⟩

def state01 : KState := ⟨⟨360629251296153959, 360629252137243782⟩, ⟨(-587294886495282956), (-587287872207988700)⟩, true⟩

def words00 : List Nat := [360581514703043768, 360581520432520340, 360581522767159869, 360581525101435138, 360581525101561897, 360581527258355777, 360581534537535723, 360581541815561984, 360581543942756951, 360581547818162636]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 12300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 12300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360684271344177071, 360684272186696822⟩, ⟨(-1265268649729073419), (-1265261617832179031)⟩, true⟩

def words01 : List Nat := [360581553519408127, 360581559219772919, 360581564749685927, 360581566592317717, 360581566592457178, 360581562724951634, 360581559769421983, 360581564043071873, 360581572379894436, 360581580715401296]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 12310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 12300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360617852510736026, 360617853354697579⟩, ⟨(-447302004015529299), (-447294954348537269)⟩, true⟩

def words02 : List Nat := [360581584851044103, 360581585460801370, 360581592604002011, 360581599746088215, 360581602126844934, 360581602126996329, 360581597980013321, 360581588606047940, 360581579233574219, 360581579333584244]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 12320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 12300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360453892683903209, 360453893529291003⟩, ⟨1575210167284300348, 1575217234544206998⟩, true⟩

def words03 : List Nat := [360581579629414654, 360581579925224839, 360581579925359892, 360581576944263227, 360581574261237843, 360581569924942216, 360581565589306193, 360581562192788203, 360581555190090918, 360581544844894262]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 12330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 12300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360604885279022601, 360604886125844588⟩, ⟨(-289121042074906193), (-289113957110196289)⟩, true⟩

def words04 : List Nat := [360581534501342388, 360581521114245473, 360581513625261817, 360581512652878171, 360581511680640261, 360581505036816817, 360581491889588292, 360581485257400648, 360581478626238859, 360581477984227699]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 12340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 12300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360505914160107625, 360505915008373452⟩, ⟨933633236192663074, 933640338996069070⟩, true⟩

def words05 : List Nat := [360581477984363130, 360581475636744307, 360581473289477592, 360581474905569889, 360581474905699231, 360581473233056692, 360581471560669632, 360581466534800266, 360581458364378038, 360581452252628798]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 12350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 12300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360543544195883094, 360543545045582201⟩, ⟨468437320498774900, 468444441024696544⟩, true⟩

def words06 : List Nat := [360581446141818764, 360581444070091078, 360581442279743366, 360581436319918455, 360581430361031959, 360581422753743297, 360581418958665115, 360581419211024634, 360581419211162827, 360581414442593090]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 12360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 12300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360767509278089843, 360767510129224863⟩, ⟨(-2303391358502316402), (-2303384220207065618)⟩, true⟩

def words07 : List Nat := [360581412667750007, 360581413953885840, 360581421720986233, 360581426906759594, 360581426906902201, 360581425665321264, 360581429660656057, 360581438215202620, 360581453245367410, 360581468273138355]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 12370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 12300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360686174787977116, 360686175640564065⟩, ⟨(-1296807667039563028), (-1296800510762295532)⟩, true⟩

def words08 : List Nat := [360581480042403810, 360581488662412396, 360581494518715733, 360581500374116873, 360581504589258446, 360581508067502821, 360581508295421131, 360581508523319516, 360581510546702449, 360581518993742800]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 12380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 12300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360410323113001621, 360410323967022580⟩, ⟨2123013556528836030, 2123020730580796322⟩, true⟩

def words09 : List Nat := [360581533902371664, 360581548808623516, 360581559204268734, 360581563154775459, 360581563488289897, 360581563821790441, 360581563821917010, 360581559693635496, 360581549124585467, 360581535316262967]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 12390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 12300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 12300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk123
