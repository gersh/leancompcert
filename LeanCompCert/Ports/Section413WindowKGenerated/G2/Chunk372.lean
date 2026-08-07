import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk372

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360562312283234079, 360562320756964964⟩, ⟨713420900154333206, 713633984177522980⟩, true⟩

def state01 : KState := ⟨⟨360592418819573060, 360592427298022687⟩, ⟨(-406618795516220793), (-406405535932537283)⟩, true⟩

def words00 : List Nat := [360581504157194346, 360581504598983228, 360581504676427110, 360581504753921694, 360581504754348451, 360581504413173933, 360581504868868792, 360581505324634756, 360581505353512027, 360581505647544804]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 37200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 37200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360598509367719116, 360598517850906746⟩, ⟨(-633272931839886530), (-633059495931120426)⟩, true⟩

def words01 : List Nat := [360581506499100730, 360581507350767148, 360581507971778295, 360581508276252783, 360581508276719316, 360581507958295473, 360581508042204094, 360581508809001430, 360581509266402522, 360581509723883531]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 37210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 37200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360618244797347814, 360618253285310270⟩, ⟨(-1368152425654932432), (-1367938812003840478)⟩, true⟩

def words02 : List Nat := [360581509749605603, 360581509750107429, 360581509726509883, 360581510075644766, 360581510236438046, 360581510423836609, 360581510424283454, 360581510247764294, 360581510367412119, 360581511354875852]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 37220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 37200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360552886161260952, 360552894653954966⟩, ⟨1065549906972460523, 1065763696802873591⟩, true⟩

def words03 : List Nat := [360581512768331095, 360581514181808494, 360581515053239218, 360581515204901538, 360581515205324212, 360581514896368203, 360581514614895924, 360581514615397894, 360581514210792869, 360581513442805742]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 37230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 37200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360607117578407811, 360607126075836224⟩, ⟨(-954238775059711419), (-954024808896507495)⟩, true⟩

def words04 : List Nat := [360581512674736241, 360581512565066863, 360581513413240885, 360581514261465410, 360581514488549539, 360581514610860970, 360581514611275026, 360581514417840344, 360581514671050455, 360581515359106566]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 37240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 37200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360605110491716213, 360605118993929441⟩, ⟨(-879375182537424216), (-879161038116607506)⟩, true⟩

def words05 : List Nat := [360581515688095320, 360581516017117192, 360581517065939440, 360581518667051233, 360581520082245682, 360581521497446089, 360581522374454094, 360581523055368032, 360581523689053234, 360581524322876152]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 37250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 37200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360585123437906351, 360585131944852172⟩, ⟨(-134648309626324357), (-134433988845173627)⟩, true⟩

def words06 : List Nat := [360581524934630947, 360581525139601976, 360581525140049329, 360581524981974229, 360581524823824756, 360581524326527888, 360581524596547348, 360581525001861964, 360581525002313758, 360581525012147250]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 37260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 37200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360604087814514486, 360604096326199272⟩, ⟨(-841645024534399126), (-841430527108408760)⟩, true⟩

def words07 : List Nat := [360581525050647065, 360581525089289798, 360581525846957973, 360581525886748412, 360581525887220086, 360581525237287502, 360581524655987347, 360581525158471168, 360581525764329906, 360581526370267071]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 37270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 37200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360582295751009212, 360582304267484452⟩, ⟨(-29258612810892436), (-29043936773643034)⟩, true⟩

def words08 : List Nat := [360581526431931399, 360581526519696526, 360581526944445473, 360581527369320734, 360581527608550205, 360581527609052693, 360581527340619918, 360581526703487001, 360581526066299132, 360581525421736855]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 37280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 37200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360538805720037187, 360538814241243158⟩, ⟨1592825475562354462, 1593040328032508508⟩, true⟩

def words09 : List Nat := [360581525961227580, 360581526500785551, 360581526639065504, 360581526639568519, 360581526406405788, 360581525988216548, 360581525569890422, 360581525024155710, 360581524241742029, 360581523097222582]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 37290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 37200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 37200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk372
