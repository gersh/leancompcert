import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk372A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk372A
