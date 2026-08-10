import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk356A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360640203010928837, 360640210743466768⟩, ⟨(-2070943820408126873), (-2070757720469718753)⟩, true⟩

def state01 : KState := ⟨⟨360636014398786856, 360636022135880529⟩, ⟨(-1921864661000296689), (-1921678398854721739)⟩, true⟩

def words00 : List Nat := [360582046262039226, 360582047523876375, 360582049573395335, 360582051622944794, 360582053473584930, 360582054994567615, 360582055858059263, 360582056721549783, 360582057563618451, 360582059079553700]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 35600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 35600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360605201780853805, 360605209522449059⟩, ⟨(-824426985264545530), (-824240562795139286)⟩, true⟩

def words01 : List Nat := [360582061175136421, 360582063270693300, 360582064967861108, 360582065879832077, 360582066307789864, 360582066735858132, 360582067950918094, 360582069046981331, 360582069697055964, 360582070347164954]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 35610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 35600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360624942773311048, 360624950519423946⟩, ⟨(-1527646287150555470), (-1527459703740498918)⟩, true⟩

def words02 : List Nat := [360582071627899350, 360582073313042501, 360582074960668521, 360582076608286860, 360582077604879875, 360582078100012513, 360582078956443739, 360582079812966268, 360582080473909587, 360582081677580033]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 35620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 35600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360601149295238548, 360601157045908727⟩, ⟨(-679791032004170714), (-679604286196031108)⟩, true⟩

def words03 : List Nat := [360582082356733216, 360582083035897612, 360582083947507854, 360582085252302042, 360582086358683268, 360582087465080540, 360582087969183944, 360582087969662380, 360582088462688918, 360582088998261466]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 35630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 35600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360609215690886966, 360609223446060592⟩, ⟨(-967402694450009103), (-967215788116867789)⟩, true⟩

def words04 : List Nat := [360582089949604058, 360582090387397816, 360582090424860256, 360582090462382125, 360582090462782562, 360582090642654662, 360582091472418455, 360582092302227108, 360582092567916771, 360582093329426645]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 35640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 35600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk356A
