import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk787A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360552358805343013, 360552399095979085⟩, ⟨2346326464392093218, 2348468048602464302⟩, true⟩

def state01 : KState := ⟨⟨360587676384303211, 360587716685569847⟩, ⟨(-433395512913200087), (-431253092027014315)⟩, true⟩

def words00 : List Nat := [360582239480743944, 360582239098771970, 360582238819796393, 360582238673578032, 360582238527294070, 360582238224877970, 360582237941478418, 360582237819645932, 360582237697465725, 360582237742448467]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 78700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 78700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360579219934841115, 360579260246808251⟩, ⟨232273010310891579, 234416273487823895⟩, true⟩

def words01 : List Nat := [360582237743450192, 360582237733406027, 360582237873159593, 360582238105371694, 360582238201604236, 360582238298004384, 360582238299008411, 360582238296323025, 360582238132356514, 360582238095810892]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 78710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 78700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360574303638290767, 360574343960861854⟩, ⟨619376451043376850, 621520549017344872⟩, true⟩

def words02 : List Nat := [360582238182213403, 360582238311203246, 360582238358809243, 360582238406527238, 360582238407469920, 360582238431031573, 360582238431949368, 360582238431123265, 360582238430188260, 360582238290202860]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 78720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 78700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360600453864565236, 360600494197750314⟩, ⟨(-1439610491868165283), (-1437465558202702313)⟩, true⟩

def words03 : List Nat := [360582238216982068, 360582238244373200, 360582238374764318, 360582238375889043, 360582238345417113, 360582238176791727, 360582238007932575, 360582238114721838, 360582238347484073, 360582238580496245]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 78730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 78700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360571264256371774, 360571304600295283⟩, ⟨858811328620707124, 860957107881635736⟩, true⟩

def words04 : List Nat := [360582238712777263, 360582238713902134, 360582238685119334, 360582238651783413, 360582238618146849, 360582238544494655, 360582238309760365, 360582237994477457, 360582237678993286, 360582237388966796]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 78740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 78700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk787A
