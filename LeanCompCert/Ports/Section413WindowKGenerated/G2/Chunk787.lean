import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk787

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

def state06 : KState := ⟨⟨360549694976082974, 360549735330595128⟩, ⟨2557571249445128335, 2559717862615704107⟩, true⟩

def words05 : List Nat := [360582237251049166, 360582237227319640, 360582237203466467, 360582237099095116, 360582236958294403, 360582236740490345, 360582236522377552, 360582236300480374, 360582235968874803, 360582235557393195]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 78750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 78700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360553820392206499, 360553860757330816⟩, ⟨2232623799268034549, 2234771248305239185⟩, true⟩

def words06 : List Nat := [360582235145662088, 360582234725946107, 360582234386558526, 360582234167660263, 360582233948659877, 360582233581032266, 360582233052329410, 360582232526060466, 360582231999463107, 360582231599635060]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 78760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 78700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360562308904037691, 360562349279898950⟩, ⟨1563862616885582916, 1566010911722291952⟩, true⟩

def words07 : List Nat := [360582231240494334, 360582230738732416, 360582230236767898, 360582229828613127, 360582229517482021, 360582229113215300, 360582228708845191, 360582228223418986, 360582227811107856, 360582227560068058]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 78770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 78700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360574009519093000, 360574049905540162⟩, ⟨642038590442419149, 644187719291979559⟩, true⟩

def words08 : List Nat := [360582227308654652, 360582227218347546, 360582227103710392, 360582226908624067, 360582226713375662, 360582226407276717, 360582226183348266, 360582226120497323, 360582226057525343, 360582225914161713]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 78780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 78700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360572911418340670, 360572951815430673⟩, ⟨728533414876451515, 730683382326891149⟩, true⟩

def words09 : List Nat := [360582225868378649, 360582225926714869, 360582225927638219, 360582225869701747, 360582225650933032, 360582225272526607, 360582224893914252, 360582224676461022, 360582224563693912, 360582224447186091]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 78790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 78700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 78700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk787
