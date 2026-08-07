import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk699

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360560087993329504, 360560119480609127⟩, ⟨1569492635046705930, 1570979308658887212⟩, true⟩

def state01 : KState := ⟨⟨360550540823852043, 360550572320466011⟩, ⟨2236864878645715378, 2238352204775504952⟩, true⟩

def words00 : List Nat := [360582593828114594, 360582593482907011, 360582593143428023, 360582592700663305, 360582592257753824, 360582591643273386, 360582591151863326, 360582590803119342, 360582590454292819, 360582589946052845]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 69900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 69900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360587101290511247, 360587132796470789⟩, ⟨(-319265192551980427), (-317777213027303947)⟩, true⟩

def words01 : List Nat := [360582589488876267, 360582589236069558, 360582588982969500, 360582588894980392, 360582588747708384, 360582588412619086, 360582588077325828, 360582587908253309, 360582587926834890, 360582587992863471]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 69910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 69900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360560448753828645, 360560480269241447⟩, ⟨1544238535417971933, 1545727175959206215⟩, true⟩

def words02 : List Nat := [360582587993756339, 360582587916758746, 360582587635297943, 360582587343560947, 360582587051570910, 360582586708122744, 360582586160308389, 360582585435534043, 360582584710590840, 360582584189961585]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 69920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 69900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360542649242197965, 360542680766933003⟩, ⟨2789110184968537385, 2790599477460247917⟩, true⟩

def words03 : List Nat := [360582583874680351, 360582583763524384, 360582583652263715, 360582583439126832, 360582583076730777, 360582582633718343, 360582582190440955, 360582581687303534, 360582581243139734, 360582580673673928]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 69930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 69900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360568375358653058, 360568406892730513⟩, ⟨989744491326368651, 991234437273894165⟩, true⟩

def words04 : List Nat := [360582580103995173, 360582579738502880, 360582579475744971, 360582579309498014, 360582579143161700, 360582578802567232, 360582578345141544, 360582578054985501, 360582577764541273, 360582577506558589]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 69940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 69900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360573309837031117, 360573341380556155⟩, ⟨644466569647036910, 645957176499497566⟩, true⟩

def words05 : List Nat := [360582577304877411, 360582576944061375, 360582576583069864, 360582576282344804, 360582576100276786, 360582575795581860, 360582575490796809, 360582575082157768, 360582574747198064, 360582574616355176]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 69950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 69900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360558531894611294, 360558563447456008⟩, ⟨1678385176469639587, 1679876435373263583⟩, true⟩

def words06 : List Nat := [360582574485811615, 360582574486802317, 360582574284250591, 360582573979914021, 360582573675439122, 360582573229116690, 360582572932393848, 360582572648703201, 360582572364912837, 360582571971614552]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 69960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 69900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360552277508024911, 360552309070238021⟩, ⟨2116059037981855224, 2117550952436859022⟩, true⟩

def words07 : List Nat := [360582571629300077, 360582571319568264, 360582571009532387, 360582570861822497, 360582570584073953, 360582570130905011, 360582569677561809, 360582569221819575, 360582568875045893, 360582568443665242]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 69970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 69900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360550616564482620, 360550648136129434⟩, ⟨2232249123042871992, 2233741697716426376⟩, true⟩

def words08 : List Nat := [360582568012154169, 360582567478917756, 360582566915939015, 360582566491941247, 360582566067681756, 360582565592396013, 360582565122802380, 360582564521773501, 360582563920575423, 360582563291118953]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 69980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 69900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360535467402754303, 360535498983749457⟩, ⟨3292658543057464593, 3294151772067183613⟩, true⟩

def words09 : List Nat := [360582562835931005, 360582562584537943, 360582562333069292, 360582561882546092, 360582561283190922, 360582560632931661, 360582559982397849, 360582559535626639, 360582558966019272, 360582558294778989]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 69990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 69900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 69900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk699
