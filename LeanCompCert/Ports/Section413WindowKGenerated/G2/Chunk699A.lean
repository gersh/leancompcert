import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk699A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk699A
