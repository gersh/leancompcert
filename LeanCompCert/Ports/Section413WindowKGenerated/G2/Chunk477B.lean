import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk477A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk477B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk477A

def state06 : KState := ⟨⟨360563777691437578, 360563791947674894⟩, ⟨901952407986077731, 902412504350247641⟩, true⟩

def words05 : List Nat := [360582689320925622, 360582688947414551, 360582688573794711, 360582688283437479, 360582688283987212, 360582688200768695, 360582688117481939, 360582687816031113, 360582687076730823, 360582686681853082]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 47750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 47700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360573068604735271, 360573082867168622⟩, ⟨458107321070749559, 458567713388269083⟩, true⟩

def words06 : List Nat := [360582686286783349, 360582685881228176, 360582685636265087, 360582685090664232, 360582684544979350, 360582683781682960, 360582683291730592, 360582683053436345, 360582682815068953, 360582682358761427]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 47760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 47700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360580097001311234, 360580111269944221⟩, ⟨122137088597943868, 122597777102598694⟩, true⟩

def words07 : List Nat := [360582682158345859, 360582681954132297, 360582681749731874, 360582681441521825, 360582680695721774, 360582679549380775, 360582678402961957, 360582677693527345, 360582677203609695, 360582677150586804]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 47770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 47700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360558145020483846, 360558159295390495⟩, ⟨1171059123551888702, 1171520111842417180⟩, true⟩

def words08 : List Nat := [360582677097476772, 360582676822823729, 360582676617329881, 360582676672280922, 360582676672832153, 360582676518943042, 360582675927666943, 360582675026186435, 360582674124623937, 360582673212775773]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 47780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 47700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360531086400665277, 360531100681757539⟩, ⟨2464444086947284027, 2464905370879100743⟩, true⟩

def words09 : List Nat := [360582672700367251, 360582672624624471, 360582672548812514, 360582672226625396, 360582671704834172, 360582670874210679, 360582670043416875, 360582669649223778, 360582668817875812, 360582667739725722]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 47790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 47700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 47700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk477B
