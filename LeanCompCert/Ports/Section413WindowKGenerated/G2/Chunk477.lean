import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk477

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360566770792444929, 360566785011420509⟩, ⟨758059153261170412, 758517471122372690⟩, true⟩

def state01 : KState := ⟨⟨360577075801190009, 360577090026343249⟩, ⟨266511244702332266, 266969857268553870⟩, true⟩

def words00 : List Nat := [360582686617155028, 360582686820624573, 360582686821209039, 360582686805928553, 360582686790551775, 360582686411325767, 360582686252253281, 360582686161179253, 360582686070045113, 360582685705598512]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 47700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 47700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360607638305154877, 360607652536508907⟩, ⟨(-1191727383300676680), (-1191268474863264010)⟩, true⟩

def words01 : List Nat := [360582685909503332, 360582686230882334, 360582686989959597, 360582687310630291, 360582687311235394, 360582687254900177, 360582687579327747, 360582688297251643, 360582688820932976, 360582689344730377]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 47710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 47700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590242361628718, 360590256599231332⟩, ⟨(-361673030055186747), (-361213823404915191)⟩, true⟩

def words02 : List Nat := [360582689649815876, 360582689650472369, 360582689769284309, 360582689893901834, 360582689894452729, 360582689768810101, 360582689661737516, 360582689332516733, 360582689003186269, 360582688900599313]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 47720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 47700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360561318497720334, 360561332741517310⟩, ⟨1019081833598245755, 1019541335935688653⟩, true⟩

def words03 : List Nat := [360582689348306005, 360582689796119559, 360582689903670312, 360582689904327502, 360582689785832461, 360582689558157183, 360582689539364873, 360582689540021534, 360582689311673452, 360582688865018268]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 47730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 47700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580958814266598, 360580973064253628⟩, ⟨81493146338607553, 81952944220093301⟩, true⟩

def words04 : List Nat := [360582688418216266, 360582688636904964, 360582689302687539, 360582689968567991, 360582690263523359, 360582690264180090, 360582690121133722, 360582689823047900, 360582689524783619, 360582689356279180]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 47740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 47700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk477
