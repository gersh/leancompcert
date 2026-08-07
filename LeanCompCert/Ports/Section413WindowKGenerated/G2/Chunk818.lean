import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk818

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360603881693134781, 360603925351470571⟩, ⟨(-1773027916428929691), (-1770616038523206895)⟩, true⟩

def state01 : KState := ⟨⟨360582223195111089, 360582266864632893⟩, ⟨(-1250323704776844), 1162469270054450⟩, true⟩

def words00 : List Nat := [360582280114707527, 360582280289925480, 360582280588173119, 360582280886761053, 360582281147540201, 360582281259432772, 360582281260484675, 360582281233463097, 360582281206240465, 360582281074011576]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 81800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 81800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360577651756841906, 360577695437393860⟩, ⟨372772013294410580, 375185708703222312⟩, true⟩

def words01 : List Nat := [360582281144610545, 360582281215604723, 360582281216649022, 360582281212825043, 360582281143598229, 360582281037255968, 360582280972167922, 360582280992377163, 360582280993431304, 360582280938600206]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 81810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 81800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360584852551867293, 360584896243499676⟩, ⟨(-216438398262749151), (-214023796198796217)⟩, true⟩

def words02 : List Nat := [360582280883507303, 360582280967872635, 360582281053366811, 360582281139066944, 360582281140149340, 360582281099672378, 360582280947166646, 360582280897654142, 360582280847793453, 360582280806853432]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 81820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 81800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360584656149879116, 360584699852677010⟩, ⟨(-200416488764227306), (-198000972973192622)⟩, true⟩

def words03 : List Nat := [360582280807897901, 360582280766253042, 360582280724386718, 360582280749502799, 360582280750488654, 360582280730428690, 360582280710270073, 360582280573721399, 360582280484602126, 360582280515511370]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 81830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 81800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360591122762826165, 360591166476654045⟩, ⟨(-729700193010758712), (-727283774469094942)⟩, true⟩

def words04 : List Nat := [360582280664287958, 360582280699402441, 360582280700447058, 360582280660831589, 360582280621004701, 360582280544096035, 360582280687716909, 360582280834805126, 360582280907027496, 360582281016800542]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 81840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 81800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360598354603010579, 360598398327918349⟩, ⟨(-1321755815405415566), (-1319338489919657358)⟩, true⟩

def words05 : List Nat := [360582281050176323, 360582281083875258, 360582281266362660, 360582281300177533, 360582281301272201, 360582281191852504, 360582281082212248, 360582281118242003, 360582281316077522, 360582281514174080]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 81850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 81800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594246468237127, 360594290204305767⟩, ⟨(-985529266197726682), (-983111027026945750)⟩, true⟩

def words06 : List Nat := [360582281617831960, 360582281727089390, 360582281943842441, 360582282160947707, 360582282275114479, 360582282276287260, 360582282241637386, 360582282114100549, 360582282006717387, 360582282154727444]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 81860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 81800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360567841339327817, 360567885086462267⟩, ⟨1176436319991228144, 1178855465173822408⟩, true⟩

def words07 : List Nat := [360582282312613534, 360582282470741808, 360582282514193161, 360582282568794458, 360582282573785393, 360582282579085983, 360582282671590358, 360582282672763306, 360582282616544516, 360582282441923599]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 81870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 81800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360596416911704325, 360596460669910950⟩, ⟨(-1163458141103966214), (-1161038089276031986)⟩, true⟩

def words08 : List Nat := [360582282267039676, 360582282178755161, 360582282299178929, 360582282434608322, 360582282437751262, 360582282444591875, 360582282495527737, 360582282546802266, 360582282648309576, 360582282822659408]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 81880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 81800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360581703973246347, 360581747742652668⟩, ⟨41436649486000485, 43857618509476901⟩, true⟩

def words09 : List Nat := [360582282917963058, 360582283013381635, 360582283104619685, 360582283270977421, 360582283339867420, 360582283408941512, 360582283409986838, 360582283404421054, 360582283249866271, 360582283244710171]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 81890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 81800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 81800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk818
