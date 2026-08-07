import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk649

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360523387948041737, 360523414931822832⟩, ⟨3862957072348192984, 3864140060676914438⟩, true⟩

def state01 : KState := ⟨⟨360566024682234490, 360566051674639966⟩, ⟨1095667453127495970, 1096851001221266388⟩, true⟩

def words00 : List Nat := [360582953923650936, 360582953244258533, 360582952715236320, 360582952327505383, 360582951939697273, 360582951350205954, 360582950800520110, 360582950411305486, 360582950021828022, 360582949702697604]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 64900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 64900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360577611536907602, 360577638538022296⟩, ⟨343436300518386732, 344620413971915288⟩, true⟩

def words01 : List Nat := [360582949443205697, 360582948965322930, 360582948487279918, 360582948203664053, 360582948057576916, 360582947852222253, 360582947646781818, 360582947322518695, 360582947004669742, 360582946923942998]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 64910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 64900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594964644335085, 360594991654060255⟩, ⟨(-783196210965976367), (-782011538477348393)⟩, true⟩

def words02 : List Nat := [360582946997952729, 360582947243006149, 360582947291434558, 360582947339957187, 360582947340737084, 360582947213032855, 360582947431994622, 360582947660393584, 360582947735995292, 360582947922430104]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 64920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 64900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360599900409421757, 360599927427790765⟩, ⟨(-1103734330902297852), (-1102549097127017958)⟩, true⟩

def words03 : List Nat := [360582948236137488, 360582948550120310, 360582948901292678, 360582949016176655, 360582949017033105, 360582948909671804, 360582948930555845, 360582949198874080, 360582949461071237, 360582949723457186]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 64930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 64900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360608178997644549, 360608206024723486⟩, ⟨(-1641515097210610462), (-1640329297769456314)⟩, true⟩

def words04 : List Nat := [360582949866968539, 360582949906787321, 360582950123138136, 360582950339767178, 360582950452901901, 360582950572716138, 360582950573723690, 360582950574835357, 360582950761203869, 360582951151083828]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 64940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 64900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360571579347713121, 360571606383414268⟩, ⟨735915737386549584, 737102096884273850⟩, true⟩

def words05 : List Nat := [360582951777212733, 360582952403498838, 360582952847089707, 360582953132034459, 360582953260489828, 360582953389178502, 360582953598310959, 360582953599225789, 360582953572167954, 360582953398452512]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 64950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 64900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595038658220069, 360595065702552900⟩, ⟨(-788171666538443709), (-786984746284123395)⟩, true⟩

def words06 : List Nat := [360582953224523100, 360582953016923893, 360582953033635818, 360582953138103970, 360582953138948027, 360582953027291403, 360582952879155826, 360582952725490819, 360582952653332766, 360582952840717865]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 64960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 64900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360593154612133019, 360593181665193802⟩, ⟨(-665750498292714515), (-664563010943387061)⟩, true⟩

def words07 : List Nat := [360582952909175710, 360582952977724135, 360582953197003017, 360582953625711301, 360582953926307247, 360582954227041912, 360582954348813559, 360582954349728910, 360582954470987374, 360582954629430373]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 64970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 64900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360572311901300348, 360572338962987824⟩, ⟨688634312514425670, 689822360469837202⟩, true⟩

def words08 : List Nat := [360582954781835990, 360582954782751175, 360582954699132912, 360582954497093592, 360582954294911614, 360582953978784472, 360582953780971422, 360582953653370718, 360582953525661131, 360582953247654232]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 64980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 64900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360581152792616506, 360581179862944124⟩, ⟨114003410155449166, 115192019676196994⟩, true⟩

def words09 : List Nat := [360582953085077007, 360582953003549253, 360582953019974291, 360582953020889642, 360582952883954006, 360582952523570403, 360582952163022661, 360582952073426982, 360582952074173812, 360582952047862220]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 64990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 64900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 64900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk649
