import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk234A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360652249958031828, 360652253180759632⟩, ⟨(-1663903426764074343), (-1663852406927291023)⟩, true⟩

def state01 : KState := ⟨⟨360598621540095815, 360598624765691397⟩, ⟨(-408939750869780026), (-408888663912581304)⟩, true⟩

def words00 : List Nat := [360581154391086167, 360581155554722691, 360581155564690407, 360581155574690156, 360581155574945103, 360581155005542055, 360581156543366846, 360581158081126067, 360581158355128342, 360581159101520171]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 23400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 23400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360644072044724942, 360644075273191585⟩, ⟨(-1473236832971094056), (-1473185678787669166)⟩, true⟩

def words01 : List Nat := [360581160865084898, 360581162628587586, 360581164919816980, 360581166405740386, 360581166406025789, 360581166088736114, 360581167273188121, 360581169696865826, 360581172383090650, 360581175069153002]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 23410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 23400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360663089042195567, 360663092273566538⟩, ⟨(-1918924138660738822), (-1918872916444041208)⟩, true⟩

def words02 : List Nat := [360581176552713689, 360581178204283884, 360581181010640213, 360581183816845698, 360581186133254063, 360581189020330118, 360581190752237708, 360581192484027548, 360581194154717815, 360581197650356089]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 23420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 23400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360569932590020041, 360569935824258725⟩, ⟨264476293916988884, 264527583338476056⟩, true⟩

def words03 : List Nat := [360581202962569974, 360581208274388833, 360581212560150737, 360581215038784656, 360581216722969716, 360581218407100617, 360581220912674295, 360581221611602554, 360581221611875429, 360581221130715145]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 23430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 23400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360630783898426681, 360630787135545458⟩, ⟨(-1162484044681389551), (-1162432687736186301)⟩, true⟩

def words04 : List Nat := [360581220649528967, 360581221126550697, 360581221126802326, 360581221029381608, 360581220931948003, 360581219279084741, 360581216877962020, 360581216291969723, 360581216444915685, 360581218559035451]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 23440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 23400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk234A
