import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk202A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360535818489210025, 360535820859735206⟩, ⟨936713526922351901, 936745932370018021⟩, true⟩

def state01 : KState := ⟨⟨360598696153545399, 360598698526517714⟩, ⟨(-333410372752329453), (-333377917860611559)⟩, true⟩

def words00 : List Nat := [360582192269586433, 360582194608048141, 360582198605267861, 360582202602141408, 360582204514859116, 360582204515118200, 360582203987498838, 360582203622992203, 360582203258449650, 360582203651555535]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 20200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 20200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360568197946684096, 360568200322124150⟩, ⟨282894099697423808, 282926604474527322⟩, true⟩

def words01 : List Nat := [360582203651786289, 360582203244839677, 360582202837884475, 360582201898228153, 360582201898446122, 360582200633161421, 360582199367968955, 360582196555152322, 360582193427545067, 360582192735797470]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 20210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 20200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360569747728899623, 360569750106784583⟩, ⟨251294758452921181, 251327312678288963⟩, true⟩

def words02 : List Nat := [360582193066106535, 360582193066365860, 360582191651890451, 360582188326660199, 360582185001716748, 360582181004819384, 360582178251477232, 360582177328646797, 360582176405879552, 360582173602220979]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 20220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 20200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360638556847786974, 360638559228118435⟩, ⟨(-1140954353645497981), (-1140921749915103637)⟩, true⟩

def words03 : List Nat := [360582174806835707, 360582176625431025, 360582180876037381, 360582183656371076, 360582184372309533, 360582185088197187, 360582185319475042, 360582186790762608, 360582189576172166, 360582192361367035]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 20230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 20200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360626160117318367, 360626162500122313⟩, ⟨(-890428598274845841), (-890395944489363975)⟩, true⟩

def words04 : List Nat := [360582193583196370, 360582193636326895, 360582195125619279, 360582196614844913, 360582197487353411, 360582197487613099, 360582196888276243, 360582194559289249, 360582192329725110, 360582194501283275]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 20240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 20200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk202A
