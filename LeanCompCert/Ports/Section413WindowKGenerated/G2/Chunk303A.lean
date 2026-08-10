import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk303A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360572670298562440, 360572675825214481⟩, ⟨326093568045873796, 326206816004082682⟩, true⟩

def state01 : KState := ⟨⟨360572009522212602, 360572015052655438⟩, ⟨345954454907804850, 346067817745950584⟩, true⟩

def words00 : List Nat := [360583441832790349, 360583441833192417, 360583441509125773, 360583440210010563, 360583438910918886, 360583436682014536, 360583434999452125, 360583434402158688, 360583433804860904, 360583432664590310]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 30300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 30300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360614497263190022, 360614502797428992⟩, ⟨(-942137129914708635), (-942023651997142181)⟩, true⟩

def words01 : List Nat := [360583432288234445, 360583432276798404, 360583433337961912, 360583433920221647, 360583433920592779, 360583433543089010, 360583433165534437, 360583432449792091, 360583433415350485, 360583434440448776]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 30310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 30300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581948484267738, 360581954022342727⟩, ⟨44695677667274190, 44809271911664438⟩, true⟩

def words02 : List Nat := [360583434923939481, 360583434924341885, 360583434810753968, 360583435296260660, 360583435490379434, 360583435490781935, 360583435021347695, 360583433714793434, 360583432408248960, 360583431413437738]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 30320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 30300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360554826570071089, 360554832111939008⟩, ⟨867366714330670361, 867480423634043831⟩, true⟩

def words03 : List Nat := [360583431365060108, 360583431264730370, 360583431164363443, 360583430521912631, 360583429326074085, 360583427855045712, 360583426383997163, 360583425415234699, 360583425025712872, 360583424083713367]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 30330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 30300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360591231194098850, 360591236739767081⟩, ⟨(-237161692291542865), (-237047867667946097)⟩, true⟩

def words04 : List Nat := [360583423282027218, 360583424113035351, 360583425412529289, 360583426712013830, 360583426881393635, 360583426881796283, 360583426141443079, 360583426312675357, 360583426313003540, 360583426523706064]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 30340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 30300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk303A
