import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk183A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360682528764351688, 360682530692666497⟩, ⟨(-1793474626494340064), (-1793450741008467516)⟩, true⟩

def state01 : KState := ⟨⟨360674970703004747, 360674972633513806⟩, ⟨(-1655175827479406257), (-1655151901827514009)⟩, true⟩

def words00 : List Nat := [360584541607963240, 360584546977542166, 360584550847636552, 360584554717336171, 360584556520191985, 360584559830888652, 360584566117845947, 360584572404161234, 360584576570911740, 360584581507861056]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 18300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 18300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360720383910128931, 360720385842841571⟩, ⟨(-2486774415578156018), (-2486750449567729598)⟩, true⟩

def words01 : List Nat := [360584589420166939, 360584597331680849, 360584608217882505, 360584616144177481, 360584620916089893, 360584625687496596, 360584631261616197, 360584638779273383, 360584646189239595, 360584653598446193]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 18310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 18300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360765418793928545, 360765420728863317⟩, ⟨(-3312667550721744264), (-3312643543991386094)⟩, true⟩

def words02 : List Nat := [360584659378008343, 360584662199665258, 360584667038353077, 360584671876582982, 360584675907703583, 360584682230551054, 360584686571432947, 360584690911866782, 360584698222104728, 360584708081217723]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 18320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 18300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360630378615629497, 360630380552764717⟩, ⟨(-836543025553579292), (-836518978477863744)⟩, true⟩

def words03 : List Nat := [360584719250783742, 360584730419175504, 360584739059575569, 360584745871598028, 360584751220733772, 360584756569347167, 360584762359947191, 360584766343331292, 360584768830682725, 360584771317800546]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 18330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 18300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360646126474433766, 360646128413773121⟩, ⟨(-1125318239962681083), (-1125294152452008603)⟩, true⟩

def words04 : List Nat := [360584776770756707, 360584783734010327, 360584789977470723, 360584796220293623, 360584799927316113, 360584800685372279, 360584801338489879, 360584801991602782, 360584804481517353, 360584807823480930]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 18340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 18300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk183A
