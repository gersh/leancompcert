import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk322A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360506963502978367, 360506969776667167⟩, ⟨2411236009477221351, 2411372609933300661⟩, true⟩

def state01 : KState := ⟨⟨360524049392633215, 360524055670368430⟩, ⟨1861064816879832665, 1861201547650977421⟩, true⟩

def words00 : List Nat := [360581854799528463, 360581852761199951, 360581851201864691, 360581850602911467, 360581850003962797, 360581848636601696, 360581846306496213, 360581843684068391, 360581841061675101, 360581839015529901]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 32200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 32200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360500573509774000, 360500579791598683⟩, ⟨2617498648577690770, 2617635511090537734⟩, true⟩

def words01 : List Nat := [360581837222015053, 360581834939388656, 360581832656822049, 360581831334157545, 360581830839084493, 360581829756509840, 360581828673955617, 360581827110832976, 360581824879751285, 360581822358671636]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 32210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 32200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360460284613266496, 360460290899138785⟩, ⟨3915626630917882855, 3915763623864792725⟩, true⟩

def words02 : List Nat := [360581819837608135, 360581817291815288, 360581813784505853, 360581809677771744, 360581805571221993, 360581801209695341, 360581797474327828, 360581793568295867, 360581789662455650, 360581785271582620]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 32220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 32200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360534775280679044, 360534781570601510⟩, ⟨1514358192859322711, 1514495316363392171⟩, true⟩

def words03 : List Nat := [360581781502441814, 360581778467365778, 360581775432351252, 360581773356140236, 360581770675236941, 360581767080550413, 360581763486004852, 360581760850135057, 360581758688438830, 360581757231779035]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 32230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 32200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360505740141891408, 360505746435908879⟩, ⟨2450509702040593908, 2450646957587611882⟩, true⟩

def words04 : List Nat := [360581755775148027, 360581753578734199, 360581751548647587, 360581749939707505, 360581748330753754, 360581746480474635, 360581744204651153, 360581741444779731, 360581738685003962, 360581735488857333]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 32240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 32200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk322A
