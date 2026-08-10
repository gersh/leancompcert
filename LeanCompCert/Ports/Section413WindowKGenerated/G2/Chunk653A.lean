import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk653A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588760769102308, 360588788099972084⟩, ⟨(-383462826912828221), (-382257243059462065)⟩, true⟩

def state01 : KState := ⟨⟨360560013942989649, 360560041282629398⟩, ⟨1493678294794357498, 1494884451370591454⟩, true⟩

def words00 : List Nat := [360582934327602069, 360582934300747473, 360582934100789251, 360582933823477788, 360582933545922132, 360582933153202206, 360582932526562347, 360582931720264176, 360582930913813749, 360582930341753125]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 65300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 65300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360537896793167277, 360537924141470073⟩, ⟨2938333340492317796, 2939540062894975904⟩, true⟩

def words01 : List Nat := [360582929992034643, 360582929832309641, 360582929672493654, 360582929346316134, 360582928962914756, 360582928521096041, 360582928079035026, 360582927544535878, 360582926973732928, 360582926285727498]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 65310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 65300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360574110196733334, 360574137553721118⟩, ⟨572736021176849601, 573943310925233699⟩, true⟩

def words02 : List Nat := [360582925597533294, 360582925089400973, 360582924727368204, 360582924599461643, 360582924471476485, 360582924135091732, 360582923628718170, 360582923356531472, 360582923084088226, 360582922848546241]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 65320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 65300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360582221640901981, 360582249006677820⟩, ⟨42697480919074440, 43905344832144494⟩, true⟩

def words03 : List Nat := [360582922714917066, 360582922362577616, 360582922010072805, 360582921831603566, 360582921770097866, 360582921616507692, 360582921462822554, 360582921165015747, 360582920967911856, 360582920958695454]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 65330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 65300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360572785224571002, 360572812599004734⟩, ⟨659282976213833263, 660491405877603223⟩, true⟩

def words04 : List Nat := [360582921025928204, 360582921026849278, 360582920972286342, 360582920767175934, 360582920561935078, 360582920195244454, 360582919945409080, 360582919871405447, 360582919797308332, 360582919583027345]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 65340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 65300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk653A
