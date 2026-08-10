import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk384A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360611511222041789, 360611520274697261⟩, ⟨(-1130436420323468221), (-1130201450980091115)⟩, true⟩

def state01 : KState := ⟨⟨360633273035120475, 360633282092666074⟩, ⟨(-1966235320244664815), (-1966000163096117617)⟩, true⟩

def words00 : List Nat := [360582089578074901, 360582090744709175, 360582091420576169, 360582092096459241, 360582092600644875, 360582093552968049, 360582095052456654, 360582096551966519, 360582097500535152, 360582098833623193]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 38400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 38400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360674216123016872, 360674225185460557⟩, ⟨(-3539134807425277128), (-3538899462117462108)⟩, true⟩

def words01 : List Nat := [360582100633093182, 360582102432630473, 360582104749593974, 360582106393304770, 360582107472262490, 360582108551211623, 360582110022070028, 360582111921217998, 360582114319171888, 360582116717119872]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 38410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 38400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360613188478790142, 360613197546186928⟩, ⟨(-1194459326748617760), (-1194223791118917450)⟩, true⟩

def words02 : List Nat := [360582118760897078, 360582120131548294, 360582121149001537, 360582122166543698, 360582122821199267, 360582122821718380, 360582122803364707, 360582122445913899, 360582122245264184, 360582123054471415]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 38420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 38400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360556345012592537, 360556354084873224⟩, ⟨990546726300215064, 990782449643460172⟩, true⟩

def words03 : List Nat := [360582124538834564, 360582126023219878, 360582127061043293, 360582127996342267, 360582128760772049, 360582129525299393, 360582129864893448, 360582129865412701, 360582129532438775, 360582128862439392]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 38430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 38400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360611890608517029, 360611899685697499⟩, ⟨(-1144967205824443767), (-1144731294109174163)⟩, true⟩

def words04 : List Nat := [360582128192358955, 360582127723632212, 360582128036265653, 360582128386921228, 360582128387403089, 360582128067273767, 360582127310711341, 360582127229113931, 360582127739928921, 360582128514749821]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 38440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 38400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk384A
