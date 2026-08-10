import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk477A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk477A
