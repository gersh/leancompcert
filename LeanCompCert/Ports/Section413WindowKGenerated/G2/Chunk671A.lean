import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk671A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360602582028932371, 360602610949966567⟩, ⟨(-1322088670511639827), (-1320777811020053569)⟩, true⟩

def state01 : KState := ⟨⟨360613834876684688, 360613863806743644⟩, ⟨(-2077260008320521945), (-2075948543221505957)⟩, true⟩

def words00 : List Nat := [360582927703708766, 360582927893618201, 360582928304936499, 360582928716530197, 360582929072235550, 360582929459918970, 360582929736704688, 360582930013587547, 360582930285424563, 360582930747435610]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 67100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 67100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360586748183126490, 360586777122105832⟩, ⟨(-259305132228947126), (-257993068438372824)⟩, true⟩

def words01 : List Nat := [360582931243621752, 360582931739969417, 360582932123817732, 360582932407064430, 360582932595595780, 360582932784393308, 360582933106588821, 360582933304540270, 360582933362656162, 360582933420902955]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 67110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 67100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360612936503614045, 360612965451546711⟩, ⟨(-2017224983110579096), (-2015912318330159710)⟩, true⟩

def words02 : List Nat := [360582933700414614, 360582934146801829, 360582934524449771, 360582934902254403, 360582935091302520, 360582935092250027, 360582935123422734, 360582935188189026, 360582935474109881, 360582935922441974]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 67120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 67100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590897804964925, 360590926761925960⟩, ⟨(-537679096305060717), (-536365825405256843)⟩, true⟩

def words03 : List Nat := [360582936258359106, 360582936594366226, 360582936855569334, 360582937256088762, 360582937555720325, 360582937855496887, 360582937975394695, 360582937976342443, 360582937993700600, 360582938113776465]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 67130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 67100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360603345517556759, 360603374483444245⟩, ⟨(-1373515292377818251), (-1372201422112419623)⟩, true⟩

def words04 : List Nat := [360582938454899523, 360582938654207954, 360582938742718540, 360582938831352918, 360582938832149925, 360582938904201266, 360582939178663685, 360582939453299401, 360582939613924430, 360582939919221636]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 67140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 67100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk671A
