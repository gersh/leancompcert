import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk671

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

def state06 : KState := ⟨⟨360624384581239618, 360624413556088035⟩, ⟨(-2786511031416465021), (-2785196559382318741)⟩, true⟩

def words05 : List Nat := [360582940173377069, 360582940427789474, 360582940903218457, 360582941157489513, 360582941177118315, 360582941196814003, 360582941437609967, 360582941874305182, 360582942492577282, 360582943111047278]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 67150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 67100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360618956277511041, 360618985261379680⟩, ⟨(-2422086176914629104), (-2420771099037822656)⟩, true⟩

def words06 : List Nat := [360582943595142694, 360582943858041171, 360582944268854397, 360582944679934202, 360582944907635622, 360582945189926039, 360582945316820377, 360582945443804156, 360582945791799930, 360582946329414430]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 67160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 67100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360569048061090314, 360569077053899112⟩, ⟨930579500335517382, 931895178768519038⟩, true⟩

def words07 : List Nat := [360582946932149710, 360582947535061484, 360582948027259991, 360582948298307444, 360582948511691184, 360582948725329607, 360582948910583808, 360582948911532085, 360582948875641455, 360582948670135619]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 67170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 67100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360617684933895928, 360617713935656077⟩, ⟨(-2337105889494999828), (-2335789609664765914)⟩, true⟩

def words08 : List Nat := [360582948479065624, 360582948605986345, 360582948807572848, 360582949009342949, 360582949023048972, 360582949043163361, 360582949284165826, 360582949525446373, 360582949987514708, 360582950505886246]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 67180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 67100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578640943821104, 360578669954624844⟩, ⟨286499050650451605, 287815938165213415⟩, true⟩

def words09 : List Nat := [360582950913602411, 360582951321410415, 360582951652077284, 360582952093987363, 360582952443207317, 360582952792571579, 360582953002655400, 360582953003603902, 360582952992529066, 360582952929895160]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 67190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 67100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 67100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk671
