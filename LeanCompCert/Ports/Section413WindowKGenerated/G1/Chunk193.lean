import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk193

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362399147779981032, 362399152751611597⟩, ⟨1671015260434574051, 1671080158407218843⟩, true⟩

def state01 : KState := ⟨⟨362476811447529797, 362476816424497736⟩, ⟨171849020110691963, 171914021122320049⟩, true⟩

def words00 : List Nat := [371285732730174024, 371285730915139963, 371285727755802809, 371285726868475623, 371285725981058392, 371285724492749169, 371285720860609765, 371285719442504021, 371285719273238961, 371285719273856738]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 19300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 19300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362481202064528613, 362481207046954672⟩, ⟨86976962576670263, 87042069010772079⟩, true⟩

def words01 : List Nat := [371285718813278738, 371285718027672230, 371285717242253318, 371285717242917748, 371285716218390659, 371285716021866531, 371285715825163135, 371285715461337539, 371285712562477084, 371285712330029764]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 19310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 19300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362414319872211109, 362414324859952097⟩, ⟨1379674503683637323, 1379739712830279791⟩, true⟩

def words02 : List Nat := [371285714390308040, 371285714390905532, 371285713124486416, 371285711839821703, 371285710555067819, 371285710059135789, 371285708222800672, 371285706611411373, 371285704999980516, 371285703013745697]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 19320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 19300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362519090576170464, 362519095569305412⟩, ⟨(-646086799751776600), (-646021486311939410)⟩, true⟩

def words03 : List Nat := [371285699321734571, 371285697379672083, 371285696157572793, 371285696158180876, 371285694656700529, 371285692709813642, 371285691054918468, 371285691055581105, 371285692182584567, 371285693910326459]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 19330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 19300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362455499695857752, 362455504694405510⟩, ⟨583935925214579545, 584001343365113949⟩, true⟩

def words04 : List Nat := [371285695103231627, 371285695103831043, 371285693562622125, 371285693340632612, 371285693514799296, 371285693515399154, 371285691192625389, 371285688880021306, 371285686567410975, 371285685642383036]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 19340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 19300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362394121618776952, 362394126622712539⟩, ⟨1772142040619452938, 1772207563051931310⟩, true⟩

def words05 : List Nat := [371285684576603939, 371285685070679979, 371285685575432792, 371285685576031257, 371285682533217119, 371285679661141740, 371285676789063087, 371285675666182003, 371285670997411639, 371285666269564395]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 19350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 19300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362421165559336664, 362421170568635836⟩, ⟨1248575270087865646, 1248640896386906556⟩, true⟩

def words06 : List Nat := [371285661541928551, 371285658756911079, 371285655026891134, 371285652676193930, 371285650325558703, 371285647530729122, 371285641901191150, 371285638620883561, 371285635340601326, 371285633185898971]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 19360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 19300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362431403414542684, 362431408429291434⟩, ⟨1050248465172657360, 1050314197057621810⟩, true⟩

def words07 : List Nat := [371285629858560120, 371285625940381915, 371285622022370355, 371285620754936798, 371285618153617894, 371285616254973605, 371285614356308799, 371285612449468325, 371285607004179977, 371285604208293376]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 19370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 19300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362445432623121243, 362445437643215380⟩, ⟨778385537502410004, 778451373008866330⟩, true⟩

def words08 : List Nat := [371285601412364945, 371285601265158916, 371285598736844830, 371285595785373366, 371285592833972325, 371285590701943832, 371285587267598287, 371285586480492174, 371285585693271001, 371285584697006451]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 19380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 19300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362452245210741990, 362452250236260984⟩, ⟨646318029083637216, 646383969805191512⟩, true⟩

def words09 : List Nat := [371285583202728101, 371285583779104606, 371285584919957060, 371285584920557069, 371285582527973009, 371285579707468880, 371285576887022938, 371285574370429936, 371285570714461992, 371285568997591149]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 19390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 19300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 19300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk193
