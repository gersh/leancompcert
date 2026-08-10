import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk918A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360565713528577658, 360565769007690186⟩, ⟨1483489826030348891, 1486928969802062009⟩, true⟩

def state01 : KState := ⟨⟨360568972103477160, 360569027595080666⟩, ⟨1184319704523552712, 1187759995028829726⟩, true⟩

def words00 : List Nat := [360581966315652760, 360581966259043230, 360581966106734121, 360581965884544442, 360581965662162805, 360581965343436125, 360581965122337529, 360581965019989112, 360581964917506316, 360581964747842118]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 91800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 91800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360573152956922442, 360573208461073028⟩, ⟨800521473565670086, 803962916081583696⟩, true⟩

def words01 : List Nat := [360581964608004225, 360581964587065070, 360581964661761981, 360581964695334855, 360581964696559003, 360581964629206075, 360581964561608456, 360581964457853392, 360581964413434670, 360581964319448999]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 91810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 91800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580723444419896, 360580778961202930⟩, ⟨105268982313919159, 108711584804502091⟩, true⟩

def words02 : List Nat := [360581964225273759, 360581964064659271, 360581963833604528, 360581963721407148, 360581963608861339, 360581963466127520, 360581963328412526, 360581963118596960, 360581962908522438, 360581962796385382]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 91820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 91800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574241094244102, 360574296623550721⟩, ⟨700630365207149538, 704074117801446614⟩, true⟩

def words03 : List Nat := [360581962866671978, 360581962950109127, 360581962951312458, 360581962949505630, 360581962950616627, 360581962928265138, 360581963000105984, 360581963016692901, 360581963017885475, 360581962935809013]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 91830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 91800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360596946954327382, 360597002496160085⟩, ⟨(-1384781407060342098), (-1381336504008652668)⟩, true⟩

def words04 : List Nat := [360581962888351856, 360581962984089148, 360581963143376238, 360581963302913558, 360581963358582189, 360581963362077846, 360581963363169767, 360581963364144227, 360581963447370979, 360581963612489699]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 91840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 91800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk918A
