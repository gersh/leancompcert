import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk740A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360587052086291921, 360587087535775849⟩, ⟨(-350168587710836218), (-348396750674912176)⟩, true⟩

def state01 : KState := ⟨⟨360563100102083829, 360563135561589121⟩, ⟨1422300966539771663, 1424073545206651117⟩, true⟩

def words00 : List Nat := [360582379536139331, 360582379471895651, 360582379274915552, 360582379195850885, 360582379116491697, 360582378922511977, 360582378546002234, 360582378078750891, 360582377611306797, 360582377198465309]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 74000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 74000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360550877599682338, 360550913069107253⟩, ⟨2326911585946771662, 2328684898815868354⟩, true⟩

def words01 : List Nat := [360582376939347647, 360582376634360063, 360582376329266150, 360582375933183866, 360582375452221978, 360582374904172037, 360582374355817298, 360582373989918478, 360582373705135482, 360582373281196093]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 74010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 74000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590445118285810, 360590480597644036⟩, ⟨(-602076191968888157), (-600302143789833819)⟩, true⟩

def words02 : List Nat := [360582372857029719, 360582372615396322, 360582372502059599, 360582372514103517, 360582372515101972, 360582372357216738, 360582372016787808, 360582371858855368, 360582371700617517, 360582371803439044]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 74020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 74000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360564159665334797, 360564195154726733⟩, ⟨1344031922938551290, 1345806713962080986⟩, true⟩

def words03 : List Nat := [360582371822833900, 360582371842361239, 360582371997758775, 360582372246358522, 360582372344807180, 360582372443418194, 360582372444358993, 360582372388910642, 360582372150972621, 360582371906671116]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 74030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 74000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360557324519173161, 360557360018479336⟩, ⟨1850045894961842049, 1851821420084811971⟩, true⟩

def words04 : List Nat := [360582371662032681, 360582371396173660, 360582370947923103, 360582370388117570, 360582369828155730, 360582369184706401, 360582368708365003, 360582368414315310, 360582368120153825, 360582367735158402]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 74040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 74000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk740A
