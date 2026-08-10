import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk843A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360599509053822702, 360599555530109205⟩, ⟨(-1445235616812527343), (-1442589689420560541)⟩, true⟩

def state01 : KState := ⟨⟨360588725732564275, 360588772220262366⟩, ⟨(-536212237069101541), (-533565347622957927)⟩, true⟩

def words00 : List Nat := [360582443363004034, 360582443465474338, 360582443466568965, 360582443452721214, 360582443438673039, 360582443347781407, 360582443445974185, 360582443566083731, 360582443606180270, 360582443682495966]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 84300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 84300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360617332069986901, 360617378569111151⟩, ⟨(-2948211549674371089), (-2945563696833849887)⟩, true⟩

def words01 : List Nat := [360582443851925430, 360582444021718622, 360582444331669460, 360582444501372107, 360582444527991274, 360582444554676791, 360582444721650883, 360582444996779901, 360582445412056131, 360582445827601517]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 84310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 84300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360615084480662278, 360615130991338131⟩, ⟨(-2758731685815719114), (-2756082858887304398)⟩, true⟩

def words02 : List Nat := [360582446167523295, 360582446556035977, 360582446955996409, 360582447356301786, 360582447719850123, 360582448062197111, 360582448334017218, 360582448605963166, 360582448873747082, 360582449262686896]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 84320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 84300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574234965967148, 360574281488040608⟩, ⟨686374194204175254, 689023982351018378⟩, true⟩

def words03 : List Nat := [360582449688394471, 360582450114320361, 360582450469744545, 360582450716399800, 360582450903847681, 360582451091635355, 360582451206700090, 360582451207910936, 360582451182685232, 360582451087072515]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 84330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 84300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360592005937387745, 360592052470910950⟩, ⟨(-812607856050591724), (-809957102176862910)⟩, true⟩

def words04 : List Nat := [360582450991190978, 360582450890047970, 360582450859015864, 360582450824554633, 360582450789994379, 360582450635767421, 360582450369767448, 360582450244583438, 360582450132915815, 360582450248030642]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 84340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 84300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk843A
