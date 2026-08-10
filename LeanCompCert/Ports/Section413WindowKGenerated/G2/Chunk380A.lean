import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk380A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360677778409329996, 360677787266766900⟩, ⟨(-3647626327237879130), (-3647398815309118142)⟩, true⟩

def state01 : KState := ⟨⟨360624511115569931, 360624519977891782⟩, ⟨(-1623513622163234258), (-1623285924582422380)⟩, true⟩

def words00 : List Nat := [360581807731437208, 360581809160979531, 360581810398868627, 360581811636835432, 360581812425772279, 360581812817713480, 360581812818174729, 360581812750287448, 360581813165285053, 360581814289417856]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 38000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 38000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360565117981273296, 360565126848425351⟩, ⟨634538692475477732, 634766573676714272⟩, true⟩

def words01 : List Nat := [360581816104316068, 360581817919220949, 360581819387180394, 360581820371697695, 360581821181381535, 360581821991168003, 360581822780977694, 360581822882935444, 360581822883394411, 360581822444787180]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 38010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 38000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360586961585091310, 360586970457084177⟩, ⟨(-195955762584914734), (-195727697311959978)⟩, true⟩

def words02 : List Nat := [360581822118346167, 360581822576031175, 360581823489822734, 360581824403673342, 360581824725762337, 360581824726275506, 360581824360654930, 360581824095219845, 360581823829649643, 360581823926692866]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 38020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 38000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360626789227622759, 360626798104509885⟩, ⟨(-1710974335239696982), (-1710746083814000134)⟩, true⟩

def words03 : List Nat := [360581823927157889, 360581823531564068, 360581823237797666, 360581823689981418, 360581823967840360, 360581824245768720, 360581824246226308, 360581824626714380, 360581825809397589, 360581826992188601]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 38030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 38000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360635909797328678, 360635918679046698⟩, ⟨(-2057975094171006520), (-2057746658953513792)⟩, true⟩

def words04 : List Nat := [360581828708008383, 360581830115776655, 360581831164157281, 360581832212534320, 360581832786069168, 360581833855225600, 360581835613666329, 360581837372113613, 360581838608634103, 360581840030418449]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 38040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 38000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk380A
