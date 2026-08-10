import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk615A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360586397069932268, 360586421196716395⟩, ⟨(-240084177938758160), (-239081799015075300)⟩, true⟩

def state01 : KState := ⟨⟨360597687618256775, 360597711753174338⟩, ⟨(-934512543330574911), (-933509664160957407)⟩, true⟩

def words00 : List Nat := [360582533855087087, 360582534057186249, 360582534072049544, 360582534087002005, 360582534087723403, 360582534186929830, 360582534603419707, 360582535020061329, 360582535201084268, 360582535448705854]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 61500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 61500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360633610677565425, 360633634820616781⟩, ⟨(-3144360348942561135), (-3143356969422523041)⟩, true⟩

def words01 : List Nat := [360582535960267465, 360582536472071862, 360582537191527433, 360582537647954708, 360582537877005045, 360582538106127058, 360582538541799129, 360582539109255748, 360582539940507293, 360582540771927350]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 61510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 61500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590929480460031, 360590953631737305⟩, ⟨(-518543221428321831), (-517539335809225259)⟩, true⟩

def words02 : List Nat := [360582541470482360, 360582542052941166, 360582542414520220, 360582542776330405, 360582542987462394, 360582542988324913, 360582542936439166, 360582542751992295, 360582542567389458, 360582542597692528]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 61520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 61500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360558631171648968, 360558655331041573⟩, ⟨1469017949131195839, 1470022334127439803⟩, true⟩

def words03 : List Nat := [360582542889034908, 360582543180532833, 360582543304299165, 360582543387080278, 360582543387802610, 360582543360552154, 360582543333061796, 360582543228880724, 360582542984058714, 360582542596789501]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 61530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 61500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360584457638405485, 360584481805942553⟩, ⟨(-120492976921048270), (-119488090674716126)⟩, true⟩

def words04 : List Nat := [360582542209336744, 360582541817446336, 360582541635065217, 360582541676337328, 360582541677138182, 360582541454623038, 360582540969089664, 360582540747657966, 360582540525979073, 360582540520006099]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 61540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 61500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk615A
