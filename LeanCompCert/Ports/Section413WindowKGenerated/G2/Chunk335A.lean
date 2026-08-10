import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk335A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588297465378691, 360588304278249510⟩, ⟨(-237883553034211325), (-237729237998143719)⟩, true⟩

def state01 : KState := ⟨⟨360591036842791427, 360591043659931242⟩, ⟨(-329755385228945510), (-329600927159701400)⟩, true⟩

def words00 : List Nat := [360581208095312664, 360581207741832549, 360581207972659852, 360581208532983249, 360581208867304553, 360581209076248874, 360581209076653136, 360581208647295898, 360581208217885012, 360581208055886013]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 33500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 33500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360517666657864464, 360517673479223549⟩, ⟨2129347233664814961, 2129501833142691525⟩, true⟩

def words01 : List Nat := [360581208323410284, 360581208591003453, 360581208591402647, 360581208412576988, 360581207983938180, 360581207330039187, 360581206676036455, 360581206114003022, 360581204665046569, 360581202770188427]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 33510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 33500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360569326078450035, 360569332904044579⟩, ⟨397433740968729043, 397588482439909815⟩, true⟩

def words02 : List Nat := [360581200875342203, 360581199868914884, 360581199461190183, 360581199027715857, 360581198594235170, 360581197373500700, 360581195266087434, 360581193414139103, 360581191562166990, 360581190598122716]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 33520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 33500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360553202768339211, 360553209598200840⟩, ⟨938224881609811163, 938379766177208073⟩, true⟩

def words03 : List Nat := [360581190244888266, 360581189446141786, 360581188735767537, 360581189385471356, 360581189594443130, 360581189803474721, 360581189803881006, 360581189328502662, 360581188361698794, 360581187528021270]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 33530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 33500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360572863223349670, 360572870057430591⟩, ⟨278558570932474475, 278713597036359099⟩, true⟩

def words04 : List Nat := [360581186694243732, 360581186148796044, 360581185103698602, 360581183611885027, 360581182120079702, 360581180403546916, 360581179133760237, 360581178750890926, 360581178367995708, 360581177467178322]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 33540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 33500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk335A
