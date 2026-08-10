import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk247A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360599759339381343, 360599762947445083⟩, ⟨(-398172781164560138), (-398112491581042686)⟩, true⟩

def state01 : KState := ⟨⟨360688498939668443, 360688502550778148⟩, ⟨(-2590703815382321033), (-2590643450548628571)⟩, true⟩

def words00 : List Nat := [360583646862424179, 360583649100277845, 360583651284126451, 360583653467855305, 360583654200034659, 360583654691530195, 360583656131434648, 360583657571316738, 360583660646329268, 360583664889390563]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 24700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 24700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360656538433246269, 360656542047425726⟩, ⟨(-1800792708255982394), (-1800732267553228496)⟩, true⟩

def words01 : List Nat := [360583668305516165, 360583671721400472, 360583675607019796, 360583680330896777, 360583684631296995, 360583688931401893, 360583691694677423, 360583693943412416, 360583696890603826, 360583699837662641]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 24710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 24700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360646720245532327, 360646723862749616⟩, ⟨(-1558121007024941149), (-1558060491211696301)⟩, true⟩

def words02 : List Nat := [360583703810382988, 360583706773287136, 360583708580743369, 360583710388091284, 360583711151115319, 360583712956651645, 360583715916596393, 360583718876365417, 360583721011982547, 360583723559841861]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 24720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 24700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360654885440148863, 360654889060418834⟩, ⟨(-1760115440524577515), (-1760054849203749577)⟩, true⟩

def words03 : List Nat := [360583726056081553, 360583728552212631, 360583732679334471, 360583735731379909, 360583737091965298, 360583738452465150, 360583740654935599, 360583744112603224, 360583746988572762, 360583749864379719]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 24730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 24700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360625148185417579, 360625151808763520⟩, ⟨(-1024645896423357146), (-1024585228988277018)⟩, true⟩

def words04 : List Nat := [360583751924471821, 360583752897680053, 360583755069123618, 360583757240485920, 360583758173285307, 360583758173608358, 360583757485975488, 360583755922723334, 360583754425399900, 360583756098328052]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 24740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 24700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk247A
