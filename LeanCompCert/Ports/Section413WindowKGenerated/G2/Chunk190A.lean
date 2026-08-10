import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk190A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360378316557496144, 360378318643263454⟩, ⟨3928551008876192379, 3928577831215354357⟩, true⟩

def state01 : KState := ⟨⟨360559005571864576, 360559007659921290⟩, ⟨494537707972353660, 494564573821762814⟩, true⟩

def words00 : List Nat := [360585075015819863, 360585066889604238, 360585060176135546, 360585055051519068, 360585049927426593, 360585042241620992, 360585035462580053, 360585030617960992, 360585025773776570, 360585023681689926]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 19000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 19000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360499255762066012, 360499257852435624⟩, ⟨1631024274443634792, 1631051184272921468⟩, true⟩

def words01 : List Nat := [360585022313434073, 360585019565922822, 360585016821918551, 360585018233900286, 360585018949119128, 360585019664302362, 360585019664520549, 360585018980810146, 360585016892291259, 360585012383680258]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 19010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 19000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360503892085003889, 360503894177660770⟩, ⟨1542496305149367944, 1542523258494087796⟩, true⟩

def words02 : List Nat := [360585007875463695, 360585004599976128, 360584998571418684, 360584990561486341, 360584982552356391, 360584973803129809, 360584967259020398, 360584962506772186, 360584957754996818, 360584951626872231]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 19020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 19000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360602568102514990, 360602570197467875⟩, ⟨(-335972595782857354), (-335945598733788734)⟩, true⟩

def words03 : List Nat := [360584947367836635, 360584945853837684, 360584944339929090, 360584942758164521, 360584939686069435, 360584934225824637, 360584928766107099, 360584926049858159, 360584925995597314, 360584926922496299]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 19030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 19000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360520716566188392, 360520718663455435⟩, ⟨1222404719575760034, 1222431760697896560⟩, true⟩

def words04 : List Nat := [360584926922714244, 360584925706431970, 360584921741752651, 360584919739576021, 360584917737543772, 360584914216530378, 360584908933460834, 360584901496626301, 360584894060526230, 360584888309686296]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 19040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 19000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk190A
