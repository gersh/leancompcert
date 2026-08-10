import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk200A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360607149620393457, 360607151942165353⟩, ⟨(-502563668871387759), (-502532243370643307)⟩, true⟩

def state01 : KState := ⟨⟨360566276509542151, 360566278833754318⟩, ⟨314859777800267255, 314891252118174405⟩, true⟩

def words00 : List Nat := [360582026586492944, 360582026343909478, 360582024531154835, 360582024504517522, 360582024477815375, 360582023814719087, 360582023275213531, 360582021004112627, 360582018733191604, 360582015528013098]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 20000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 20000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360466670504365464, 360466672830995741⟩, ⟨2308740593600473682, 2308772116316973162⟩, true⟩

def words01 : List Nat := [360582016441558384, 360582018141384976, 360582018141617252, 360582017891070831, 360582015152877592, 360582011779945392, 360582008407272991, 360582006384090600, 360582001873947610, 360581996113529057]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 20010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 20000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360629756696680023, 360629759025728448⟩, ⟨(-956944932442332247), (-956913361302468209)⟩, true⟩

def words02 : List Nat := [360581990353620663, 360581987077719330, 360581986136810680, 360581986908072581, 360581986908311433, 360581985520840180, 360581984818075995, 360581984057678746, 360581985018408369, 360581987403677504]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 20020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 20000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360578908438922173, 360578910770414502⟩, ⟨61690932554646438, 61722552657886482⟩, true⟩

def words03 : List Nat := [360581987866564741, 360581988329432451, 360581988329641449, 360581990019845510, 360581991213587662, 360581992407252553, 360581992407481246, 360581992352161258, 360581990891518264, 360581990738112002]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 20030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 20000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360570016448139193, 360570018782053524⟩, ⟨239760716314158616, 239792384966441254⟩, true⟩

def words04 : List Nat := [360581990584640048, 360581990270661104, 360581989635365101, 360581987199835122, 360581984764506747, 360581981078157547, 360581979384109656, 360581979776007390, 360581979776236312, 360581978502001975]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 20040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 20000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk200A
