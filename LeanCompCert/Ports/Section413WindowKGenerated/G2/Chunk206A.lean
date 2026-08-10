import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk206A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360634417349910172, 360634419819500136⟩, ⟨(-1082993136194517573), (-1082958709761280981)⟩, true⟩

def state01 : KState := ⟨⟨360524819666222544, 360524822138337049⟩, ⟨1174766335842795854, 1174800814293924454⟩, true⟩

def words00 : List Nat := [360581852314530954, 360581852314795502, 360581850718457248, 360581849464502397, 360581848210599802, 360581845627234554, 360581840693980909, 360581834584226485, 360581828475009747, 360581823633450777]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 20600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 20600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360499907426758530, 360499909901364077⟩, ⟨1688548099840120134, 1688582629644321784⟩, true⟩

def words01 : List Nat := [360581820868078811, 360581820446040225, 360581820024013664, 360581818426410570, 360581816527362225, 360581812785283229, 360581809043490127, 360581806853448848, 360581804397896189, 360581800426565063]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 20610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 20600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360541534180466429, 360541536657574274⟩, ⟨830124704325607144, 830159285739640362⟩, true⟩

def words02 : List Nat := [360581796455560024, 360581793239360078, 360581791805757727, 360581791711300849, 360581791616834204, 360581789208773810, 360581784455004265, 360581782040400645, 360581779625954688, 360581777049515120]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 20620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 20600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360563500565282474, 360563503044912281⟩, ⟨376697650290443531, 376732283745106539⟩, true⟩

def words03 : List Nat := [360581775099270568, 360581771425387042, 360581767751809143, 360581765604091516, 360581764864794514, 360581763534004155, 360581762203309662, 360581759682299303, 360581756462108640, 360581755578039467]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 20630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 20600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360567348919399555, 360567351401528342⟩, ⟨297079966630768622, 297114651676833884⟩, true⟩

def words04 : List Nat := [360581756145265706, 360581756145530721, 360581755254700835, 360581752533142305, 360581749811803033, 360581746500391920, 360581744789891461, 360581743423480076, 360581742057171817, 360581739520253613]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 20640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 20600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk206A
