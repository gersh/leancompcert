import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk291A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk291B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk291A

def state06 : KState := ⟨⟨360619428706200726, 360619433807884050⟩, ⟨(-1060101466875608713), (-1060000854925031491)⟩, true⟩

def words05 : List Nat := [360583066966361688, 360583068405391795, 360583071017608764, 360583074314991728, 360583076557832088, 360583078800575120, 360583080455903053, 360583081365173113, 360583082612141013, 360583083859153725]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 29150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 29100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360623957960689790, 360623963066007949⟩, ⟨(-1192239572611931060), (-1192138854650789410)⟩, true⟩

def words06 : List Nat := [360583085218633080, 360583086618552094, 360583087431647032, 360583088244728807, 360583088475881958, 360583089301426641, 360583091298983602, 360583093296477281, 360583094404153503, 360583095805555761]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 29160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 29100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360707961755260927, 360707966864221649⟩, ⟨(-3643157145895656545), (-3643056321663066499)⟩, true⟩

def words07 : List Nat := [360583097896122095, 360583099986663497, 360583103248645056, 360583105906282917, 360583107570141588, 360583109233922553, 360583111761791732, 360583114869896192, 360583119148892210, 360583123427682015]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 29170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 29100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360596023164036687, 360596028276678223⟩, ⟨(-376556756399122856), (-376455824742344526)⟩, true⟩

def words08 : List Nat := [360583126983656227, 360583129372146792, 360583131131422353, 360583132890683567, 360583133996552987, 360583133996939021, 360583133935633119, 360583133068525861, 360583132201405194, 360583131979026812]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 29180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 29100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360554017225292726, 360554022341568399⟩, ⟨850016473669017110, 850117511424779542⟩, true⟩

def words09 : List Nat := [360583133591638565, 360583135204213784, 360583136040455767, 360583136703096444, 360583137068831956, 360583137434648296, 360583137434966240, 360583137362837720, 360583136951648934, 360583135954973358]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 29190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 29100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 29100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk291B
