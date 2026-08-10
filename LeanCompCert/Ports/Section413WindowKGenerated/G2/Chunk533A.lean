import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk533A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360611946632076504, 360611964547118104⟩, ⟨(-1597965239960959313), (-1597320064555953943)⟩, true⟩

def state01 : KState := ⟨⟨360615497091170948, 360615515013243052⟩, ⟨(-1787397862533920292), (-1786752312366718570)⟩, true⟩

def words00 : List Nat := [360581996992416215, 360581997173339962, 360581997627028471, 360581998080916738, 360581998291519247, 360581998448499860, 360581998449164699, 360581998430409972, 360581998743175216, 360581999372711704]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 53300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 53300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360583974029870926, 360583991958920070⟩, ⟨(-106608926359593918), (-105963004211652278)⟩, true⟩

def words01 : List Nat := [360582000260580906, 360582001148573409, 360582001811146687, 360582002519988299, 360582003140485730, 360582003761163315, 360582004306833136, 360582004617056572, 360582004654998828, 360582004693035866]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 53310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 53300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360646937312022268, 360646955248052480⟩, ⟨(-3464101690322732342), (-3463455395909621968)⟩, true⟩

def words02 : List Nat := [360582004980888572, 360582005445749724, 360582006261351513, 360582007077064389, 360582007590357607, 360582008250250931, 360582009260896958, 360582010271727514, 360582011399622973, 360582012618139116]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 53320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 53300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360596309481599610, 360596327424684923⟩, ⟨(-763812021247379414), (-763165350550894738)⟩, true⟩

def words03 : List Nat := [360582013616867415, 360582014615638680, 360582015490966473, 360582016541708617, 360582017504110940, 360582018466598087, 360582019205088506, 360582019593105491, 360582019861948984, 360582020131035556]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 53330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 53300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593450385701477, 360593468335748456⟩, ⟨(-611354386560710297), (-610707344493803129)⟩, true⟩

def words04 : List Nat := [360582020607180796, 360582020827957924, 360582020873393665, 360582020918902424, 360582020919521996, 360582020943767768, 360582021070974249, 360582021198307333, 360582021198966645, 360582021364848308]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 53340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 53300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk533A
