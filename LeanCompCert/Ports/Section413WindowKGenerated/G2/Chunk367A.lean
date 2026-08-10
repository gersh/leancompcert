import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk367A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360551050681352811, 360551058919673477⟩, ⟨1123066726228627553, 1123271111708986321⟩, true⟩

def state01 : KState := ⟨⟨360546473496034204, 360546481739022633⟩, ⟨1291007535671753959, 1291212092481646209⟩, true⟩

def words00 : List Nat := [360581664928409563, 360581664013332821, 360581663474417989, 360581663097579201, 360581662720721595, 360581661717519150, 360581659973635783, 360581658083985493, 360581656194282274, 360581655045818647]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 36700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 36700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360560655383357721, 360560663631052758⟩, ⟨770297131720235003, 770501861332743763⟩, true⟩

def words01 : List Nat := [360581654088149117, 360581652761245829, 360581651434317923, 360581650848511257, 360581650730256159, 360581650104610203, 360581649478944162, 360581648479154455, 360581647368093257, 360581646797211058]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 36710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 36700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360575881450508320, 360575889702861678⟩, ⟨211257495605202360, 211462396294583104⟩, true⟩

def words02 : List Nat := [360581646395379619, 360581646824723440, 360581646880008766, 360581646935345253, 360581646935761182, 360581646592875476, 360581646926810832, 360581647260821882, 360581647261276866, 360581646914849007]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 36720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 36700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360613643707688027, 360613651964706856⟩, ⟨(-1176055866932678069), (-1175850794857467799)⟩, true⟩

def words03 : List Nat := [360581646943168059, 360581647128361146, 360581647880958047, 360581647894155522, 360581647894611495, 360581647284979516, 360581646675278421, 360581646443912395, 360581647315447698, 360581648187050901]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 36730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 36700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580123208664441, 360580131470393149⟩, ⟨55284672862517482, 55489918001502644⟩, true⟩

def words04 : List Nat := [360581648568264201, 360581648568758713, 360581648210705934, 360581647604327874, 360581646997851965, 360581646202980376, 360581645101880032, 360581643621438104, 360581642140982052, 360581641400134687]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 36740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 36700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk367A
