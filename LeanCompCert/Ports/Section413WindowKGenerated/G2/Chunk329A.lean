import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk329A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360599028503556672, 360599035064736977⟩, ⟨(-583096717447556636), (-582950758767803972)⟩, true⟩

def state01 : KState := ⟨⟨360548536514130065, 360548543079487989⟩, ⟨1078003844747703844, 1078149940892658798⟩, true⟩

def words00 : List Nat := [360581316735634073, 360581316565286862, 360581315473511867, 360581314649233641, 360581313824885055, 360581312767897590, 360581310789689079, 360581308098381677, 360581305407153008, 360581303636792537]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 32900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 32900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360537425399131676, 360537431968624870⟩, ⟨1443872461700554747, 1444018693957919893⟩, true⟩

def words01 : List Nat := [360581302641718928, 360581302567297465, 360581302492833191, 360581301796070905, 360581301129235996, 360581299996487170, 360581298863676468, 360581298651287765, 360581297781043085, 360581296449000263]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 32910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 32900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360524999455815169, 360525006029461881⟩, ⟨1852978223475500972, 1853124592486788768⟩, true⟩

def words02 : List Nat := [360581295116945264, 360581293760545414, 360581292994435544, 360581291996302820, 360581290998196916, 360581289213628664, 360581286836797298, 360581284863393783, 360581282889975847, 360581280690636700]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 32920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 32900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360539126022483135, 360539132600313975⟩, ⟨1387705496977938459, 1387852003793210461⟩, true⟩

def words03 : List Nat := [360581278982165948, 360581276810787304, 360581274639456537, 360581273387774628, 360581272836107073, 360581271645561904, 360581270455040475, 360581268803202392, 360581266605205612, 360581265326597922]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 32930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 32900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360572484813621283, 360572491395598409⟩, ⟨288818209687528596, 288964853101798252⟩, true⟩

def words04 : List Nat := [360581264047917373, 360581263728550576, 360581263728942233, 360581263248095831, 360581262767208988, 360581261666501680, 360581261481316680, 360581261695266787, 360581261695668894, 360581261193871605]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 32940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 32900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk329A
