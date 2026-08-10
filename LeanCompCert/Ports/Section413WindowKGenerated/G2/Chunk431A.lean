import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk431A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360658158493787587, 360658170006006111⟩, ⟨(-3237115110081850611), (-3236779793045585743)⟩, true⟩

def state01 : KState := ⟨⟨360660035057575691, 360660046575393667⟩, ⟨(-3318125304945144446), (-3317789746544054652)⟩, true⟩

def words00 : List Nat := [360583073921593160, 360583075152310471, 360583076921210614, 360583078690200876, 360583080196611881, 360583081718474264, 360583082968854911, 360583084219244530, 360583085550673161, 360583087336532494]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 43100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 43100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360611425515526191, 360611437038886747⟩, ⟨(-1222274555933421922), (-1221938758563271164)⟩, true⟩

def words01 : List Nat := [360583089353961411, 360583091371409850, 360583092972422118, 360583094037842916, 360583094964074865, 360583095890419436, 360583097354527977, 360583098283158228, 360583098940894149, 360583099598693726]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 43110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 43100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591957188616773, 360591968717523958⟩, ⟨(-382661707059918367), (-382325670491484181)⟩, true⟩

def words02 : List Nat := [360583100227712830, 360583101126381306, 360583102309196217, 360583103492068427, 360583104173220992, 360583104319049751, 360583104319533667, 360583104309480950, 360583104299252074, 360583104428022405]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 43120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 43100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360593880302768151, 360593891837273778⟩, ⟨(-465600569899680598), (-465264291842650534)⟩, true⟩

def words03 : List Nat := [360583104428549927, 360583104228561378, 360583104365574963, 360583105138768448, 360583105772875301, 360583106407048762, 360583106771161749, 360583106771750097, 360583106850700425, 360583107101364953]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 43130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 43100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360597205243666327, 360597216783723459⟩, ⟨(-609068154471477367), (-608731636895639403)⟩, true⟩

def words04 : List Nat := [360583107337204908, 360583107722641761, 360583107823870864, 360583107925159527, 360583107925652001, 360583108243937701, 360583108752916867, 360583109261993931, 360583109445062789, 360583109772602150]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 43140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 43100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk431A
