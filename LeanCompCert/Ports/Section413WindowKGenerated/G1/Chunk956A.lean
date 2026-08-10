import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk956A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362499658061476746, 362499797003837973⟩, ⟨(-1401582381023092936), (-1392614286298710236)⟩, true⟩

def state01 : KState := ⟨⟨362498694015350733, 362498832987925326⟩, ⟨(-1309446827361666710), (-1300475844084120428)⟩, true⟩

def words00 : List Nat := [371285230196448773, 371285230227976870, 371285230367962902, 371285230509651839, 371285230682532426, 371285230765646098, 371285230847325220, 371285230930159416, 371285231103084190, 371285231249170538]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 95600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 95600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487545002328224, 362487684005107471⟩, ⟨(-243405954043960279), (-234432082749722979)⟩, true⟩

def words01 : List Nat := [371285231472361486, 371285231696906373, 371285231887327803, 371285231932682160, 371285231997469526, 371285232063992124, 371285232238201995, 371285232267633075, 371285232295778094, 371285232325217597]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 95610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 95600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490156440902205, 362490295473639727⟩, ⟨(-493097316398417262), (-484120580338749870)⟩, true⟩

def words02 : List Nat := [371285232462635881, 371285232547037226, 371285232685680785, 371285232825701334, 371285232936187654, 371285232939539792, 371285232916251448, 371285232922236239, 371285233035991724, 371285233092399975]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 95620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 95600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362495126969351237, 362495266032658999⟩, ⟨(-968432042543232888), (-959452382900666518)⟩, true⟩

def words03 : List Nat := [371285233143899202, 371285233196576281, 371285233357327670, 371285233495211614, 371285233659805987, 371285233825650087, 371285233988288088, 371285234005969420, 371285234113136279, 371285234222212636]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 95630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 95600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486746800230468, 362486885893446004⟩, ⟨(-166908034057183598), (-157925513882523496)⟩, true⟩

def words04 : List Nat := [371285234356824823, 371285234406156015, 371285234455074971, 371285234505072403, 371285234544455472, 371285234548158649, 371285234632261236, 371285234723472151, 371285234812982807, 371285234833719681]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 95640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 95600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk956A
