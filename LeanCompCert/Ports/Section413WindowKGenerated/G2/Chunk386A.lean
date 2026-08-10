import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk386A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360613414457064085, 360613423608132466⟩, ⟨(-1205844817410330160), (-1205606059164911896)⟩, true⟩

def state01 : KState := ⟨⟨360597709157319810, 360597718313360776⟩, ⟨(-599793651194678474), (-599554700983876968)⟩, true⟩

def words00 : List Nat := [360582191574873909, 360582191575395723, 360582191860850367, 360582192338438955, 360582192356181089, 360582192356703007, 360582191910423659, 360582190994295587, 360582190078114013, 360582190233254489]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 38600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 38600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360547073034086197, 360547082195041731⟩, ⟨1355719569461244262, 1355958709448783160⟩, true⟩

def words01 : List Nat := [360582191304710167, 360582192376219372, 360582193041941242, 360582193298973790, 360582193387554547, 360582193476268765, 360582193758787558, 360582193759309583, 360582193375771046, 360582192467166247]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 38610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 38600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360602303304024615, 360602312469908166⟩, ⟨(-777628132362714351), (-777388802031414477)⟩, true⟩

def words02 : List Nat := [360582191558493264, 360582190748789113, 360582190386245530, 360582190224161200, 360582190062043584, 360582189313035793, 360582188781190279, 360582188466112108, 360582188503485574, 360582189024953819]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 38620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 38600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360580929845699247, 360580939016561026⟩, ⟨48090409904904893, 48329932569515235⟩, true⟩

def words03 : List Nat := [360582189144585229, 360582189264270999, 360582189366249069, 360582189875088051, 360582190215785288, 360582190556552577, 360582190557022602, 360582190522838717, 360582189822977991, 360582189791213447]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 38630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 38600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360540227941269957, 360540237117048053⟩, ⟨1620960913533026809, 1621200626188941375⟩, true⟩

def words04 : List Nat := [360582189949592027, 360582189950114331, 360582189565667297, 360582188671679264, 360582187777652414, 360582186555509430, 360582185736697263, 360582184900648141, 360582184064587394, 360582182799485025]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 38640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 38600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk386A
