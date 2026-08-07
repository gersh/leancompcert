import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk366

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362485540655445816, 362485559526414611⟩, ⟨(-24355415834135426), (-23888647979236994)⟩, true⟩

def state01 : KState := ⟨⟨362472014642243736, 362472033523848130⟩, ⟨470732154196439411, 471199311369333225⟩, true⟩

def words00 : List Nat := [371284907337939556, 371284907339131955, 371284906833737007, 371284906204267040, 371284905574386343, 371284905170640922, 371284904395345802, 371284904366334918, 371284904336891632, 371284904305366004]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 36600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 36600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362480325818172164, 362480344710532866⟩, ⟨166452620268947823, 166920171285239587⟩, true⟩

def words01 : List Nat := [371284904225178630, 371284904497148963, 371284905098954378, 371284905100147160, 371284904708235367, 371284904203713229, 371284903698736029, 371284903502531580, 371284903003294717, 371284902880147428]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 36610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 36600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362460322672187220, 362460341575324360⟩, ⟨898956732581212054, 899424678283681286⟩, true⟩

def words02 : List Nat := [371284902756583274, 371284902625885637, 371284901501482406, 371284901019056747, 371284900536029431, 371284900287709011, 371284899046015782, 371284897747043262, 371284896447667967, 371284895893595823]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 36620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 36600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362448730354739731, 362448749268639619⟩, ⟨1323687321136699692, 1324155661134076550⟩, true⟩

def words03 : List Nat := [371284895224104519, 371284894863504732, 371284894502509205, 371284894139663297, 371284893064771022, 371284892049125113, 371284891032930031, 371284890761560635, 371284889873225147, 371284888888212056]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 36630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 36600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362462228032718511, 362462246957291194⟩, ⟨829129942435240327, 829598673539225179⟩, true⟩

def words04 : List Nat := [371284887902711231, 371284887293281208, 371284886363194601, 371284886177762679, 371284885991996454, 371284885603524011, 371284884341820581, 371284883578167297, 371284882813914996, 371284882664618322]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 36640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 36600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362459818748716651, 362459837684172667⟩, ⟨917544698416255119, 918013828447669285⟩, true⟩

def words05 : List Nat := [371284882047911644, 371284881410819749, 371284880878632444, 371284880879948203, 371284880652492558, 371284880650846750, 371284880648830752, 371284880650024974, 371284879659526488, 371284878977911011]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 36650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 36600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362449166842621671, 362449185788712511⟩, ⟨1308132112710574585, 1308601632669671301⟩, true⟩

def words06 : List Nat := [371284878295671866, 371284878229225512, 371284877365479841, 371284876314853598, 371284875263817443, 371284874438819498, 371284873344058017, 371284872820081837, 371284872295744496, 371284871679977024]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 36660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 36600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489337965774623, 362489356922689057⟩, ⟨(-165149686842001633), (-164679769927853569)⟩, true⟩

def words07 : List Nat := [371284870707651333, 371284870478848902, 371284870249442444, 371284870190832419, 371284869470300569, 371284868615228510, 371284867759728256, 371284867647437151, 371284867287454823, 371284867411227324]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 36670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 36600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362464833648708154, 362464852616399535⟩, ⟨733719921586453083, 734190233855268545⟩, true⟩

def words08 : List Nat := [371284867532322462, 371284867533517528, 371284866664529250, 371284866538584607, 371284866412064937, 371284866152115248, 371284865396618852, 371284864500858895, 371284863604648601, 371284863252372696]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 36680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 36600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362466607399646016, 362466626378083042⟩, ⟨668761536123094937, 669232242705282795⟩, true⟩

def words09 : List Nat := [371284862904462699, 371284863102399408, 371284863274588097, 371284863275804327, 371284862832909110, 371284862496182497, 371284862562564987, 371284862563760960, 371284862084608813, 371284861589055938]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 36690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 36600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 36600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk366
