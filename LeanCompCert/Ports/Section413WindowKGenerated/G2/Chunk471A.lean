import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk471A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360575720169402598, 360575734018400512⟩, ⟨337933897161747604, 338374677826524208⟩, true⟩

def state01 : KState := ⟨⟨360565754831895622, 360565768686996310⟩, ⟨807264733650766099, 807705801787378915⟩, true⟩

def words00 : List Nat := [360582918042148216, 360582917861415660, 360582917613624782, 360582917015725437, 360582916417744948, 360582915707081954, 360582915225056716, 360582914842429623, 360582914459748294, 360582913789984792]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 47100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 47100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360576639263288209, 360576653124494875⟩, ⟨294409596633992436, 294850952453806132⟩, true⟩

def words01 : List Nat := [360582913511676255, 360582913597487187, 360582913754374819, 360582913755022244, 360582913462830963, 360582912777794469, 360582912092672267, 360582911285861046, 360582910704680937, 360582910572552045]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 47110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 47100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360555966294128002, 360555980161502107⟩, ⟨1268429828808013765, 1268871475266875269⟩, true⟩

def words02 : List Nat := [360582910440333494, 360582910069993706, 360582909250540292, 360582908880172261, 360582908509626360, 360582907839030674, 360582906719426174, 360582905316524476, 360582903913558033, 360582902959619376]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 47120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 47100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360529949868715105, 360529963742193164⟩, ⟨2494642068563906263, 2495084002733150777⟩, true⟩

def words03 : List Nat := [360582902388918676, 360582901807899448, 360582901226839445, 360582900418568302, 360582899161352393, 360582897604791338, 360582896048106489, 360582894940244722, 360582894096488569, 360582892974325815]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 47130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 47100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360595432982005960, 360595446861595851⟩, ⟨(-592683893580148267), (-592241671269227539)⟩, true⟩

def words04 : List Nat := [360582891852065675, 360582890687134768, 360582889789828154, 360582889341237838, 360582888892626147, 360582888021518013, 360582887083183914, 360582886593566101, 360582886103779187, 360582886329024554]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 47140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 47100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk471A
