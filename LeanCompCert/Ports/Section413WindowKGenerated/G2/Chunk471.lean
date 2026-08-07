import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk471

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

def state06 : KState := ⟨⟨360591552966168410, 360591566851942703⟩, ⟨(-409713096058172407), (-409270582122283019)⟩, true⟩

def words05 : List Nat := [360582886329610241, 360582886299622104, 360582886552380241, 360582887118665701, 360582887572021633, 360582888025464107, 360582888130206144, 360582888325204991, 360582888509761018, 360582888694521905]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 47150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 47100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360606029278181834, 360606043170056296⟩, ⟨(-1092544758037334452), (-1092101956386500668)⟩, true⟩

def words06 : List Nat := [360582889327273537, 360582889511713804, 360582889512291137, 360582889454336203, 360582889396274940, 360582889397824780, 360582889906834406, 360582890415951012, 360582890700519711, 360582891192010749]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 47160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 47100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360586359888851466, 360586373786853731⟩, ⟨(-164654458371730042), (-164211367642065174)⟩, true⟩

def words07 : List Nat := [360582891970845840, 360582892749837752, 360582893381262619, 360582893700320538, 360582893700920712, 360582893552351935, 360582893403668920, 360582893182670905, 360582893256971429, 360582893331423748]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 47170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 47100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360573605195912718, 360573619100085003⟩, ⟨436986206487305378, 437429588348198602⟩, true⟩

def words08 : List Nat := [360582893332001217, 360582893182432885, 360582892769467397, 360582892602346895, 360582892435061844, 360582892155456519, 360582891427835639, 360582890349306468, 360582889270698621, 360582888639994904]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 47180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 47100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360556036581594200, 360556050491868010⟩, ⟨1266237973516184378, 1266681643338472712⟩, true⟩

def words09 : List Nat := [360582888511428930, 360582888579411837, 360582888579989407, 360582888424191441, 360582888282981305, 360582888029679702, 360582887878994047, 360582887879642601, 360582887535271752, 360582886967362470]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 47190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 47100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 47100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk471
