import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk796A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360548510724678062, 360548551978654923⟩, ⟨2677477447643234533, 2679695281089976829⟩, true⟩

def state01 : KState := ⟨⟨360573901247827725, 360573942512538806⟩, ⟨656268020032776357, 658486707976882393⟩, true⟩

def words00 : List Nat := [360582216070240785, 360582215806171606, 360582215620579282, 360582215508492393, 360582215396311177, 360582215140484371, 360582214777377433, 360582214439029828, 360582214100355728, 360582213919497441]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 79600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 79600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360588769327605199, 360588810603170462⟩, ⟨(-527519586691861692), (-525300034591919442)⟩, true⟩

def words01 : List Nat := [360582213816634199, 360582213565578170, 360582213314305107, 360582213220916637, 360582213206679234, 360582213153336961, 360582213099872056, 360582212967620060, 360582213012892050, 360582213097052831]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 79610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 79600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360590731325370733, 360590772611653515⟩, ⟨(-683736712125397386), (-681516306643829074)⟩, true⟩

def words02 : List Nat := [360582213338328020, 360582213488394255, 360582213557351098, 360582213626420273, 360582213627395624, 360582213606625951, 360582213805494739, 360582214004579617, 360582214073408139, 360582214182063986]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 79620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 79600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360612350975393190, 360612392272438313⟩, ⟨(-2405379350740251077), (-2403158088200592217)⟩, true⟩

def words03 : List Nat := [360582214447919503, 360582214714136341, 360582215137434985, 360582215477523941, 360582215682825069, 360582215888209882, 360582216207173986, 360582216626619830, 360582217006457690, 360582217386535316]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 79630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 79600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360606204332518148, 360606245640406912⟩, ⟨(-1915942029547267723), (-1913719903367464853)⟩, true⟩

def words04 : List Nat := [360582217687257214, 360582217830814416, 360582218092376851, 360582218354266790, 360582218521933253, 360582218693942512, 360582218779484843, 360582218865151558, 360582219023859144, 360582219326821804]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 79640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 79600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk796A
