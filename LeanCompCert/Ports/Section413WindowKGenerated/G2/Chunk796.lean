import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk796

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

def state06 : KState := ⟨⟨360567333143037670, 360567374461659468⟩, ⟨1180335244815814541, 1182558225936873307⟩, true⟩

def words05 : List Nat := [360582219576015638, 360582219825410629, 360582219953702144, 360582219954840916, 360582219925824845, 360582219834199871, 360582219806742732, 360582219807881565, 360582219716186821, 360582219531028498]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 79650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 79600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360581031914185796, 360581073243560005⟩, ⟨89026912205013627, 91250749915027133⟩, true⟩

def words06 : List Nat := [360582219345596747, 360582219305376678, 360582219362812436, 360582219420468976, 360582219421519966, 360582219347688220, 360582219163603101, 360582218924276193, 360582218684609276, 360582218602539735]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 79660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 79600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360562105755554490, 360562147095776340⟩, ⟨1597011208546425575, 1599235910542286911⟩, true⟩

def words07 : List Nat := [360582218589178663, 360582218497091386, 360582218404792914, 360582218391416273, 360582218405280330, 360582218419328641, 360582218420359088, 360582218327946239, 360582218078180609, 360582217827585355]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 79670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 79600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360559844428360775, 360559885779325333⟩, ⟨1777114360759201163, 1779339918788693519⟩, true⟩

def words08 : List Nat := [360582217576633961, 360582217321886234, 360582216909888765, 360582216419219358, 360582215928368892, 360582215398582942, 360582214966715003, 360582214692348338, 360582214417844745, 360582214050360453]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 79680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 79600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360592439231508863, 360592480593222310⟩, ⟨(-820566659131550707), (-818340244471470259)⟩, true⟩

def words09 : List Nat := [360582213771096065, 360582213649417721, 360582213561717693, 360582213562857080, 360582213441156305, 360582213152902207, 360582212864434107, 360582212733536139, 360582212834896252, 360582212964905583]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 79690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 79600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 79600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk796
