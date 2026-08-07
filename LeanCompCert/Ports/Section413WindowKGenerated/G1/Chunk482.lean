import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk482

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496113110909590, 362496146581308427⟩, ⟨(-528282871675544782), (-527192915309283862)⟩, true⟩

def state01 : KState := ⟨⟨362471580159427266, 362471613644326465⟩, ⟨654347345486682474, 655438000843511782⟩, true⟩

def words00 : List Nat := [371285209425493348, 371285209427136843, 371285209613719866, 371285209809287948, 371285210109127697, 371285210110732550, 371285209837777485, 371285209566956253, 371285209295490350, 371285209122460535]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 48200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 48200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362448982179875096, 362449015679204425⟩, ⟨1743992509746810611, 1745083860854231017⟩, true⟩

def words01 : List Nat := [371285208894028512, 371285208948235253, 371285208949454860, 371285208925340445, 371285208328095837, 371285207864438952, 371285207399927372, 371285207221776568, 371285206470690523, 371285205721943003]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 48210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 48200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362463651415694076, 362463684929422332⟩, ⟨1036618764030610869, 1037710809525778497⟩, true⟩

def words02 : List Nat := [371285204972528728, 371285204652489300, 371285204193911916, 371285203905832692, 371285203617233667, 371285203263763295, 371285202337441951, 371285201735586946, 371285201132946897, 371285200807704020]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 48220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 48200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362462100413487107, 362462133941855353⟩, ⟨1111450046533263592, 1112542798188357526⟩, true⟩

def words03 : List Nat := [371285200362817000, 371285199879638270, 371285199395813472, 371285199295786689, 371285198979518156, 371285198677386557, 371285198374760296, 371285197984941577, 371285197079571959, 371285196603509341]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 48230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 48200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362457990745839092, 362458024288512205⟩, ⟨1309725918568688773, 1310819360365048845⟩, true⟩

def words04 : List Nat := [371285196126529886, 371285195965616460, 371285195232356073, 371285194493374886, 371285193753794955, 371285193147521986, 371285192420935284, 371285192123228714, 371285191824990324, 371285191529141533]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 48240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 48200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362476672403353672, 362476705960558518⟩, ⟨408212730640486221, 409306873665797395⟩, true⟩

def words05 : List Nat := [371285190967211127, 371285190545401694, 371285190122796362, 371285190092473569, 371285189599765338, 371285189034877764, 371285188469336312, 371285188023447931, 371285187420744971, 371285187246792787]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 48250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 48200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362443153532966789, 362443187104648832⟩, ⟨2025961628999085883, 2027056470769774447⟩, true⟩

def words06 : List Nat := [371285187072256412, 371285186899695765, 371285186216295333, 371285185775997136, 371285185334930199, 371285184925644624, 371285183944567620, 371285182968686846, 371285181992202432, 371285181230830100]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 48260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 48200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362424910261628941, 362424943847818725⟩, ⟨2906784477494197064, 2907880019625951400⟩, true⟩

def words07 : List Nat := [371285180361954901, 371285179921643217, 371285179480756693, 371285179041952241, 371285178031449715, 371285177149830256, 371285176267415260, 371285175692011682, 371285174588545364, 371285173342839976]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 48270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 48200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362461504128403960, 362461537728981476⟩, ⟨1139892008402548364, 1140988245247486086⟩, true⟩

def words08 : List Nat := [371285172096452635, 371285171278438775, 371285170299046071, 371285169685246317, 371285169071000206, 371285168344312410, 371285167260428157, 371285166576170446, 371285165891086686, 371285165565909360]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 48280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 48200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362465534086995681, 362465567702218868⟩, ⟨945243388626446374, 946340332784224334⟩, true⟩

def words09 : List Nat := [371285165077831266, 371285164592050581, 371285164105670535, 371285163800009435, 371285163281732115, 371285162843237158, 371285162404207642, 371285161905282470, 371285161073419468, 371285160669771337]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 48290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 48200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 48200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk482
