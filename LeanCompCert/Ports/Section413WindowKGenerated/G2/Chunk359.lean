import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk359

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360614214119915213, 360614221988721949⟩, ⟨(-1155740685289246190), (-1155549713718958834)⟩, true⟩

def state01 : KState := ⟨⟨360585936739904709, 360585944613319104⟩, ⟨(-140731319244770018), (-140540182238181482)⟩, true⟩

def words00 : List Nat := [360582035378263143, 360582035484598521, 360582035484995944, 360582035295284303, 360582035105450922, 360582034563281198, 360582033804443748, 360582032655564825, 360582031506657497, 360582031044155389]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 35900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 35900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360506997460249636, 360507005338202831⟩, ⟨2694585788593181111, 2694777088611236551⟩, true⟩

def words01 : List Nat := [360582031927321388, 360582032810530577, 360582033303760813, 360582033304243375, 360582033025263309, 360582032244939132, 360582031464523798, 360582030648403030, 360582029060207164, 360582026972072855]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 35910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 35900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360566291495309133, 360566299377816815⟩, ⟨564507799364798959, 564699263002958727⟩, true⟩

def words02 : List Nat := [360582024883946812, 360582023054045367, 360582021611999754, 360582020943420258, 360582020274832495, 360582018952141838, 360582017897900946, 360582017280750232, 360582016663488953, 360582016028610107]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 35920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 35900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590752682434618, 360590760569545836⟩, ⟨(-314615040406759641), (-314423411341207751)⟩, true⟩

def words03 : List Nat := [360582015591636069, 360582014458226365, 360582013324785185, 360582013040027084, 360582013040431212, 360582012920285880, 360582012800101813, 360582012094796331, 360582012004406155, 360582012248371100]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 35930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 35900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360570894608782344, 360570902500440266⟩, ⟨399137923839623919, 399329716336736627⟩, true⟩

def words04 : List Nat := [360582013090756481, 360582013161986206, 360582013162416453, 360582012844776296, 360582012527084010, 360582011551500653, 360582010972682235, 360582010954766905, 360582010936796084, 360582010420227102]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 35940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 35900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360584157150647206, 360584165046872031⟩, ⟨(-77620187483306632), (-77428230784161018)⟩, true⟩

def words05 : List Nat := [360582010574631258, 360582011038134033, 360582012076172712, 360582012343473492, 360582012343924361, 360582011865433036, 360582011386876052, 360582011809485379, 360582011869764268, 360582011930140457]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 35950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 35900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360602114445681680, 360602122346505979⟩, ⟨(-723748828448584693), (-723556706329912399)⟩, true⟩

def words06 : List Nat := [360582011930571013, 360582011602439247, 360582010503657875, 360582010176474341, 360582009849175522, 360582009326566844, 360582008852772431, 360582007906793070, 360582006960773908, 360582007345357001]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 35960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 35900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360536479831915629, 360536487737295497⟩, ⟨1637512863606653127, 1637705149612196051⟩, true⟩

def words07 : List Nat := [360582008134057068, 360582008922805916, 360582009104703468, 360582009105186923, 360582008516938658, 360582007719528438, 360582006922021081, 360582006895480725, 360582006098875917, 360582004834283052]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 35970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 35900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360548368574356747, 360548376484299073⟩, ⟨1209785344137557467, 1209977794323232219⟩, true⟩

def words08 : List Nat := [360582003569645250, 360582002417145388, 360582001672756637, 360582001686177003, 360582001686622798, 360582001046121668, 360582000083058934, 360581998867532689, 360581997651933940, 360581996317428366]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 35980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 35900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360558383421851642, 360558391336404506⟩, ⟨849281004319024082, 849473620460580936⟩, true⟩

def words09 : List Nat := [360581995383746389, 360581993963494610, 360581992543226048, 360581991893512054, 360581991842916691, 360581991371755522, 360581990900569823, 360581989906090279, 360581988480780926, 360581987825861745]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 35990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 35900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 35900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk359
