import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk359A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk359A
