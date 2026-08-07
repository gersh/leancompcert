import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk434

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362502155833457465, 362502182738778585⟩, ⟨(-724730191703664081), (-723941214777161121)⟩, true⟩

def state01 : KState := ⟨⟨362486300645575446, 362486327563806832⟩, ⟨(-36629674438649657), (-35840137138833565)⟩, true⟩

def words00 : List Nat := [371285502707028331, 371285502708460739, 371285502337431525, 371285502418698153, 371285502658094194, 371285502659536339, 371285502423935368, 371285502105343332, 371285501942796961, 371285501963448886]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 43400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 43400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362480590902960645, 362480617834080187⟩, ⟨211384548474741593, 212174645314906211⟩, true⟩

def words01 : List Nat := [371285502514354427, 371285503065803650, 371285503582058141, 371285503664231867, 371285503873408355, 371285504083310471, 371285504566115005, 371285504567551801, 371285504509860410, 371285504398919315]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 43410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 43400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362496508251437614, 362496535195399313⟩, ⟨(-479816252086903431), (-479025597575919905)⟩, true⟩

def words02 : List Nat := [371285504393926978, 371285504395505558, 371285504555502529, 371285504873349786, 371285505123476634, 371285505124909858, 371285504740916105, 371285504815453345, 371285505362057332, 371285505617503895]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 43420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 43400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485300294721549, 362485327251749675⟩, ⟨7060082809240298, 7851304860126852⟩, true⟩

def words03 : List Nat := [371285505890881717, 371285506164742728, 371285506774494426, 371285507194029218, 371285507546377673, 371285507899225005, 371285508249824325, 371285508251258896, 371285507993178196, 371285507990811833]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 43430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 43400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362495734699856464, 362495761669668651⟩, ⟨(-446180173599138583), (-445388396141379467)⟩, true⟩

def words04 : List Nat := [371285508513654620, 371285508704796294, 371285508898534921, 371285509092724380, 371285509445129827, 371285509594446905, 371285510121914785, 371285510649952243, 371285511072173693, 371285511309581625]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 43440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 43400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362528010028621122, 362528037011380708⟩, ⟨(-1848681815323033812), (-1847889475235902080)⟩, true⟩

def words05 : List Nat := [371285512076374184, 371285512843878328, 371285513996458915, 371285514443606703, 371285514812067143, 371285515181004484, 371285516079066891, 371285516714383245, 371285517693739144, 371285518673670212]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 43450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 43400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362496679639640418, 362496706635363104⟩, ⟨(-486990487230364512), (-486197583701702230)⟩, true⟩

def words06 : List Nat := [371285519554245753, 371285519845992514, 371285520352659541, 371285520860040687, 371285521525265005, 371285521552947453, 371285521578516794, 371285521604555982, 371285521964167392, 371285522223141124]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 43460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 43400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362463852162678892, 362463879171324264⟩, ⟨940292075577927883, 941085540921713933⟩, true⟩

def words07 : List Nat := [371285522874084306, 371285523525619652, 371285524151912706, 371285524153347601, 371285524074392938, 371285524065371076, 371285524263663274, 371285524265098265, 371285523769182931, 371285523273001397]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 43470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 43400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483851635942816, 362483878657436874⟩, ⟨70653340729760297, 71447364800154561⟩, true⟩

def words08 : List Nat := [371285522807544480, 371285522809125179, 371285522578394747, 371285522498231695, 371285522417617527, 371285522254396112, 371285521551336047, 371285521378113262, 371285521501773213, 371285521503258906]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 43480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 43400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362499216891832324, 362499243926404490⟩, ⟨(-597713025254883390), (-596918432351918046)⟩, true⟩

def words09 : List Nat := [371285521466578720, 371285521329055495, 371285521317710742, 371285521319302748, 371285521360152001, 371285521460940403, 371285521557181751, 371285521558649451, 371285521661827132, 371285521979038869]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 43490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 43400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 43400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk434
