import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk334

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362445693072829434, 362445708669573421⟩, ⟨1300211851509431029, 1300563935037243387⟩, true⟩

def state01 : KState := ⟨⟨362474693572478942, 362474709178895000⟩, ⟨331536892425326803, 331889299048483143⟩, true⟩

def words00 : List Nat := [371284646544472967, 371284646159107103, 371284645623649522, 371284645804401231, 371284645805239259, 371284645746037794, 371284644492971429, 371284643700571391, 371284643008931742, 371284643010054787]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 33400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 33400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362490482836659953, 362490498452907444⟩, ⟨(-196091090170591231), (-195738355028434033)⟩, true⟩

def words01 : List Nat := [371284642713555166, 371284642160004207, 371284641946114552, 371284641947304330, 371284641841165713, 371284641840678686, 371284641839826173, 371284641809204098, 371284641528930879, 371284641705502267]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 33410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 33400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473489709739017, 362473505335607499⟩, ⟨371974481568067773, 372327538294353805⟩, true⟩

def words02 : List Nat := [371284642543122998, 371284642544206447, 371284642474193533, 371284642393379064, 371284642312156615, 371284642276599754, 371284642210432215, 371284642625157385, 371284642861808591, 371284642862927103]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 33420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 33400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362496688025578778, 362496703661246624⟩, ⟨(-403567871385719870), (-403214487018489482)⟩, true⟩

def words03 : List Nat := [371284642937368783, 371284643345526033, 371284644510716326, 371284644629695718, 371284644630540083, 371284644613955484, 371284645245640612, 371284645449173368, 371284645810514433, 371284646172325286]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 33430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 33400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480473175639126, 362480488821049424⟩, ⟨138685948659423713, 139039658864720141⟩, true⟩

def words04 : List Nat := [371284646479151940, 371284646480234687, 371284645940998462, 371284646050506540, 371284646432520789, 371284646433620766, 371284646076112960, 371284645718507542, 371284645461336108, 371284645462570044]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 33440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 33400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362451561386757812, 362451577041907109⟩, ⟨1106008340920072294, 1106362376944421798⟩, true⟩

def words05 : List Nat := [371284645673621814, 371284646009338440, 371284646128366236, 371284646129448150, 371284645216321257, 371284644576818984, 371284644188509752, 371284644189591339, 371284643252372335, 371284642265366297]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 33450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 33400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482960602838711, 362482976267661553⟩, ⟨55365928465855514, 55720288216274434⟩, true⟩

def words06 : List Nat := [371284641277928681, 371284641183343258, 371284641340037557, 371284641819306642, 371284642027774467, 371284642028857314, 371284641276200322, 371284640903950771, 371284641049577790, 371284641050697594]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 33460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 33400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362482339411801521, 362482355086505797⟩, ⟨76135832670484283, 76490523201130605⟩, true⟩

def words07 : List Nat := [371284641001776248, 371284640952852263, 371284641056231703, 371284641057444033, 371284640887034145, 371284640850196513, 371284640813006221, 371284640775580957, 371284639816561986, 371284639749683848]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 33470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 33400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362459178272071496, 362459193956432885⟩, ⟨851648519581383366, 852003533481575020⟩, true⟩

def words08 : List Nat := [371284639979810805, 371284639980893209, 371284639091211812, 371284638201590294, 371284637311610683, 371284636579217446, 371284635401301358, 371284635114966695, 371284634828250198, 371284634491920541]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 33480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 33400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488446899755156, 362488462593880704⟩, ⟨(-128666447857772530), (-128311106906061198)⟩, true⟩

def words09 : List Nat := [371284633766186995, 371284633800622090, 371284634725190996, 371284634726273859, 371284634463634660, 371284633841342145, 371284633218639532, 371284632979231363, 371284632410377499, 371284632525915388]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 33490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 33400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 33400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk334
