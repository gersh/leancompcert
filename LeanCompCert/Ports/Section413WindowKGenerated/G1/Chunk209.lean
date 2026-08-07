import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk209

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362529852996573157, 362529858867129864⟩, ⟨(-947960547005648393), (-947877570212521793)⟩, true⟩

def state01 : KState := ⟨⟨362476679122502536, 362476684998930336⟩, ⟨163705288276216864, 163788387804962382⟩, true⟩

def words00 : List Nat := [371284510224450311, 371284510503455191, 371284513060750339, 371284515618145717, 371284518609345060, 371284518609995871, 371284518559026387, 371284518239127463, 371284518015298148, 371284518016042004]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 20900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 20900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362412389988922779, 362412395871218111⟩, ⟨1508484698337199791, 1508567920586250329⟩, true⟩

def words01 : List Nat := [371284518441809319, 371284519242357772, 371284520054146966, 371284520054798190, 371284517827010931, 371284516017011952, 371284514206839041, 371284513920093701, 371284510594922749, 371284507148492789]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 20910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 20900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362456437302421653, 362456443190558421⟩, ⟨586843805027693671, 586927149508682497⟩, true⟩

def words02 : List Nat := [371284503702098161, 371284502530919665, 371284500574023230, 371284499394894387, 371284498215687928, 371284496800759780, 371284492349542700, 371284489334363270, 371284486319126675, 371284485577061464]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 20920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 20900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362464274266582281, 362464280160640134⟩, ⟨422749922052818550, 422833390493192862⟩, true⟩

def words03 : List Nat := [371284484237795184, 371284482910931687, 371284481583939702, 371284481341766358, 371284479974457200, 371284479134198365, 371284478293803247, 371284476975896418, 371284473740742759, 371284472777187087]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 20930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 20900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362450225739204259, 362450231639071700⟩, ⟨717066989339672517, 717150579462509161⟩, true⟩

def words04 : List Nat := [371284472722296162, 371284472722948692, 371284471060736406, 371284469381559293, 371284467702266561, 371284466346086501, 371284463846608546, 371284463617257373, 371284463387714511, 371284463170310961]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 20940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 20900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362481763289639376, 362481769195420938⟩, ⟨56028248657823961, 56111962710659027⟩, true⟩

def words05 : List Nat := [371284461536876578, 371284460343321222, 371284459564014030, 371284459564666509, 371284456951258759, 371284453675654641, 371284450400101796, 371284448813874088, 371284446419867142, 371284446292878508]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 20950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 20900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362442811615275741, 362442817526943585⟩, ⟨872545863315415782, 872629700775619232⟩, true⟩

def words06 : List Nat := [371284446165654521, 371284445737757281, 371284442747192722, 371284442023227932, 371284441299026170, 371284440631437842, 371284437936759695, 371284435042201989, 371284432147652384, 371284430769708279]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 20960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 20900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362397288187176242, 362397294104725658⟩, ⟨1827642298035870312, 1827726258862318940⟩, true⟩

def words07 : List Nat := [371284428785828681, 371284428703005353, 371284428619964004, 371284428550024953, 371284425457416590, 371284423037315846, 371284420617100891, 371284419365527662, 371284415809459730, 371284411657578963]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 20970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 20900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478423575657677, 362478429499053133⟩, ⟨125195125667692233, 125279209173823761⟩, true⟩

def words08 : List Nat := [371284407505811013, 371284405616696816, 371284402913498378, 371284402472492423, 371284402031319799, 371284401191363070, 371284398468103232, 371284397661904749, 371284398017155987, 371284398017832258]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 20980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 20900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362426529327832498, 362426535257198803⟩, ⟨1214869137604931564, 1214953346468547854⟩, true⟩

def words09 : List Nat := [371284397733984176, 371284397463771394, 371284397868647661, 371284397869367496, 371284397405904777, 371284397051972480, 371284396697863912, 371284396323000193, 371284392932757681, 371284390178459211]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 20990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 20900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 20900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk209
