import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk097

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362475212761716174, 362475213942748616⟩, ⟨66400224608036256, 66407981109626994⟩, true⟩

def state01 : KState := ⟨⟨362517790091730441, 362517791275300855⟩, ⟨(-346180297029444232), (-346172515896549078)⟩, true⟩

def words00 : List Nat := [371282067582790998, 371282072883193654, 371282086812662036, 371282100739376429, 371282113126156958, 371282114458148974, 371282122132286261, 371282129804984682, 371282140140517845, 371282143812022455]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 9700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 9700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362515660325034254, 362515661511192409⟩, ⟨(-325503696214199739), (-325495889941274707)⟩, true⟩

def words01 : List Nat := [371282147345931378, 371282150879208314, 371282159696817500, 371282163279895388, 371282168433694145, 371282173586542465, 371282177987546995, 371282177987830877, 371282174279360759, 371282177724550986]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 9710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 9700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362471269952769349, 362471271141461954⟩, ⟨106308944055270757, 106316774976063277⟩, true⟩

def words02 : List Nat := [371282191764963061, 371282191765246896, 371282191724157035, 371282189848787962, 371282189239731060, 371282189240043635, 371282189887381573, 371282194477030657, 371282197839516260, 371282197839815096]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 9720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 9700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362574989469567950, 362574990660823863⟩, ⟨(-903308936921681168), (-903301081046422028)⟩, true⟩

def words03 : List Nat := [371282203386587559, 371282210055007490, 371282227289851927, 371282233054171940, 371282234825697307, 371282236596947882, 371282240789758524, 371282240790074441, 371282249276416595, 371282258797458047]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 9730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 9700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362550432558385141, 362550433752210519⟩, ⟨(-664462523662193724), (-664454642747422428)⟩, true⟩

def words04 : List Nat := [371282267247107619, 371282267247392233, 371282266650148642, 371282271627618391, 371282279700394723, 371282279700681260, 371282278508412298, 371282277010936150, 371282284557756693, 371282291547026700]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 9740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 9700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362476955411267626, 362476956607662346⟩, ⟨52429261391920244, 52437167370967978⟩, true⟩

def words05 : List Nat := [371282303085658567, 371282314622038752, 371282326031505746, 371282326031790536, 371282323968095147, 371282324486921172, 371282330255505329, 371282330255795954, 371282329818464123, 371282329268253634]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 9750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 9700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362590416288839640, 362590417487784177⟩, ⟨(-1055416495613443629), (-1055408564735068589)⟩, true⟩

def words06 : List Nat := [371282336077734955, 371282338254102174, 371282347224531326, 371282356193234851, 371282363438427222, 371282363438712985, 371282367251659343, 371282374403950020, 371282392045858172, 371282403101873312]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 9760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 9700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478608717952262, 362478609919497247⟩, ⟨37962741497378253, 37970697795401229⟩, true⟩

def words07 : List Nat := [371282414039414336, 371282424974815369, 371282443257450188, 371282456467719084, 371282469087187140, 371282481704186403, 371282494210481005, 371282494210766432, 371282492800607762, 371282492403934405]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 9770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 9700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362515565125048562, 362515566329136974⟩, ⟨(-323556003622891800), (-323548022436735298)⟩, true⟩

def words08 : List Nat := [371282502074168822, 371282502074454519, 371282500714094034, 371282499422970903, 371282498881788675, 371282498882108521, 371282503037448425, 371282510341796237, 371282517501215507, 371282520876942435]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 9780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 9700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362635173007536916, 362635174214217845⟩, ⟨(-1495057085602144491), (-1495049079022731063)⟩, true⟩

def words09 : List Nat := [371282534701149454, 371282548522688122, 371282566451052918, 371282572667561235, 371282577406463847, 371282582144485447, 371282594475554381, 371282602616691455, 371282618185416693, 371282633751099518]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 9790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 9700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 9700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk097
