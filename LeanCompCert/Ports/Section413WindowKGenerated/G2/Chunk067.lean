import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk067

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360345426658195028, 360345426892583489⟩, ⟨1563459235137513456, 1563460300375102606⟩, true⟩

def state01 : KState := ⟨⟨360904466984474938, 360904467219597884⟩, ⟨(-2185055873508852389), (-2185054803346520377)⟩, true⟩

def words00 : List Nat := [360578744352783144, 360578731639833396, 360578750388472994, 360578770803761666, 360578771532545824, 360578773185243587, 360578783331415250, 360578793474585039, 360578825669092623, 360578874192724614]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 6700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 6700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360719769641615746, 360719769877481067⟩, ⟨(-945072275046510503), (-945071199899049821)⟩, true⟩

def words01 : List Nat := [360578911405198608, 360578948606594439, 360578983375843920, 360579029806709101, 360579061771145534, 360579093726077114, 360579114410906676, 360579114410984679, 360579134282167925, 360579155207060141]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 6710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 6700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360419870304832139, 360419870541432156⟩, ⟨1070967195624407720, 1070968275712776104⟩, true⟩

def words02 : List Nat := [360579166508177948, 360579166508256012, 360579156080199093, 360579133961865106, 360579111850096479, 360579083083778960, 360579069642483901, 360579051497799193, 360579033358498907, 360579004014792153]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 6720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 6700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360896757865555376, 360896758102893264⟩, ⟨(-2140920285680575746), (-2140919200622686464)⟩, true⟩

def words03 : List Nat := [360578980372978590, 360578969245518461, 360578968900416460, 360578992617729413, 360578997576170486, 360579002533145796, 360579029373274652, 360579067169283569, 360579114304500390, 360579161425750009]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 6730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 6700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360499237951810626, 360499238189895723⟩, ⟨539020341827606092, 539021431925330716⟩, true⟩

def words04 : List Nat := [360579191336460278, 360579199629264245, 360579210532411696, 360579221432348427, 360579221432414165, 360579220223526621, 360579197418536866, 360579160554218591, 360579123700808736, 360579093216847624]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 6740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 6700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360303957433521908, 360303957672345435⟩, ⟨1858672370736364971, 1858673465822243259⟩, true⟩

def words05 : List Nat := [360579081388289225, 360579081149090546, 360579080909954190, 360579069548185372, 360579056000903939, 360579027128837334, 360578998265293996, 360578979636617045, 360578950047736910, 360578909368472986]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 6750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 6700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360632773481029458, 360632773720595963⟩, ⟨(-364801361477595067), (-364800261365537767)⟩, true⟩

def words06 : List Nat := [360578868701224694, 360578849760705677, 360578869408639144, 360578890080842378, 360578890080915280, 360578888010112507, 360578883054114095, 360578886490617285, 360578888896088369, 360578896854347915]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 6760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 6700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360519831011183032, 360519831251499098⟩, ⟨400121192978126179, 400122298168513327⟩, true⟩

def words07 : List Nat := [360578896854418131, 360578889396284728, 360578881940339044, 360578889088149349, 360578891703663784, 360578894318420828, 360578894318491732, 360578885355224724, 360578855045209307, 360578846339724543]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 6770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 6700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360443407108890827, 360443407349951591⟩, ⟨918163266819495570, 918164377062595750⟩, true⟩

def words08 : List Nat := [360578850525582855, 360578850525661676, 360578842073709620, 360578813852002046, 360578785638600688, 360578743329635349, 360578716192865773, 360578691752394622, 360578667319115023, 360578630380446819]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 6780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 6700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360688633529220979, 360688633771027765⟩, ⟨(-747836221001032534), (-747835105688675930)⟩, true⟩

def words09 : List Nat := [360578612094275175, 360578613719741645, 360578636870498989, 360578649852434974, 360578649852508489, 360578643996512880, 360578638142226498, 360578641844761408, 360578658020109095, 360578674190717712]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 6790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 6700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 6700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk067
