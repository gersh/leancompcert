import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk161

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362588806581357930, 362588809985857383⟩, ⟨(-1678705067273480572), (-1678667989837079858)⟩, true⟩

def state01 : KState := ⟨⟨362541003146779457, 362541006555703542⟩, ⟨(-908949583869310902), (-908912435173612990)⟩, true⟩

def words00 : List Nat := [371284557866155367, 371284559916528701, 371284565828153811, 371284571739305557, 371284578786618982, 371284580697639262, 371284581842864040, 371284582988099324, 371284587409566905, 371284590912033155]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 16100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 16100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362519579553031032, 362519582966379802⟩, ⟨(-563382652901158452), (-563345432901474054)⟩, true⟩

def words01 : List Nat := [371284598270667963, 371284605628595583, 371284612630602048, 371284616457424285, 371284620536367549, 371284624615039928, 371284631776951497, 371284633810235894, 371284635978668740, 371284638147019870]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 16110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 16100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362569525112371731, 362569528530124995⟩, ⟨(-1368775966730163786), (-1368738675708179740)⟩, true⟩

def words02 : List Nat := [371284641632077725, 371284643215517628, 371284647509132428, 371284651802409267, 371284655505655870, 371284655816998147, 371284659978077892, 371284664138917343, 371284671823124953, 371284677084107502]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 16120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 16100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362530659266364839, 362530662688583529⟩, ⟨(-741633132910151564), (-741595769837490116)⟩, true⟩

def words03 : List Nat := [371284682295861427, 371284687507129818, 371284694199775444, 371284698994353679, 371284704011510100, 371284709028230591, 371284713145956505, 371284713146448292, 371284714994682834, 371284717841929822]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 16130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 16100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362554508582362742, 362554512008972654⟩, ⟨(-1126504408990742975), (-1126466975021297715)⟩, true⟩

def words04 : List Nat := [371284724534049404, 371284728064843060, 371284731566107979, 371284735067111014, 371284739694438185, 371284743046939336, 371284749519897029, 371284755992251433, 371284761731369373, 371284766050516751]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 16140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 16100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362607931014286525, 362607934445346483⟩, ⟨(-1989409320943058427), (-1989371815082634945)⟩, true⟩

def words05 : List Nat := [371284773496542587, 371284780941903923, 371284791108501983, 371284796955566324, 371284802118484232, 371284807280917093, 371284815654988077, 371284822134585439, 371284829753259714, 371284837371212294]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 16150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 16100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362498416759591346, 362498420195097990⟩, ⟨(-219273066746738756), (-219235489005371012)⟩, true⟩

def words06 : List Nat := [371284844960406033, 371284847448889738, 371284851497663576, 371284855546184436, 371284860376499599, 371284860767915991, 371284860768285339, 371284860731498622, 371284862031938135, 371284862870937124]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 16160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 16100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362427614281008770, 362427617720939464⟩, ⟨926275426465375525, 926313075766865803⟩, true⟩

def words07 : List Nat := [371284866887451279, 371284870903666338, 371284874827996689, 371284874828489480, 371284873675463511, 371284873691711756, 371284875269586807, 371284875270079653, 371284871758079843, 371284868220059790]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 16170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 16100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362495930690764272, 362495934135106211⟩, ⟨(-179337847945782221), (-179300127247927619)⟩, true⟩

def words08 : List Nat := [371284864682265759, 371284863051643271, 371284860937081634, 371284861791776662, 371284862321589082, 371284862322082159, 371284857767492247, 371284857034744812, 371284859389243916, 371284860073760530]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 16180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 16100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362537290020753115, 362537293469604825⟩, ⟨(-849200240546318098), (-849162446813391812)⟩, true⟩

def words09 : List Nat := [371284860074139113, 371284859956078348, 371284863538646276, 371284865352666739, 371284867753684882, 371284870154590194, 371284872528942522, 371284872797816094, 371284876033995283, 371284879270060761]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 16190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 16100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 16100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk161
