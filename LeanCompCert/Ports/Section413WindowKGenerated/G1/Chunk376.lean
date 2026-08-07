import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk376

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362468654639007659, 362468674599511388⟩, ⟨607094448460321308, 607601640796657060⟩, true⟩

def state01 : KState := ⟨⟨362472613341346882, 362472633312830581⟩, ⟨458345446748830943, 458853051988840147⟩, true⟩

def words00 : List Nat := [371284833871859586, 371284833873223414, 371284833917420468, 371284834233136967, 371284834397985442, 371284834399212628, 371284833621406395, 371284833551783244, 371284833605418148, 371284833606688301]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 37600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 37600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487656190726086, 362487676173400432⟩, ⟨(-107521778508044585), (-107013752331522299)⟩, true⟩

def words01 : List Nat := [371284833283250252, 371284832856386607, 371284832522497930, 371284832523849729, 371284832266451921, 371284832221645645, 371284832176411861, 371284832129566091, 371284831574517302, 371284831651661735]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 37610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 37600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362474529065973033, 362474549059561737⟩, ⟨386417563206622760, 386926000039138590⟩, true⟩

def words02 : List Nat := [371284832168029365, 371284832169262782, 371284832010964805, 371284831851232525, 371284831691044797, 371284831537743259, 371284831184600333, 371284831338218937, 371284831439370484, 371284831440641704]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 37620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 37600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362502604320477012, 362502624325199665⟩, ⟨(-670162925236377113), (-669654069379447823)⟩, true⟩

def words03 : List Nat := [371284831245763935, 371284831324797708, 371284832109661225, 371284832110890137, 371284832107939085, 371284832059877610, 371284832554514146, 371284832828250111, 371284833301775100, 371284833775815232]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 37630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 37600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362515880421483520, 362515900437282076⟩, ⟨(-1169989608320721010), (-1169480335509378262)⟩, true⟩

def words04 : List Nat := [371284834247699148, 371284834253829638, 371284834965677638, 371284835678109672, 371284836602090830, 371284836943974874, 371284837240972179, 371284837538381482, 371284838541178745, 371284839367575844]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 37640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 37600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362495932659412592, 362495952686272594⟩, ⟨(-418803086857260122), (-418293397525444616)⟩, true⟩

def words05 : List Nat := [371284840702554950, 371284842037949952, 371284843101269710, 371284843343142997, 371284843657048620, 371284843971565771, 371284844991064818, 371284845288717179, 371284845584574716, 371284845880889693]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 37650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 37600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362511722172053278, 362511742209902160⟩, ⟨(-1013434047116611059), (-1012923943887462417)⟩, true⟩

def words06 : List Nat := [371284846646274650, 371284847060813369, 371284848180261120, 371284849300174938, 371284850346797744, 371284850585906018, 371284851112794155, 371284851640262879, 371284852802102519, 371284853517170684]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 37660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 37600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362509926715008175, 362509946764075194⟩, ⟨(-945732916926027979), (-945222391054643025)⟩, true⟩

def words07 : List Nat := [371284854181099624, 371284854845421678, 371284856099064145, 371284857184751594, 371284858271133088, 371284859357909201, 371284860436249275, 371284860576000207, 371284861242604263, 371284861909876669]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 37670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 37600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483009255120174, 362483029315145903⟩, ⟨68674986177617745, 69185925031000169⟩, true⟩

def words08 : List Nat := [371284862865048520, 371284862986404531, 371284863097040561, 371284863208065512, 371284863530293149, 371284863603331291, 371284864087454249, 371284864572081160, 371284864971210061, 371284864972482889]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 37680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 37600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362520368364804407, 362520388435937388⟩, ⟨(-1339531656246571519), (-1339020298706605689)⟩, true⟩

def words09 : List Nat := [371284865580308752, 371284866237440158, 371284867598256032, 371284868162471512, 371284868539256848, 371284868916409754, 371284869472454793, 371284869711775628, 371284870654751807, 371284871598222033]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 37690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 37600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 37600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk376
