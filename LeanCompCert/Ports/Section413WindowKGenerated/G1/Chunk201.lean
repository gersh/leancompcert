import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk201

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488086487052881, 362488091898541380⟩, ⟨(-65031562156072355), (-64957997614726065)⟩, true⟩

def state01 : KState := ⟨⟨362504563920549494, 362504569337591496⟩, ⟨(-396154928641726037), (-396081252445588277)⟩, true⟩

def words00 : List Nat := [371284862945536820, 371284863478653306, 371284864018287130, 371284864558094443, 371284865862065061, 371284865946693338, 371284868495641031, 371284871044586976, 371284873600871974, 371284874580869027]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 20100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 20100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362539084717802657, 362539090140496973⟩, ⟨(-1090587548274387533), (-1090513758381591099)⟩, true⟩

def words01 : List Nat := [371284875801509445, 371284877022348162, 371284880706060529, 371284881544198117, 371284881886267376, 371284882228486311, 371284885033175465, 371284886960359528, 371284889654781755, 371284892349215149]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 20110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 20100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362506529529749024, 362506534958078556⟩, ⟨(-435634797088320585), (-435560893786833071)⟩, true⟩

def words02 : List Nat := [371284894919612372, 371284894920236845, 371284895951081643, 371284897697727446, 371284899288253401, 371284899288878477, 371284898234927722, 371284897188626617, 371284897555782965, 371284898631329422]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 20120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 20100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362449476138184831, 362449481572135072⟩, ⟨713390217175585621, 713464233651352233⟩, true⟩

def words03 : List Nat := [371284901568790954, 371284904506219736, 371284907416891269, 371284907417516247, 371284907436217156, 371284907826734520, 371284909835816753, 371284909836441805, 371284908565511641, 371284906807172379]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 20130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 20100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362526774172338701, 362526779611885854⟩, ⟨(-843809532504577184), (-843735403278464264)⟩, true⟩

def words04 : List Nat := [371284905048737939, 371284904553369405, 371284903579471241, 371284904321055752, 371284904507483273, 371284904508119325, 371284903241693499, 371284903836726250, 371284906886506026, 371284908965105126]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 20140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 20100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362501022490271304, 362501027935535229⟩, ⟨(-324716846412877577), (-324642601966057553)⟩, true⟩

def words05 : List Nat := [371284911019980169, 371284913074867624, 371284916168879553, 371284918032888559, 371284920297845716, 371284922562811056, 371284924834084209, 371284924834709874, 371284924631062748, 371284925430601642]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 20150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 20100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362454094959135206, 362454100409965289⟩, ⟨621766953873236405, 621841310563340051⟩, true⟩

def words06 : List Nat := [371284928681654505, 371284929441279181, 371284929750669692, 371284930060229313, 371284930800059625, 371284930800748843, 371284930346087274, 371284930381539061, 371284930419756960, 371284930420404721]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 20160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 20100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362566728490548883, 362566733947034928⟩, ⟨(-1650571276765710301), (-1650496805966305633)⟩, true⟩

def words07 : List Nat := [371284929094281514, 371284929296886556, 371284931948880505, 371284933305217015, 371284934270299738, 371284935235492060, 371284938649192153, 371284941151126493, 371284945204714304, 371284949258170833]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 20170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 20100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362498175731592674, 362498181193731209⟩, ⟨(-266962440940833568), (-266887856044779928)⟩, true⟩

def words08 : List Nat := [371284952964399892, 371284953404533916, 371284956291687717, 371284959178884601, 371284962119878690, 371284962120505148, 371284961796368716, 371284961452498427, 371284962378948825, 371284963034351051]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 20180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 20100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362455542080550405, 362455547548336364⟩, ⟨594253547292443915, 594328246238352809⟩, true⟩

def words09 : List Nat := [371284965693675606, 371284968352999313, 371284970908758391, 371284970909386010, 371284970859302159, 371284970859241763, 371284972656674320, 371284972657301184, 371284971194650531, 371284969738744204]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 20190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 20100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 20100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk201
