import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk406

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362473240401436787, 362473263820039954⟩, ⟨483676846797162097, 484319322365680569⟩, true⟩

def state01 : KState := ⟨⟨362481735131854883, 362481758562377566⟩, ⟨138775107751368540, 139418067312011928⟩, true⟩

def words00 : List Nat := [371285192592502591, 371285192593970885, 371285192529072457, 371285192719740132, 371285192814979486, 371285192816312511, 371285192187463148, 371285191809781665, 371285191657951057, 371285191659331815]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 40600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 40600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362490846893395099, 362490870336043451⟩, ⟨(-231283615217699596), (-230640163170793144)⟩, true⟩

def words01 : List Nat := [371285191575792405, 371285191492411666, 371285191707972241, 371285191790303773, 371285192055377877, 371285192320960604, 371285192585708653, 371285192587043953, 371285192339253640, 371285192480668872]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 40610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 40600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476016161931532, 362476039616478313⟩, ⟨371194263683935310, 371838199106670610⟩, true⟩

def words02 : List Nat := [371285192868355633, 371285192869692064, 371285192632037078, 371285192276811359, 371285191921081398, 371285191681934618, 371285191268372102, 371285191365230693, 371285191429002673, 371285191430386920]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 40620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 40600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362527466820022795, 362527490286631711⟩, ⟨(-1719529131155946302), (-1718884705587401414)⟩, true⟩

def words03 : List Nat := [371285191435093373, 371285191665732015, 371285192417385286, 371285192627538298, 371285192688213203, 371285192749259128, 371285193414719512, 371285193852072370, 371285194893736435, 371285195935961516]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 40630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 40600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494991395630134, 362495014874282439⟩, ⟨(-399564361916910435), (-398919446842275451)⟩, true⟩

def words04 : List Nat := [371285196945072967, 371285197452058146, 371285198451289049, 371285199451161163, 371285200474480547, 371285200692143356, 371285200830081004, 371285200968470960, 371285201356231752, 371285201599163936]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 40640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 40600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362474266765645828, 362474290256306113⟩, ⟨443039000651564731, 443684403910703843⟩, true⟩

def words05 : List Nat := [371285202100887226, 371285202603111256, 371285203104897627, 371285203106232246, 371285202802230382, 371285202636895166, 371285202849912176, 371285202851248090, 371285202584286330, 371285202317395900]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 40650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 40600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476225109057719, 362476248611679470⟩, ⟨363437639268241195, 364083528941002099⟩, true⟩

def words06 : List Nat := [371285202308874820, 371285202310360396, 371285202377274841, 371285202482088530, 371285202492416917, 371285202493751928, 371285201698748719, 371285201214972879, 371285200750153795, 371285200751559997]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 40660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 40600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362487030024044109, 362487053538848329⟩, ⟨(-76026105046339415), (-75379719851871141)⟩, true⟩

def words07 : List Nat := [371285200532456360, 371285200314096854, 371285200405459338, 371285200415398683, 371285200613828056, 371285200812745200, 371285200895018286, 371285200896363074, 371285200545038011, 371285200592267570]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 40670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 40600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362456806289588895, 362456829816286732⟩, ⟨1153656660820336086, 1154303529909619804⟩, true⟩

def words08 : List Nat := [371285201022274249, 371285201023609630, 371285200649214808, 371285200263361073, 371285199877003101, 371285199632526515, 371285199085881894, 371285198782776484, 371285198479235387, 371285198052460476]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 40680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 40600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362498196628709745, 362498220167481802⟩, ⟨(-530796313082789220), (-530148952632733460)⟩, true⟩

def words09 : List Nat := [371285197356220322, 371285196910218895, 371285196619192938, 371285196620528819, 371285195973137727, 371285195232942687, 371285194492229673, 371285194355244714, 371285194393189802, 371285194714725538]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 40690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 40600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 40600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk406
