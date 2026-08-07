import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk652

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362470348058097805, 362470410797160884⟩, ⟨982508594333380158, 985271451371314266⟩, true⟩

def state01 : KState := ⟨⟨362484590910422046, 362484653669348771⟩, ⟨53854378259804091, 56618530506554757⟩, true⟩

def words00 : List Nat := [371285522092226746, 371285522078065518, 371285522046518759, 371285522149905230, 371285522182427448, 371285522184648048, 371285521903588635, 371285521842091402, 371285521916252823, 371285521918551448]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 65200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 65200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478334409606122, 362478397188759049⟩, ⟨461947698777384071, 464713170079004463⟩, true⟩

def words01 : List Nat := [371285521906897183, 371285521895824578, 371285522105275623, 371285522211866057, 371285522389543342, 371285522568097324, 371285522745699699, 371285522747920607, 371285522612214313, 371285522505687584]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 65210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 65200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362467053383910336, 362467116182842496⟩, ⟨1197737560225760031, 1200504321632009075⟩, true⟩

def words02 : List Nat := [371285522397953992, 371285522395390676, 371285522079129657, 371285521763487049, 371285521446983925, 371285521200950897, 371285520868912576, 371285520708794920, 371285520547953653, 371285520357633728]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 65220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 65200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485580781381270, 362485643600436659⟩, ⟨(-10940542227892332), (-8172468084862870)⟩, true⟩

def words03 : List Nat := [371285520077004244, 371285519901816109, 371285519725451037, 371285519647290199, 371285519351340528, 371285519018966079, 371285518685717718, 371285518559540939, 371285518330125919, 371285518334605589]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 65230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 65200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362476420567329640, 362476483406441895⟩, ⟨586648284626468358, 589417667380264222⟩, true⟩

def words04 : List Nat := [371285518336293417, 371285518298627674, 371285517947285977, 371285517797790989, 371285517647226535, 371285517569298531, 371285517312964523, 371285517016972265, 371285516720054184, 371285516627397915]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 65240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 65200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362477659009956474, 362477721869045954⟩, ⟨505889570844908227, 508660257216403609⟩, true⟩

def words05 : List Nat := [371285516522386435, 371285516556709744, 371285516590184321, 371285516592446101, 371285516459472119, 371285516385284127, 371285516467654022, 371285516469876907, 371285516350954879, 371285516234004833]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 65250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 65200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362480189489378811, 362480252368388324⟩, ⟨340718126056061247, 343490112508174493⟩, true⟩

def words06 : List Nat := [371285516116105146, 371285516096678631, 371285515971662533, 371285515898240001, 371285515824102448, 371285515716323522, 371285515295118922, 371285515109644189, 371285514969311867, 371285514971613515]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 65260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 65200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362479406038330283, 362479468937610835⟩, ⟨391883259304284669, 394656568944754727⟩, true⟩

def words07 : List Nat := [371285514892648462, 371285514814393805, 371285514809851797, 371285514821811936, 371285514843280538, 371285514865550609, 371285514886864548, 371285514889088213, 371285514624377830, 371285514534561582]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 65270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 65200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477222043167466, 362477284962276279⟩, ⟨534512964094139716, 537287568226066440⟩, true⟩

def words08 : List Nat := [371285514550477480, 371285514552739866, 371285514466431644, 371285514374685479, 371285514282116311, 371285514200561997, 371285514108935685, 371285514181991279, 371285514207458260, 371285514209760214]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 65280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 65200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362491216794105905, 362491279733294307⟩, ⟨(-379238634720404714), (-376462719489524510)⟩, true⟩

def words09 : List Nat := [371285514170270973, 371285514257946600, 371285514578837064, 371285514587979937, 371285514589717044, 371285514560095971, 371285514579653339, 371285514582104075, 371285514604941453, 371285514695706988]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 65290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 65200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 65200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk652
