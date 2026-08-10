import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk936A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk936B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk936A

def state06 : KState := ⟨⟨362485711580252399, 362485844729477845⟩, ⟨(-72766686369691188), (-64346817346021132)⟩, true⟩

def words05 : List Nat := [371285157469339967, 371285157513248946, 371285157575462395, 371285157601786696, 371285157661437132, 371285157722377462, 371285157781874334, 371285157785152466, 371285157699786345, 371285157711216819]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 93650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 93600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477129113528710, 362477262291931274⟩, ⟨731112712860356931, 739535314765505015⟩, true⟩

def words06 : List Nat := [371285157821970463, 371285157825248855, 371285157784298816, 371285157743407397, 371285157701240637, 371285157656272992, 371285157557547588, 371285157507449788, 371285157456274569, 371285157405785929]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 93660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 93600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498972164819856, 362499105372899352⟩, ⟨(-1315029609719752800), (-1306604227824780560)⟩, true⟩

def words07 : List Nat := [371285157334876944, 371285157350020628, 371285157469283431, 371285157494879240, 371285157501359133, 371285157508852119, 371285157621495232, 371285157692141442, 371285157843254249, 371285157995866392]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 93670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 93600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362485194616545241, 362485327854256549⟩, ⟨(-24303314255205835), (-15875156303501403)⟩, true⟩

def words08 : List Nat := [371285158123700079, 371285158126982003, 371285158236114285, 371285158350443326, 371285158481411408, 371285158484691118, 371285158473484772, 371285158425289007, 371285158407031554, 371285158412620709]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 93680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 93600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478080646544505, 362478213913731459⟩, ⟨642267594911493276, 650698514586417800⟩, true⟩

def words09 : List Nat := [371285158492064853, 371285158572803638, 371285158652208327, 371285158655488552, 371285158597115678, 371285158545301526, 371285158529942720, 371285158533245059, 371285158472070050, 371285158401613919]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 93690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 93600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 93600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk936B
