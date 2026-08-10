import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk630A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk630B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk630A

def state06 : KState := ⟨⟨362486032350583359, 362486090885178166⟩, ⟨(-45014712803431984), (-42521515732462442)⟩, true⟩

def words05 : List Nat := [371285416763760429, 371285416681106714, 371285416671891023, 371285416674274881, 371285416701450934, 371285416754847299, 371285416806596909, 371285416808739543, 371285416580048508, 371285416593369720]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 63050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 63000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481050496799529, 362481109050489660⟩, ⟨269137642656950519, 271632043977757191⟩, true⟩

def words06 : List Nat := [371285416787818176, 371285416789960064, 371285416649535789, 371285416438107447, 371285416225846708, 371285416090810053, 371285415860161276, 371285415872140655, 371285415882601033, 371285415884863812]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 63060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 63000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362510691601748742, 362510750174828854⟩, ⟨(-1600456257003743328), (-1597960632662889554)⟩, true⟩

def words07 : List Nat := [371285415956260486, 371285416097106177, 371285416488172789, 371285416706305664, 371285416879459482, 371285417053262950, 371285417330227406, 371285417482843399, 371285417885893142, 371285418289908468]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 63070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 63000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482534784511384, 362482593376940080⟩, ⟨175795650758788191, 178292495708456975⟩, true⟩

def words08 : List Nat := [371285418673530443, 371285418722805938, 371285419011750315, 371285419301816692, 371285419582201477, 371285419584344502, 371285419530001770, 371285419445808703, 371285419376940990, 371285419379408118]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 63080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 63000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362473715757144262, 362473774368857387⟩, ⟨732250650418692079, 734748712122647125⟩, true⟩

def words09 : List Nat := [371285419395317149, 371285419456843726, 371285419516860950, 371285419519004164, 371285419244199364, 371285419046858214, 371285418899621187, 371285418901801823, 371285418746126574, 371285418563978190]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 63090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 63000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 63000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk630B
