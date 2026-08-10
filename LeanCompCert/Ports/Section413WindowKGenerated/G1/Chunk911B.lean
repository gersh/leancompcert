import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk911A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk911B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk911A

def state06 : KState := ⟨⟨362496522995855177, 362496648867577565⟩, ⟨(-1059984679270271837), (-1052237369168676897)⟩, true⟩

def words05 : List Nat := [371285105751386923, 371285105746265566, 371285105850666075, 371285105887968591, 371285105895317390, 371285105903644544, 371285105972246511, 371285105982124883, 371285106110906272, 371285106241134584]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 91150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 91100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488519548454597, 362488645448973993⟩, ⟨(-330376487925487112), (-322626552544159418)⟩, true⟩

def words06 : List Nat := [371285106345361144, 371285106348552232, 371285106425422789, 371285106526677090, 371285106663248155, 371285106666432874, 371285106657502679, 371285106649697057, 371285106709400816, 371285106751882329]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 91160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 91100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362472845251506732, 362472971180626032⟩, ⟨1098763880002757158, 1106516422983579854⟩, true⟩

def words07 : List Nat := [371285106850757539, 371285106950895573, 371285107049900829, 371285107053085395, 371285106991687533, 371285106937353333, 371285106931499580, 371285106934684203, 371285106826984796, 371285106697438750]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 91170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 91100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483277955201314, 362483403912884707⟩, ⟨147499157678844105, 155254305276952043⟩, true⟩

def words08 : List Nat := [371285106566510334, 371285106525229590, 371285106495521220, 371285106543179362, 371285106570526553, 371285106573711834, 371285106453598285, 371285106436557625, 371285106446084852, 371285106449404907]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 91180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 91100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485467225571155, 362485593212288661⟩, ⟨(-52137111259131682), (-44379315897299682)⟩, true⟩

def words09 : List Nat := [371285106433115803, 371285106419243196, 371285106506850997, 371285106553150600, 371285106600607895, 371285106649301314, 371285106697105542, 371285106700291159, 371285106592973440, 371285106602318406]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 91190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 91100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 91100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk911B
