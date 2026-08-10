import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk597A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk597B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk597A

def state06 : KState := ⟨⟨362488534461888463, 362488586807542914⟩, ⟨(-208920749671201285), (-206807714487705189)⟩, true⟩

def words05 : List Nat := [371285124249192319, 371285124419530608, 371285124869629919, 371285125202774429, 371285125522738413, 371285125843439690, 371285126162167491, 371285126164189541, 371285126167194410, 371285126227658245]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 59750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 59700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475318211782973, 362475370575431489⟩, ⟨580951560966851663, 583065671570291473⟩, true⟩

def words06 : List Nat := [371285126471291089, 371285126473313221, 371285126343636582, 371285126163235206, 371285125982083861, 371285125885808333, 371285125709921103, 371285125736490090, 371285125738017604, 371285125731388831]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 59760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 59700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362508846514948199, 362508898896902781⟩, ⟨(-1423198329332314484), (-1421083124485419138)⟩, true⟩

def words07 : List Nat := [371285125686782012, 371285125806412377, 371285126039302667, 371285126140366668, 371285126193779568, 371285126247847256, 371285126493704965, 371285126613265150, 371285127012300098, 371285127412242347]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 59770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 59700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489011911465075, 362489064311640521⟩, ⟨(-237413101276758356), (-235296807092207084)⟩, true⟩

def words08 : List Nat := [371285127810162499, 371285127874328108, 371285128196059969, 371285128518848221, 371285128855335223, 371285128857358215, 371285128855504823, 371285128820469358, 371285128922026189, 371285128990152468]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 59780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 59700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362495629827619247, 362495682246042070⟩, ⟨(-633060770561636152), (-630943385277068344)⟩, true⟩

def words09 : List Nat := [371285129337588447, 371285129685863270, 371285130027063260, 371285130137395503, 371285130331106952, 371285130525828573, 371285130999682969, 371285131173050756, 371285131351003940, 371285131529745068]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 59790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 59700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 59700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk597B
