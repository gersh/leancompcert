import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk724A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk724B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk724A

def state06 : KState := ⟨⟨362467664495602892, 362467742626338452⟩, ⟨1266550465974505022, 1270373789271770036⟩, true⟩

def words05 : List Nat := [371285274805755945, 371285274971708454, 371285275137552203, 371285275140046075, 371285275118201948, 371285275129342319, 371285275157951625, 371285275160438869, 371285274935485831, 371285274696298041]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 72450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 72400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491058744463435, 362491136897474817⟩, ⟨(-428675143733672437), (-424850206218056149)⟩, true⟩

def words06 : List Nat := [371285274456033246, 371285274407051648, 371285274336133360, 371285274388903781, 371285274409820551, 371285274412313472, 371285274247586177, 371285274262472874, 371285274466222839, 371285274549691317]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 72460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 72400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362488264100115852, 362488342275843975⟩, ⟨(-226141083273544507), (-222314499362869869)⟩, true⟩

def words07 : List Nat := [371285274563080269, 371285274577291218, 371285274715867948, 371285274775459272, 371285274857784363, 371285274941027272, 371285275022400424, 371285275024933729, 371285275019698154, 371285275065135474]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 72470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 72400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483406867037443, 362483485064913591⟩, ⟨125940170459000899, 129768359773277863⟩, true⟩

def words08 : List Nat := [371285275299256566, 371285275301744580, 371285275282477337, 371285275247422401, 371285275211472445, 371285275186299295, 371285275114818144, 371285275166841403, 371285275217649036, 371285275220242234]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 72480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 72400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362504157764757491, 362504235985110629⟩, ⟨(-1378371327632795190), (-1374541508848282392)⟩, true⟩

def words09 : List Nat := [371285275338123147, 371285275482008948, 371285275814623327, 371285275921744877, 371285275998154284, 371285276075353189, 371285276341534907, 371285276525879722, 371285276789106996, 371285277053387642]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 72490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 72400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 72400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk724B
