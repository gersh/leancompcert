import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk944A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk944B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk944A

def state06 : KState := ⟨⟨362496452985848577, 362496588508340669⟩, ⟨(-1086882877845737396), (-1078239777666327766)⟩, true⟩

def words05 : List Nat := [371285173209249900, 371285173293780528, 371285173459348211, 371285173490014746, 371285173501495956, 371285173514013253, 371285173572763170, 371285173605178390, 371285173728265826, 371285173852793234]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 94450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 94400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485122577680245, 362485258130016425⟩, ⟨(-16586357657001656), (-7940438259883134)⟩, true⟩

def words06 : List Nat := [371285173959346281, 371285173962655447, 371285174018597348, 371285174105572215, 371285174196567706, 371285174199876681, 371285174151333404, 371285174103585530, 371285174073754174, 371285174078421122]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 94460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 94400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362473920034488468, 362474055616673894⟩, ⟨1041813262434440488, 1050462001843653882⟩, true⟩

def words07 : List Nat := [371285174144122840, 371285174211253042, 371285174276247654, 371285174279556997, 371285174195023194, 371285174146389372, 371285174155642650, 371285174158952340, 371285174083701420, 371285173969784009]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 94470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 94400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362494155136112724, 362494290747930551⟩, ⟨(-870080174516877284), (-861428635290944666)⟩, true⟩

def words08 : List Nat := [371285173854349764, 371285173841164994, 371285173834608221, 371285173889846713, 371285173926801145, 371285173930177987, 371285173940952542, 371285173990240835, 371285174132825374, 371285174232756715]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 94480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 94400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362493330032113822, 362493465674110134⟩, ⟨(-792110775527642464), (-783456384589581748)⟩, true⟩

def words09 : List Nat := [371285174332108172, 371285174432523092, 371285174578107403, 371285174669217192, 371285174792827674, 371285174917751287, 371285175041416919, 371285175044729000, 371285175126175152, 371285175218087557]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 94490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 94400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 94400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk944B
