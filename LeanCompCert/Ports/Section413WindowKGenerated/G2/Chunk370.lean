import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk370

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360561344323983991, 360561352703121512⟩, ⟨748299615058295951, 748509189662302005⟩, true⟩

def state01 : KState := ⟨⟨360586482070658921, 360586490454504307⟩, ⟨(-181712472364594625), (-181502723546046259)⟩, true⟩

def words00 : List Nat := [360581582134881974, 360581582665950172, 360581583943115813, 360581585220311619, 360581585881215502, 360581585881713846, 360581586083842720, 360581586354679100, 360581586355090111, 360581586433441757]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 37000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 37000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360588246636839287, 360588255025427749⟩, ⟨(-247054701080279293), (-246844776696895435)⟩, true⟩

def words01 : List Nat := [360581586433887795, 360581586096431433, 360581586150353662, 360581586936977140, 360581587254063097, 360581587571219139, 360581587571667661, 360581587517260823, 360581587148665767, 360581587329344529]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 37010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 37000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360615264822033604, 360615273215325505⟩, ⟨(-1247521945439918801), (-1247311846912481705)⟩, true⟩

def words02 : List Nat := [360581588239018331, 360581588623358546, 360581588623810581, 360581588338459311, 360581588053040178, 360581587750198137, 360581588421033352, 360581589091927765, 360581589395007480, 360581590305144509]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 37020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 37000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360607393346193465, 360607401744187743⟩, ⟨(-956055560555960042), (-955845287875782014)⟩, true⟩

def words03 : List Nat := [360581591526137052, 360581592747208852, 360581594350720765, 360581595226447514, 360581595471863161, 360581595717300547, 360581595717715673, 360581595319824731, 360581595985359580, 360581596682556692]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 37030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 37000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360570314650410383, 360570323053157069⟩, ⟨417246959850473194, 417457408581938814⟩, true⟩

def words04 : List Nat := [360581597012398742, 360581597012897589, 360581596615182900, 360581596457982926, 360581596300644577, 360581595823030494, 360581594617967144, 360581592989117010, 360581591360256003, 360581590459596528]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 37040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 37000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360528399628403738, 360528408035852295⟩, ⟨1970348676957597873, 1970559299917312931⟩, true⟩

def words05 : List Nat := [360581590155901769, 360581589644932032, 360581589133940013, 360581588151571109, 360581586695246764, 360581585052015585, 360581583408727021, 360581582493300969, 360581581604505649, 360581580170226751]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 37050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 37000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588582598612111, 360588591010770472⟩, ⟨(-260316139910657566), (-260105342382313702)⟩, true⟩

def words06 : List Nat := [360581578735910993, 360581578029403300, 360581577809989037, 360581577806447781, 360581577802875434, 360581577096686940, 360581575957217987, 360581575338230177, 360581574719130497, 360581574600574300]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 37060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 37000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360560108756157062, 360560117173078606⟩, ⟨795477676068764583, 795688650191470975⟩, true⟩

def words07 : List Nat := [360581574601023596, 360581574418134888, 360581574616426078, 360581575485671443, 360581576162662168, 360581576839700811, 360581577009039464, 360581577009538884, 360581576452694850, 360581575874540081]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 37070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 37000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360551830666709503, 360551839088332288⟩, ⟨1102333262724422598, 1102544411192940616⟩, true⟩

def words08 : List Nat := [360581575296248632, 360581574823782028, 360581573625226327, 360581572001025636, 360581570376830990, 360581568566261444, 360581567315354556, 360581566790991205, 360581566266606648, 360581565278981869]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 37080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 37000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360587501301597833, 360587509727942470⟩, ⟨(-220971498469911142), (-220760174845042258)⟩, true⟩

def words09 : List Nat := [360581564477946745, 360581564059725366, 360581563641383727, 360581563191036709, 360581562505573404, 360581561206750715, 360581559907902443, 360581559335289710, 360581559318390296, 360581559479301058]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 37090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 37000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 37000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk370
