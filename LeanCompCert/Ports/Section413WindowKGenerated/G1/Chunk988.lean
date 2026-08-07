import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk988

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362481449355093136, 362481598130195343⟩, ⟨360969965389606640, 370893895494151388⟩, true⟩

def state01 : KState := ⟨⟨362495159485161336, 362495308291305511⟩, ⟨(-993638186764253521), (-983711189555495173)⟩, true⟩

def words00 : List Nat := [371285352145824553, 371285352178778222, 371285352285975815, 371285352394561869, 371285352474924325, 371285352478395870, 371285352486832912, 371285352545295084, 371285352704372580, 371285352808722039]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 98800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 98800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362486009148596702, 362486157986400370⟩, ⟨(-89419802356144453), (-79489676716497077)⟩, true⟩

def words01 : List Nat := [371285352912177171, 371285353016813030, 371285353151242148, 371285353240855486, 371285353359952991, 371285353480429376, 371285353599521200, 371285353602993095, 371285353593539964, 371285353605988145]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 98810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 98800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478986015392250, 362479134884111168⟩, ⟨604642247191243074, 614575428036803840⟩, true⟩

def words02 : List Nat := [371285353681121519, 371285353684593515, 371285353623482482, 371285353563453159, 371285353502041005, 371285353455241886, 371285353381321945, 371285353386480055, 371285353391373578, 371285353394968568]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 98820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 98800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487284921416509, 362487433821616684⟩, ⟨(-215596807781827335), (-205660515488057545)⟩, true⟩

def words03 : List Nat := [371285353345104028, 371285353360010190, 371285353415216687, 371285353418689184, 371285353337763094, 371285353224518079, 371285353109892398, 371285353099183446, 371285353075854870, 371285353100908800]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 98830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 98800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362482284593015094, 362482433524501413⟩, ⟨278622294192158806, 288561678971933836⟩, true⟩

def words04 : List Nat := [371285353120903887, 371285353124377082, 371285353022392479, 371285353007715586, 371285352997303924, 371285353000800509, 371285352917680346, 371285352815416779, 371285352711691536, 371285352711946754]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 98840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 98800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362473428923802195, 362473577886524908⟩, ⟨1154105065117237686, 1164047537776783130⟩, true⟩

def words05 : List Nat := [371285352733943943, 371285352786871425, 371285352836922273, 371285352840461299, 371285352822955243, 371285352816767448, 371285352823916996, 371285352827390285, 371285352708798936, 371285352593562910]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 98850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 98800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479485146570087, 362479634140418378⟩, ⟨555351705302862612, 565297255193785668⟩, true⟩

def words06 : List Nat := [371285352476857528, 371285352386352146, 371285352243297424, 371285352195576886, 371285352146765579, 371285352089229599, 371285351894221168, 371285351803412247, 371285351718041665, 371285351721638099]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 98860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 98800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478150642164820, 362478299667695730⟩, ⟨687329941186400011, 697278623694849787⟩, true⟩

def words07 : List Nat := [371285351666405248, 371285351612228621, 371285351600931884, 371285351604800007, 371285351601631259, 371285351606335874, 371285351608935570, 371285351604352407, 371285351500670386, 371285351433712062]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 98870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 98800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481494253967063, 362481643310452078⟩, ⟨356711465337701623, 366663208748572527⟩, true⟩

def words08 : List Nat := [371285351381606616, 371285351385142485, 371285351320406972, 371285351256901633, 371285351192096374, 371285351159504794, 371285351089219846, 371285351107851303, 371285351110500189, 371285351098992361]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 98880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 98800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362500010419323067, 362500159507171300⟩, ⟨(-1474460289040340086), (-1464505443965758900)⟩, true⟩

def words09 : List Nat := [371285351094094852, 371285351128485713, 371285351263352927, 371285351272187473, 371285351274881606, 371285351270338655, 371285351358119430, 371285351409404530, 371285351561488330, 371285351715096744]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 98890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 98800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 98800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk988
