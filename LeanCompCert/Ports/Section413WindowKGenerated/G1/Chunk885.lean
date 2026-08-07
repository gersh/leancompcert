import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk885

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362489416108544265, 362489534471372526⟩, ⟨(-392337220366784441), (-385264487998993285)⟩, true⟩

def state01 : KState := ⟨⟨362486134561118138, 362486252951470432⟩, ⟨(-101900957220827083), (-94825788839239393)⟩, true⟩

def words00 : List Nat := [371285181340620213, 371285181343719202, 371285181338645999, 371285181334679679, 371285181351352792, 371285181354810052, 371285181419242942, 371285181508296092, 371285181591493892, 371285181606791927]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 88500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 88500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362491365220008577, 362491483638243414⟩, ⟨(-564856278309870535), (-557778641901765917)⟩, true⟩

def words01 : List Nat := [371285181728839329, 371285181852529769, 371285182102035900, 371285182182493167, 371285182234103425, 371285182286580809, 371285182375491080, 371285182401933514, 371285182475215991, 371285182549892608]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 88510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 88500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482901223982284, 362483019670087810⟩, ⟨184418202452966296, 191498306117801556⟩, true⟩

def words02 : List Nat := [371285182619342014, 371285182622480403, 371285182674006383, 371285182766138186, 371285182895163230, 371285182898247822, 371285182857414000, 371285182807480037, 371285182756264205, 371285182759505158]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 88520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 88500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362469994288432450, 362470112762275935⟩, ⟨1327197895557667368, 1334280455002587490⟩, true⟩

def words03 : List Nat := [371285182823927779, 371285182914009787, 371285183004620457, 371285183007705496, 371285182928186223, 371285182889264874, 371285182873159893, 371285182876245035, 371285182733136040, 371285182566375807]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 88530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 88500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478025237675213, 362478143739175032⟩, ⟨616082506406875531, 623167514683039375⟩, true⟩

def words04 : List Nat := [371285182398267580, 371285182331563590, 371285182199580486, 371285182098305837, 371285181996028800, 371285181874468303, 371285181581998743, 371285181418476604, 371285181253389895, 371285181204050053]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 88540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 88500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362471105092767644, 362471223622412128⟩, ⟨1228928386968346640, 1236015887592168400⟩, true⟩

def words05 : List Nat := [371285181126904344, 371285181051409824, 371285180976514221, 371285180979914768, 371285180920282173, 371285180894387611, 371285180867503204, 371285180816716100, 371285180595068432, 371285180441377713]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 88550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 88500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362462446854335724, 362462565411444797⟩, ⟨1995725838488149978, 2002815771521565974⟩, true⟩

def words06 : List Nat := [371285180285889268, 371285180176195646, 371285179895863991, 371285179610980444, 371285179324890733, 371285179078976330, 371285178780962005, 371285178592369726, 371285178402744388, 371285178212297474]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 88560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 88500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477030020390763, 362477148605412772⟩, ⟨703988625780299593, 711081031197616953⟩, true⟩

def words07 : List Nat := [371285177959119803, 371285177760531623, 371285177560357675, 371285177452703748, 371285177191796461, 371285176911682030, 371285176630272642, 371285176459267964, 371285176249961020, 371285176162775581]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 88570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 88500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362464801135003339, 362464919747829143⟩, ⟨1787247685719972099, 1794342554145101649⟩, true⟩

def words08 : List Nat := [371285176074458636, 371285175986915658, 371285175776365380, 371285175632779420, 371285175487679634, 371285175349284629, 371285175040384999, 371285174720574118, 371285174399541461, 371285174207182853]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 88580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 88500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362460285832849346, 362460404473552948⟩, ⟨2187343827842716687, 2194441166100379939⟩, true⟩

def words09 : List Nat := [371285173980647133, 371285173882708405, 371285173783628094, 371285173685337883, 371285173471912603, 371285173271071055, 371285173068630630, 371285172961179488, 371285172708588181, 371285172432538280]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 88590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 88500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 88500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk885
