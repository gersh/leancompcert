import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk800A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362504178110248092, 362504274079236944⟩, ⟨(-1533251376021457301), (-1528067054241300161)⟩, true⟩

def state01 : KState := ⟨⟨362492432627168965, 362492528621156343⟩, ⟨(-593588443996078706), (-588402122207829070)⟩, true⟩

def words00 : List Nat := [371285173721441706, 371285173854128547, 371285174004894968, 371285174157016715, 371285174355802588, 371285174366062727, 371285174375537149, 371285174385970619, 371285174510651833, 371285174605805856]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 80000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 80000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362473898144036253, 362473994162884019⟩, ⟨889512156470906985, 894700467468743571⟩, true⟩

def words01 : List Nat := [371285174784597183, 371285174964481816, 371285175135054764, 371285175166343467, 371285175225439796, 371285175285931144, 371285175375610196, 371285175378376191, 371285175260134462, 371285175123487228]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 80010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 80000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484783084828904, 362484879128435982⟩, ⟨18477531155003610, 23667823515680966⟩, true⟩

def words02 : List Nat := [371285175001985166, 371285175005033529, 371285175012449577, 371285175082737973, 371285175092593330, 371285175095359499, 371285174896875384, 371285174839348458, 371285174862463979, 371285174865328594]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 80020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 80000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362492202354136932, 362492298423006789⟩, ⟨(-575342184178203289), (-570149869914190883)⟩, true⟩

def words03 : List Nat := [371285174863738696, 371285174819865352, 371285174867741254, 371285174885693571, 371285174950521520, 371285175016411180, 371285175081124859, 371285175083939795, 371285175107827387, 371285175200284507]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 80030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 80000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474885578139364, 362474981671634367⟩, ⟨810797557811036370, 815991843202895852⟩, true⟩

def words04 : List Nat := [371285175369394735, 371285175372163700, 371285175365808553, 371285175360277588, 371285175353745829, 371285175355136505, 371285175277628092, 371285175251729650, 371285175224860993, 371285175198719975]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 80040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 80000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk800A
