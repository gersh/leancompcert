import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk820A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362478828026624819, 362478929045318546⟩, ⟨510822734989859349, 516416105867608583⟩, true⟩

def state01 : KState := ⟨⟨362493784681185137, 362493885725294768⟩, ⟨(-715673998710395525), (-710078543603481683)⟩, true⟩

def words00 : List Nat := [371285226774335806, 371285226777466155, 371285226891333747, 371285227024739606, 371285227103076512, 371285227105917158, 371285227044427160, 371285227090542792, 371285227283826307, 371285227392344268]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 82000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 82000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494318558930636, 362494419628921879⟩, ⟨(-759424321091822111), (-753826743301466663)⟩, true⟩

def words01 : List Nat := [371285227499991540, 371285227608626164, 371285227864765316, 371285228047863141, 371285228261866432, 371285228477013719, 371285228690303565, 371285228744002930, 371285228858020006, 371285228973561649]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 82010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 82000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486732639724511, 362486833735023947⟩, ⟨(-137169157552032016), (-131569503853720252)⟩, true⟩

def words02 : List Nat := [371285229236211998, 371285229301645505, 371285229360212735, 371285229419758986, 371285229494019594, 371285229520992265, 371285229622334912, 371285229724792849, 371285229812723575, 371285229835231750]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 82020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 82000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362506367812551963, 362506468933579365⟩, ⟨(-1747961815426293710), (-1742360051131373306)⟩, true⟩

def words03 : List Nat := [371285230005348353, 371285230176973068, 371285230408318968, 371285230442471543, 371285230452841654, 371285230464049975, 371285230622740926, 371285230736162573, 371285230996965742, 371285231259110120]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 82030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 82000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489885302781670, 362489986449446398⟩, ⟨(-395665923638066619), (-390062055927687129)⟩, true⟩

def words04 : List Nat := [371285231487750015, 371285231607083987, 371285231824266378, 371285232042910944, 371285232292537053, 371285232344989816, 371285232368072946, 371285232392119295, 371285232490613249, 371285232551798257]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 82040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 82000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk820A
