import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk799

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362472251753848180, 362472347473912348⟩, ⟨1019857358604222607, 1025021778837527749⟩, true⟩

def state01 : KState := ⟨⟨362487551819614645, 362487647564375909⟩, ⟨(-202649202232790404), (-197482808574896670)⟩, true⟩

def words00 : List Nat := [371285176123472339, 371285176122533189, 371285176143298058, 371285176234066930, 371285176285582937, 371285176288344524, 371285176130875420, 371285176131331149, 371285176246179250, 371285176279964816]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 79900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 79900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362483831029325644, 362483926799344608⟩, ⟨94741138329085342, 99909550452710706⟩, true⟩

def words01 : List Nat := [371285176314182051, 371285176349378855, 371285176526406492, 371285176645968839, 371285176769997710, 371285176895043242, 371285176999806008, 371285177002570286, 371285176930988784, 371285176918844768]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 79910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 79900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362481120429119243, 362481216223735522⟩, ⟨311403091324333932, 316573469390971356⟩, true⟩

def words02 : List Nat := [371285177026522333, 371285177029284803, 371285176962604083, 371285176896757048, 371285176829866252, 371285176781487344, 371285176746257731, 371285176802215274, 371285176854797520, 371285176857657591]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 79920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 79900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489770035161280, 362489865854762185⟩, ⟨(-380005814657228991), (-374833439440568819)⟩, true⟩

def words03 : List Nat := [371285176894028993, 371285176981351217, 371285177107095066, 371285177109865527, 371285177075626970, 371285177023816598, 371285176970865950, 371285176954143587, 371285176916936406, 371285176978723100]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 79930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 79900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478329947214190, 362478425791725026⟩, ⟨534534365735019296, 539708732376921502⟩, true⟩

def words04 : List Nat := [371285177039365778, 371285177042128875, 371285176900554393, 371285176910350550, 371285176946256312, 371285176949019897, 371285176795985897, 371285176610856187, 371285176424608151, 371285176369991154]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 79940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 79900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362469437740831518, 362469533610240641⟩, ⟨1245567726064232088, 1250744083454219352⟩, true⟩

def words05 : List Nat := [371285176301955727, 371285176319516458, 371285176323280426, 371285176326092082, 371285176199890778, 371285176123095145, 371285176086635017, 371285176089398572, 371285175924841293, 371285175732344871]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 79950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 79900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477249529851798, 362477345424041127⟩, ⟨620884211489137349, 626062550428007217⟩, true⟩

def words06 : List Nat := [371285175538630181, 371285175410725840, 371285175203521918, 371285175101084925, 371285174997835299, 371285174871080724, 371285174535082293, 371285174356907645, 371285174177195303, 371285174141690596]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 79960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 79900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478204089465899, 362478300008775808⟩, ⟨544553813194257871, 549734161151861537⟩, true⟩

def words07 : List Nat := [371285174045870320, 371285173930315907, 371285173851386457, 371285173854464034, 371285173815915373, 371285173787487764, 371285173758088967, 371285173726978563, 371285173486681570, 371285173404139048]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 79970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 79900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476108468625912, 362476204412586019⟩, ⟨712189550336247396, 717371869946724596⟩, true⟩

def words08 : List Nat := [371285173320088868, 371285173317984094, 371285173213863251, 371285173110475937, 371285173006001133, 371285172914571844, 371285172743884760, 371285172730503517, 371285172716260275, 371285172681994030]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 79980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 79900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362504178110248092, 362504274079236944⟩, ⟨(-1533251376021457301), (-1528067054241300161)⟩, true⟩

def words09 : List Nat := [371285172578175895, 371285172587985472, 371285172738306131, 371285172761916797, 371285172764056684, 371285172762580615, 371285172911602991, 371285172997268146, 371285173237907106, 371285173479816421]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 79990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 79900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 79900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk799
