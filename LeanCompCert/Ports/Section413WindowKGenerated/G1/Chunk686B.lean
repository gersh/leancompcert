import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk686A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk686B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk686A

def state06 : KState := ⟨⟨362481976155284529, 362482046012093880⟩, ⟨230290177275018098, 233529539795818070⟩, true⟩

def words05 : List Nat := [371285449001018296, 371285448849185422, 371285448696147737, 371285448684084050, 371285448388903276, 371285448053568531, 371285447717212947, 371285447564595086, 371285447304863455, 371285447257940018]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 68650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 68600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475946013858163, 362476015891895150⟩, ⟨644280429920999394, 647521250039555900⟩, true⟩

def words06 : List Nat := [371285447210175777, 371285447162526719, 371285446923938869, 371285446718118058, 371285446511123219, 371285446362098509, 371285446062603749, 371285445756475138, 371285445449421372, 371285445355271291]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 68660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 68600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362457117117201742, 362457187016385712⟩, ⟨1937413502992925256, 1940655775380936438⟩, true⟩

def words07 : List Nat := [371285445258057338, 371285445299147931, 371285445300914659, 371285445299353616, 371285445014661537, 371285444753335543, 371285444490852972, 371285444318172181, 371285443915761713, 371285443506999879]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 68670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 68600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476681991747458, 362476751911950555⟩, ⟨593641435331443826, 596885151418744622⟩, true⟩

def words08 : List Nat := [371285443097176029, 371285442879484030, 371285442554771106, 371285442442710164, 371285442329884897, 371285442194801899, 371285441805077040, 371285441628271249, 371285441458965148, 371285441461396162]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 68680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 68600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481355511773557, 362481425453360927⟩, ⟨272580066803258128, 275825251885570616⟩, true⟩

def words09 : List Nat := [371285441336680125, 371285441168738672, 371285441018054737, 371285441020642726, 371285440939815685, 371285440868505420, 371285440796402369, 371285440700943428, 371285440432525519, 371285440376969160]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 68690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 68600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 68600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk686B
