import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk993A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk993B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk993A

def state06 : KState := ⟨⟨360582708979846868, 360582774372922890⟩, ⟨(-38870103685789517), (-34482854686458943)⟩, true⟩

def words05 : List Nat := [360582427577727539, 360582427478800181, 360582427379588128, 360582427395797967, 360582427397007497, 360582427396162254, 360582427395158940, 360582427343638111, 360582427321590761, 360582427326750987]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 99350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 99300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360576944078193711, 360577009484858134⟩, ⟨533915653984313861, 538304253197041377⟩, true⟩

def words06 : List Nat := [360582427403504011, 360582427404948592, 360582427380831644, 360582427280344282, 360582427179647638, 360582426985771789, 360582426842007997, 360582426799737627, 360582426757322647, 360582426655565562]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 99360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 99300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360598114742464800, 360598180162785692⟩, ⟨(-1569903165717995635), (-1565513209395077401)⟩, true⟩

def words07 : List Nat := [360582426648912374, 360582426697233435, 360582426810210941, 360582426907956819, 360582426918105524, 360582426928364608, 360582427039541494, 360582427202138880, 360582427361839375, 360582427521844315]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 99370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 99300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360595610231961287, 360595675666042114⟩, ⟨(-1321066845141636654), (-1316675521289715696)⟩, true⟩

def words08 : List Nat := [360582427623380612, 360582427738031819, 360582427850921097, 360582427964230776, 360582427990464358, 360582428045644845, 360582428048622222, 360582428051744018, 360582428099031874, 360582428233967885]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 99380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 99300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360584013711171899, 360584079158883843⟩, ⟨(-168400203258189923), (-164007524541852173)⟩, true⟩

def words09 : List Nat := [360582428469587365, 360582428705479334, 360582428863315193, 360582428920341892, 360582428938149914, 360582428956366852, 360582429075292623, 360582429164373170, 360582429182263518, 360582429200387029]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 99390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 99300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 99300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk993B
