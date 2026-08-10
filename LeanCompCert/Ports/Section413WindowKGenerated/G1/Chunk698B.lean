import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk698A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk698B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk698A

def state06 : KState := ⟨⟨362488398334036027, 362488470751843660⟩, ⟨(-220810912207275053), (-217394170015480965)⟩, true⟩

def words05 : List Nat := [371285359820362665, 371285359807863024, 371285359807877268, 371285359810269165, 371285359582823669, 371285359323438621, 371285359063052126, 371285359008175622, 371285358894423744, 371285358941677538]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 69850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 69800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362475024218009453, 362475096657370671⟩, ⟨713524100249865949, 716942348284805413⟩, true⟩

def words06 : List Nat := [371285358944786327, 371285358947189362, 371285358754694962, 371285358714588741, 371285358673278311, 371285358674715327, 371285358423204136, 371285358135556873, 371285357846966120, 371285357747227331]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 69860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 69800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477245290375738, 362477317751299871⟩, ⟨558397416673973162, 561817171419507370⟩, true⟩

def words07 : List Nat := [371285357641905505, 371285357684462870, 371285357726579011, 371285357729019020, 371285357649540252, 371285357605265010, 371285357716958200, 371285357719350379, 371285357605649581, 371285357493306447]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 69870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 69800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477540266178202, 362477612748556868⟩, ⟨537779730311847750, 541200984404777148⟩, true⟩

def words08 : List Nat := [371285357379908504, 371285357318536846, 371285357178394114, 371285357145346676, 371285357111594046, 371285357045623222, 371285356732679602, 371285356551709770, 371285356369405273, 371285356359723055]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 69880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 69800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478344299007640, 362478416803127494⟩, ⟨481600406602587074, 485023180299120508⟩, true⟩

def words09 : List Nat := [371285356250715902, 371285356142979543, 371285356084366719, 371285356087046029, 371285356067575975, 371285356056718940, 371285356045035395, 371285356016478222, 371285355714625102, 371285355618296295]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 69890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 69800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 69800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk698B
