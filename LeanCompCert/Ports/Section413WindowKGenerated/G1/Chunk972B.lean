import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk972A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk972B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk972A

def state06 : KState := ⟨⟨362487829940699980, 362487973940695671⟩, ⟨(-265952990145951153), (-256497174460234585)⟩, true⟩

def words05 : List Nat := [371285336672933824, 371285336656544704, 371285336688224673, 371285336692025088, 371285336713101867, 371285336738609264, 371285336750398464, 371285336753871302, 371285336704606035, 371285336735912046]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 97250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 97200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484638570591813, 362484782600969215⟩, ⟨44470639755629923, 53929410524837701⟩, true⟩

def words06 : List Nat := [371285336843053726, 371285336856581080, 371285336861460877, 371285336867515032, 371285336875689384, 371285336879474365, 371285336913780769, 371285336971344603, 371285337027479836, 371285337031014706]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 97260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 97200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362492610229981560, 362492754291318281⟩, ⟨(-730956123001511491), (-721494340670567051)⟩, true⟩

def words07 : List Nat := [371285337120094507, 371285337216785621, 371285337347036177, 371285337370100068, 371285337374665770, 371285337380261787, 371285337478552611, 371285337531793085, 371285337610400996, 371285337690536314]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 97270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 97200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362492493320136523, 362492637412271315⟩, ⟨(-719623142013450874), (-710158363490255072)⟩, true⟩

def words08 : List Nat := [371285337769383535, 371285337772798013, 371285337774260471, 371285337830789436, 371285337917447595, 371285337920921679, 371285337919856078, 371285337919679621, 371285338011030294, 371285338089995974]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 97280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 97200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362473885375758168, 362474029498657067⟩, ⟨1090855514714783259, 1100323286434783099⟩, true⟩

def words09 : List Nat := [371285338207158191, 371285338325688652, 371285338416516835, 371285338419931541, 371285338369745159, 371285338310043569, 371285338279223448, 371285338282638304, 371285338175101003, 371285338062751978]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 97290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 97200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 97200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk972B
