import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk972

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362490435967682470, 362490579783309327⟩, ⟨(-519353040605264268), (-509915151133693104)⟩, true⟩

def state01 : KState := ⟨⟨362485390995000664, 362485534841030055⟩, ⟨(-28919612649680466), (-19478767891912768)⟩, true⟩

def words00 : List Nat := [371285333922452719, 371285333974420680, 371285334025132563, 371285334076973575, 371285334159386652, 371285334199726878, 371285334292801990, 371285334387282792, 371285334459266697, 371285334464859746]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 97200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 97200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362506937952956673, 362507081829796307⟩, ⟨(-2123613491746986447), (-2114169651769874617)⟩, true⟩

def words01 : List Nat := [371285334549671370, 371285334636213679, 371285334826937179, 371285334917784080, 371285334991758800, 371285335066913894, 371285335229848228, 371285335357952375, 371285335583948449, 371285335811428158]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 97210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 97200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486117639915322, 362486261547561306⟩, ⟨(-99403937573458105), (-89957102444386797)⟩, true⟩

def words02 : List Nat := [371285336028407458, 371285336105190553, 371285336181723941, 371285336260003947, 371285336369175011, 371285336372587066, 371285336353170151, 371285336333913524, 371285336344562553, 371285336358038990]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 97220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 97200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475944707274793, 362476088645670150⟩, ⟨889823237753953520, 899273062794644064⟩, true⟩

def words03 : List Nat := [371285336475744012, 371285336594882493, 371285336712489372, 371285336715902427, 371285336727320122, 371285336751831554, 371285336800406407, 371285336803818933, 371285336711584915, 371285336620400659]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 97230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 97200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486837522242022, 362486981491157894⟩, ⟨(-169413264217809311), (-159960471206214735)⟩, true⟩

def words04 : List Nat := [371285336538362371, 371285336542131575, 371285336572575782, 371285336634751239, 371285336678392778, 371285336681805628, 371285336584119071, 371285336576342634, 371285336649870076, 371285336670321027]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 97240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 97200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk972
