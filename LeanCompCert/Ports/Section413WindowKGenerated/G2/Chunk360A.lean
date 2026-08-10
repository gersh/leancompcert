import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk360A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360558383421851642, 360558391336404506⟩, ⟨849281004319024082, 849473620460580936⟩, true⟩

def state01 : KState := ⟨⟨360546228665042592, 360546236584157981⟩, ⟨1286684849718239123, 1286877630133834533⟩, true⟩

def words00 : List Nat := [360581987170820178, 360581986264536626, 360581984866908801, 360581982888551056, 360581980910225169, 360581978554938111, 360581976749875031, 360581975714958482, 360581974680042267, 360581973258141148]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 36000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 36000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360641967385435224, 360641975309115439⟩, ⟨(-2161390286029358916), (-2161197341211847056)⟩, true⟩

def words01 : List Nat := [360581972266150416, 360581972044173599, 360581972369356741, 360581972800373553, 360581972800827522, 360581972502646694, 360581972675404421, 360581973716251821, 360581975382428757, 360581977048622620]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 36010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 36000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360591206792654168, 360591214720949429⟩, ⟨(-332845351619869146), (-332652240545428124)⟩, true⟩

def words02 : List Nat := [360581978326766573, 360581979828128436, 360581981138588809, 360581982449116438, 360581983224772516, 360581983232416318, 360581983232851608, 360581982854059881, 360581982475203331, 360581982331047805]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 36020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 36000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360569945261511493, 360569953194367845⟩, ⟨433411913701293206, 433605189133774232⟩, true⟩

def words03 : List Nat := [360581983165730987, 360581984000460510, 360581984447525253, 360581984448009710, 360581984442040039, 360581984240892788, 360581984606566704, 360581984747836709, 360581984748268312, 360581984414932046]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 36030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 36000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360555899166746225, 360555907104180508⟩, ⟨939716178238520230, 939909618681946214⟩, true⟩

def words04 : List Nat := [360581984101468772, 360581984508609445, 360581984637461370, 360581984766391278, 360581984766842393, 360581984229498136, 360581983195071545, 360581981990602150, 360581980786059865, 360581979493048246]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 36040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 36000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk360A
