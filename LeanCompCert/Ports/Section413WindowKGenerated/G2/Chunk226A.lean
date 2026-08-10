import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk226A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360547705599574737, 360547708596464783⟩, ⟨737297412271779889, 737343237257150467⟩, true⟩

def state01 : KState := ⟨⟨360577999491598719, 360578002491255084⟩, ⟨52444540207653182, 52490427725434482⟩, true⟩

def words00 : List Nat := [360580332960103905, 360580333676940363, 360580334460404898, 360580335243851902, 360580335244123415, 360580334056579382, 360580331610509863, 360580328797229978, 360580325984111042, 360580324049314591]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 22600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 22600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360594830158409970, 360594833160852228⟩, ⟨(-328190833375678015), (-328144882854832637)⟩, true⟩

def words01 : List Nat := [360580323946901620, 360580322860582173, 360580322637387765, 360580324477658177, 360580325821577141, 360580327165426856, 360580327165694622, 360580326979017441, 360580326313352677, 360580326954987995]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 22610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 22600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360564321058277694, 360564324063476759⟩, ⟨362083582077264124, 362129594971087754⟩, true⟩

def words02 : List Nat := [360580329544796092, 360580330193735801, 360580330193996753, 360580329860556752, 360580329527093880, 360580328761806292, 360580328762045489, 360580328327833934, 360580327893629420, 360580326255035358]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 22620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 22600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360611319630285518, 360611322638253513⟩, ⟨(-702189662380596378), (-702143586812279794)⟩, true⟩

def words03 : List Nat := [360580325548184894, 360580324238178133, 360580322928202238, 360580322186381855, 360580319505348697, 360580315166008505, 360580310826995822, 360580308434185740, 360580309228638849, 360580310598731749]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 22630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 22600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360557035221385304, 360557038232143695⟩, ⟨526858509474894877, 526904648231533227⟩, true⟩

def words04 : List Nat := [360580310987997131, 360580310988290197, 360580309835049532, 360580310231125908, 360580310231375482, 360580309291958252, 360580308131966937, 360580305992258974, 360580303852685266, 360580301130520364]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 22640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 22600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk226A
