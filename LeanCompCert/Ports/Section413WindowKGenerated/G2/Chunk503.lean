import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk503

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360621516610641449, 360621532490585214⟩, ⟨(-1991039154858956242), (-1990499429115018416)⟩, true⟩

def state01 : KState := ⟨⟨360581611710931158, 360581627597503638⟩, ⟨16276317649399856, 16816376849422300⟩, true⟩

def words00 : List Nat := [360581961262100474, 360581961811475607, 360581962221304980, 360581962631316366, 360581962942083847, 360581962942778458, 360581962859474448, 360581962527160495, 360581962194736496, 360581961852658666]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 50300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 50300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360566306376472164, 360566322269584479⟩, ⟨786474510290899770, 787014898543004372⟩, true⟩

def words01 : List Nat := [360581962234224146, 360581962622552467, 360581962781858894, 360581962884119845, 360581962884701805, 360581962794758299, 360581962891307858, 360581962892002708, 360581962780370487, 360581962470270946]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 50310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 50300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360593105181765471, 360593121081444468⟩, ⟨(-562239588774858030), (-561698870054562974)⟩, true⟩

def words02 : List Nat := [360581962243386501, 360581962526614730, 360581962620735529, 360581962714973978, 360581962715619716, 360581962405286806, 360581961701101544, 360581961256840041, 360581960812384827, 360581960983889193]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 50320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 50300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360582322009867713, 360582337916160769⟩, ⟨(-19428799446714438), (-18887747807805290)⟩, true⟩

def words03 : List Nat := [360581960984509471, 360581960967046966, 360581961325293965, 360581961900841819, 360581962377172299, 360581962853605206, 360581962975454131, 360581962976149111, 360581962711796512, 360581962720042142]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 50330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 50300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360568777423606811, 360568793336444999⟩, ⟨662463512223729791, 663004893377048081⟩, true⟩

def words04 : List Nat := [360581963121916836, 360581963130365081, 360581963130984254, 360581962896437901, 360581962661774399, 360581962328408547, 360581962190889287, 360581961963584373, 360581961736215244, 360581961258855666]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 50340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 50300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360606674701535674, 360606690620942394⟩, ⟨(-1245994301179953369), (-1245452589268781643)⟩, true⟩

def words05 : List Nat := [360581960997904935, 360581960727406188, 360581960456714716, 360581960434278752, 360581960285129384, 360581959795970325, 360581959306697931, 360581959139899863, 360581959631555761, 360581960123349639]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 50350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 50300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360580623188599613, 360580639114623472⟩, ⟨66050676158651392, 66592721341557966⟩, true⟩

def words06 : List Nat := [360581960417602293, 360581960639939244, 360581961255645198, 360581961871537589, 360581962212100081, 360581962212795476, 360581962160220231, 360581961869679690, 360581961579022566, 360581961185724159]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 50360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 50300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360532508550220112, 360532524482802352⟩, ⟨2489893621110162911, 2490435996671557283⟩, true⟩

def words07 : List Nat := [360581961268008521, 360581961376679166, 360581961377305022, 360581961239667289, 360581960813434468, 360581960134765589, 360581959455919805, 360581959170567156, 360581958492214144, 360581957511716040]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 50370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 50300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360603673874843073, 360603689813988829⟩, ⟨(-1095759147617374700), (-1095216441354505392)⟩, true⟩

def words08 : List Nat := [360581956531094563, 360581955847237385, 360581955368204862, 360581955282574656, 360581955196893272, 360581954773977061, 360581954582746477, 360581954684231788, 360581955015861400, 360581955447904519]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 50380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 50300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360579098638568621, 360579114584352291⟩, ⟨142657203044795793, 143200243824553439⟩, true⟩

def words09 : List Nat := [360581955580731948, 360581955713620201, 360581955714193294, 360581955980732529, 360581956150009591, 360581956319393755, 360581956320013640, 360581956261124254, 360581955914591506, 360581955859031350]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 50390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 50300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 50300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk503
