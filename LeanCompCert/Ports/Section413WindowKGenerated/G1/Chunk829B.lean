import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk829A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk829B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk829A

def state06 : KState := ⟨⟨362477257077390884, 362477360567992747⟩, ⟨653039999544481972, 658837256100950116⟩, true⟩

def words05 : List Nat := [371285301926112191, 371285302058012083, 371285302187690131, 371285302195740059, 371285302235268015, 371285302276188488, 371285302376421074, 371285302379297137, 371285302285998047, 371285302193548448]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 82950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 82900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492493518847855, 362492597035189217⟩, ⟨(-611015558670471036), (-605216166630811666)⟩, true⟩

def words06 : List Nat := [371285302107669791, 371285302110890884, 371285302173441093, 371285302279558647, 371285302361579992, 371285302364470035, 371285302377789450, 371285302452107045, 371285302634638454, 371285302725531255]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 82960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 82900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362488033949971971, 362488137492550773⟩, ⟨(-240991213603285969), (-235189644507746365)⟩, true⟩

def words07 : List Nat := [371285302787753709, 371285302850859824, 371285302959065059, 371285302996050168, 371285303074435467, 371285303153959276, 371285303216682222, 371285303219609013, 371285303195849064, 371285303233569709]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 82970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 82900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482524232074057, 362482627800231257⟩, ⟨216250739184549521, 222054430910147311⟩, true⟩

def words08 : List Nat := [371285303414965981, 371285303417842675, 371285303405850972, 371285303401120307, 371285303395270015, 371285303397664380, 371285303373933112, 371285303424501947, 371285303474211655, 371285303477191254]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 82980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 82900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497611092371808, 362497714686632123⟩, ⟨(-1035865025607114747), (-1030059167463585693)⟩, true⟩

def words09 : List Nat := [371285303526854567, 371285303610371817, 371285303817655067, 371285303877689335, 371285303893763269, 371285303910691458, 371285304071704544, 371285304180443305, 371285304331953342, 371285304484737404]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 82990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 82900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 82900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk829B
