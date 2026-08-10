import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk813A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk813B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk813A

def state06 : KState := ⟨⟨360608154725605553, 360608197897495425⟩, ⟨(-2116868970397406712), (-2114496776818736880)⟩, true⟩

def words05 : List Nat := [360582206376609423, 360582206485174536, 360582206744431985, 360582207131245121, 360582207455708548, 360582207780362142, 360582208015985173, 360582208185692375, 360582208506075062, 360582208826849554]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 81350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 81300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360592496924201024, 360592540107073316⟩, ⟨(-842913912629962812), (-840540825465849860)⟩, true⟩

def words06 : List Nat := [360582209111574527, 360582209345380433, 360582209481551261, 360582209617845294, 360582209716244364, 360582209905295089, 360582210043550560, 360582210182035306, 360582210244425760, 360582210372579875]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 81360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 81300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360626371887482716, 360626415081358957⟩, ⟨(-3599471730937511595), (-3597097748330249143)⟩, true⟩

def words07 : List Nat := [360582210651336916, 360582210930429261, 360582211360039437, 360582211802050013, 360582212109712703, 360582212417437588, 360582212792192893, 360582213285762603, 360582213829860221, 360582214374211955]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 81370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 81300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360608487771169448, 360608530976145257⟩, ⟨(-2143978653898166876), (-2141603767951033800)⟩, true⟩

def words08 : List Nat := [360582214842902636, 360582215315503525, 360582215897642330, 360582216480108958, 360582216990216910, 360582217349930061, 360582217633622367, 360582217917425104, 360582218113678715, 360582218438297694]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 81380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 81300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360579838444143767, 360579881660101865⟩, ⟨188000873331148654, 190376653178529676⟩, true⟩

def words09 : List Nat := [360582218890815927, 360582219343546387, 360582219700411513, 360582219906835652, 360582220048839930, 360582220191190614, 360582220403811219, 360582220466101521, 360582220467140382, 360582220439624943]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 81390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 81300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 81300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk813B
