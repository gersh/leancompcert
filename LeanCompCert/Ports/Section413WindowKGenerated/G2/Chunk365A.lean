import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk365A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360614379138793444, 360614387283914241⟩, ⟨(-1188720839699651293), (-1188519865337363073)⟩, true⟩

def state01 : KState := ⟨⟨360554873251874548, 360554881401668419⟩, ⟨983359215909298207, 983560360862208769⟩, true⟩

def words00 : List Nat := [360581826407056176, 360581826407547328, 360581826330243744, 360581826583151824, 360581826583569981, 360581826281737630, 360581825231194378, 360581823744974624, 360581822258744900, 360581820880191077]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 36500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 36500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360491440001297164, 360491448155724380⟩, ⟨3299732241241460742, 3299933555380674010⟩, true⟩

def words01 : List Nat := [360581820142743069, 360581819803064242, 360581819463345859, 360581818749492272, 360581817287118288, 360581815526157670, 360581813765150145, 360581812072710453, 360581810255910165, 360581807782103917]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 36510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 36500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360597969482313748, 360597977641374609⟩, ⟨(-591328429843152176), (-591126946459588928)⟩, true⟩

def words02 : List Nat := [360581805308318642, 360581803327814672, 360581801727416626, 360581800875312060, 360581800023215467, 360581798535162961, 360581797073942369, 360581796360933950, 360581795682296446, 360581796125772529]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 36520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 36500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360543735052592971, 360543743216343984⟩, ⟨1390064513567962655, 1390266168305299105⟩, true⟩

def words03 : List Nat := [360581796126217880, 360581795936550817, 360581795746808001, 360581795219197741, 360581795068788887, 360581794727957743, 360581794387092415, 360581793589784733, 360581792044918183, 360581791004201272]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 36530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 36500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360551583017269225, 360551591185647749⟩, ⟨1103307493301284407, 1103509317151077569⟩, true⟩

def words04 : List Nat := [360581789963363258, 360581789670165398, 360581789340394160, 360581788532009690, 360581787723589187, 360581786725092670, 360581786103384853, 360581785203290716, 360581784303196458, 360581782959030816]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 36540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 36500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk365A
