import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk364A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360546330477545399, 360546338576286165⟩, ⟨1294675526544477518, 1294874810355207118⟩, true⟩

def state01 : KState := ⟨⟨360584887101475068, 360584895204832418⟩, ⟨(-108943289224255185), (-108743837346723661)⟩, true⟩

def words00 : List Nat := [360581911083216432, 360581910658945312, 360581911062409789, 360581911511298083, 360581911511753563, 360581911308851039, 360581910556795715, 360581909774059100, 360581908991222220, 360581908639306980]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 36400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 36400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360579225327160199, 360579233435177193⟩, ⟨97214271847755646, 97413893406259506⟩, true⟩

def words01 : List Nat := [360581908639743295, 360581908269991975, 360581907900169078, 360581908284232621, 360581908622165152, 360581908960159136, 360581908960595522, 360581908868665171, 360581908244289870, 360581908171404713]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 36410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 36400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360531953840641384, 360531961953277186⟩, ⟨1818850364461296108, 1819050154259713874⟩, true⟩

def words02 : List Nat := [360581908098371155, 360581907526983973, 360581906204004776, 360581904383072286, 360581902562160280, 360581900365893754, 360581898633946553, 360581897450697815, 360581896267452058, 360581894705246984]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 36420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 36400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360557061984748641, 360557070102008081⟩, ⟨903983958927683423, 904183917188438919⟩, true⟩

def words03 : List Nat := [360581893335032609, 360581892218330932, 360581891101537778, 360581890736536303, 360581889620372717, 360581887771510112, 360581885922655241, 360581884638517776, 360581883732972320, 360581883052534658]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 36430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 36400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360516944091757316, 360516952213693644⟩, ⟨2366043241905283942, 2366243370614074352⟩, true⟩

def words04 : List Nat := [360581882372067775, 360581881315466598, 360581880548162600, 360581879889395381, 360581879230534851, 360581878211979534, 360581876442680645, 360581874294995351, 360581872147339755, 360581869727290738]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 36440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 36400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk364A
