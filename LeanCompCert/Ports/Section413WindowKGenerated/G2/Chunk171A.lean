import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk171A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360612284213167066, 360612285886436582⟩, ⟨(-493945512069322215), (-493926142751143517)⟩, true⟩

def state01 : KState := ⟨⟨360613074939641786, 360613076614950775⟩, ⟨(-507802586141977152), (-507783181938528692)⟩, true⟩

def words00 : List Nat := [360583404423292134, 360583404774843269, 360583404775035970, 360583403410396848, 360583402045883299, 360583398393451564, 360583397880720035, 360583399326364051, 360583399326558558, 360583400781747659]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 17100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 17100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360676518119143229, 360676519796495122⟩, ⟨(-1593580930687182512), (-1593561491519625296)⟩, true⟩

def words01 : List Nat := [360583404758659362, 360583408735169780, 360583415158942391, 360583419569345567, 360583420665920458, 360583421762382360, 360583426257956758, 360583432495930104, 360583437933448592, 360583443370379847]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 17110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 17100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360626811341132259, 360626813020548601⟩, ⟨(-742480031093567284), (-742460556572118250)⟩, true⟩

def words02 : List Nat := [360583446623865476, 360583450001700517, 360583456777023727, 360583463551618720, 360583469190911319, 360583471457437042, 360583471457633114, 360583471105869516, 360583470754108682, 360583472844460100]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 17120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 17100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360628233061176214, 360628234742635291⟩, ⟨(-766839668756868167), (-766820159233093007)⟩, true⟩

def words03 : List Nat := [360583477262156711, 360583481679378907, 360583484386542691, 360583486136568220, 360583486136750027, 360583485903165674, 360583488827822616, 360583493499482610, 360583496110016882, 360583498720277606]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 17130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 17100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360634412307956320, 360634413991465260⟩, ⟨(-872785473000798249), (-872765928332113757)⟩, true⟩

def words04 : List Nat := [360583503590824958, 360583510147027020, 360583515641589406, 360583521135549136, 360583523687876384, 360583523688093413, 360583523036672946, 360583523198383084, 360583523849642911, 360583526817053733]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 17140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 17100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk171A
