import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk331A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360563344565308910, 360563351209836787⟩, ⟨591216036885093543, 591364746038963203⟩, true⟩

def state01 : KState := ⟨⟨360627468346414594, 360627474995117551⟩, ⟨(-1531745985557077607), (-1531597138187781883)⟩, true⟩

def words00 : List Nat := [360581216781906746, 360581217360829292, 360581217914084436, 360581218467384527, 360581218467791991, 360581218241548394, 360581217105155848, 360581216879439090, 360581217152964100, 360581218550486227]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 33100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 33100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360630143264882767, 360630149917796562⟩, ⟨(-1620353468125220192), (-1620204481314203446)⟩, true⟩

def words01 : List Nat := [360581219377472654, 360581220204451940, 360581221941444969, 360581224137961851, 360581225883724522, 360581227629454866, 360581228654757446, 360581229222424437, 360581230699856275, 360581232177350495]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 33110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 33100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360606046723565745, 360606053380642592⟩, ⟨(-822301579459750744), (-822152454747410460)⟩, true⟩

def words02 : List Nat := [360581233792432056, 360581234498449790, 360581234668503772, 360581234838605534, 360581234838976314, 360581234964172982, 360581235941970227, 360581236919793244, 360581237429241650, 360581238178724528]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 33120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 33100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360609165859287964, 360609172520547602⟩, ⟨(-925828233462721064), (-925678970153794020)⟩, true⟩

def words03 : List Nat := [360581238903153670, 360581239627665566, 360581240649118448, 360581240762267238, 360581240762675218, 360581240087566601, 360581239412414889, 360581239299955669, 360581240143199159, 360581240986491485]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 33130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 33100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360553179097707126, 360553185763178854⟩, ⟨929526800555385898, 929676203473467530⟩, true⟩

def words04 : List Nat := [360581241373090952, 360581241373533535, 360581241162027399, 360581240699111137, 360581240236112254, 360581239143883900, 360581237144006633, 360581234557898769, 360581231971862352, 360581230294203695]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 33140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 33100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk331A
