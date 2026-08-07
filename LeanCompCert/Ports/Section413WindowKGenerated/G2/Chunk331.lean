import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk331

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

def state06 : KState := ⟨⟨360527488051653624, 360527494721298421⟩, ⟨1781502823248794050, 1781652364525197320⟩, true⟩

def words05 : List Nat := [360581229510702531, 360581229573253395, 360581229573647932, 360581229082625994, 360581228546675234, 360581227556625486, 360581226566501175, 360581226221513463, 360581225302719197, 360581223682834163]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 33150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 33100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360603242637050846, 360603249310874245⟩, ⟨(-730881940861396507), (-730732261001990561)⟩, true⟩

def words06 : List Nat := [360581222062946844, 360581221350875848, 360581221103763186, 360581221112014621, 360581221112429436, 360581220196901599, 360581219644134983, 360581219388854612, 360581219396004893, 360581220060595327]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 33160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 33100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360595621089675869, 360595627767723967⟩, ⟨(-478111233301330950), (-477961413288248646)⟩, true⟩

def words07 : List Nat := [360581220269150702, 360581220477741837, 360581220655400770, 360581221454402801, 360581222021018543, 360581222587677302, 360581222698646439, 360581222699089533, 360581222661324750, 360581223095975429]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 33170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 33100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360565504337488593, 360565511019705973⟩, ⟨521423940047259912, 521573898418535812⟩, true⟩

def words08 : List Nat := [360581224436811598, 360581225206913051, 360581225514597295, 360581225822308581, 360581225898589799, 360581226430970143, 360581226476494059, 360581226522091392, 360581226522488801, 360581225810257903]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 33180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 33100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360658802101107166, 360658808787505867⟩, ⟨(-2575680518367246228), (-2575530421196829558)⟩, true⟩

def words09 : List Nat := [360581225769552219, 360581226202420004, 360581227031168284, 360581227889565647, 360581227974021293, 360581228058506685, 360581228800582077, 360581230232478592, 360581232569540631, 360581234906562618]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 33190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 33100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 33100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk331
