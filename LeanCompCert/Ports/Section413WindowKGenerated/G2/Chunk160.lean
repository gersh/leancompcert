import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk160

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360587060556190068, 360587062012227085⟩, ⟨(-93368023380616466), (-93352250702760092)⟩, true⟩

def state01 : KState := ⟨⟨360690522045201363, 360690523503140110⟩, ⟨(-1748995922949976424), (-1748980119835056560)⟩, true⟩

def words00 : List Nat := [360581232124931679, 360581239488868232, 360581247940920832, 360581256391954910, 360581260726653061, 360581262788854653, 360581268746583973, 360581274703628096, 360581280522305055, 360581287345508791]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 16000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 16000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360670755012338212, 360670756472196082⟩, ⟨(-1432347827150598255), (-1432331993301116245)⟩, true⟩

def words01 : List Nat := [360581292099190618, 360581296852298932, 360581304094400901, 360581314188665399, 360581323259805327, 360581332329851068, 360581339049889545, 360581341902021925, 360581347483618822, 360581353064587249]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 16010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 16000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360598528191209441, 360598529652966679⟩, ⟨(-275121225390673388), (-275105361103600424)⟩, true⟩

def words02 : List Nat := [360581360743679555, 360581364555721068, 360581365395891102, 360581366235975215, 360581366236144087, 360581367799181065, 360581368645684275, 360581369492119110, 360581369492301125, 360581368817017356]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 16020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 16000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360586763221045642, 360586764684705242⟩, ⟨(-86727020806751913), (-86711126015374691)⟩, true⟩

def words03 : List Nat := [360581368817181216, 360581368659143047, 360581372225470534, 360581372225672185, 360581372088504398, 360581368677762209, 360581365267409454, 360581360372851651, 360581358753946971, 360581359091162734]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 16030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 16000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360553615484986815, 360553616950567260⟩, ⟨444835085208442825, 444851010819694281⟩, true⟩

def words04 : List Nat := [360581359091342488, 360581357459678393, 360581354792335574, 360581354614763728, 360581354437157187, 360581353240348413, 360581349632766159, 360581344088183159, 360581338544253161, 360581333524450107]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 16040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 16000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360502465073418078, 360502466540902471⟩, ⟨1265908609544584103, 1265924565723693867⟩, true⟩

def words05 : List Nat := [360581331797834522, 360581329938730949, 360581328079836993, 360581324256977030, 360581318853580582, 360581310828051304, 360581302803460916, 360581298649191520, 360581296141895431, 360581291233662353]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 16050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 16000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360703374801643656, 360703376271032709⟩, ⟨(-1961661047690159384), (-1961645060912764968)⟩, true⟩

def words06 : List Nat := [360581286325993662, 360581286211636662, 360581291003846205, 360581295795497706, 360581296554949869, 360581296555152090, 360581298164565082, 360581300902274198, 360581307505365535, 360581315101166941]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 16060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 16000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360638873886573650, 360638875357888777⟩, ⟨(-924556424528135548), (-924540406789142796)⟩, true⟩

def words07 : List Nat := [360581319791737043, 360581324481747983, 360581333035804390, 360581344121566774, 360581354177858351, 360581364232931691, 360581371779131938, 360581375487675110, 360581379063704076, 360581382639352048]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 16070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 16000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360730138939700082, 360730140412919184⟩, ⟨(-2392568739118050033), (-2392552690753418551)⟩, true⟩

def words08 : List Nat := [360581387303071069, 360581393821589527, 360581398414546609, 360581403006953087, 360581406583447224, 360581413165762219, 360581423604702280, 360581434042383326, 360581442296441804, 360581451537724764]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 16080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 16000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360784660769244975, 360784662244377776⟩, ⟨(-3270250091212990980), (-3270234012047689134)⟩, true⟩

def words09 : List Nat := [360581464634228921, 360581477729166640, 360581488106106564, 360581497438401731, 360581503040864291, 360581508642646536, 360581518097432745, 360581529502087563, 360581542119192355, 360581554734779137]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 16090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 16000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 16000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk160
