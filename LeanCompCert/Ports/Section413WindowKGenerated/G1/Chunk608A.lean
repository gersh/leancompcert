import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk608A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362505571429693581, 362505625687099100⟩, ⟨(-1239736895265994224), (-1237508616463129050)⟩, true⟩

def state01 : KState := ⟨⟨362486916169709588, 362486970445714060⟩, ⟨(-105382579223584869), (-103153169508780139)⟩, true⟩

def words00 : List Nat := [371285272595797839, 371285272734162766, 371285273075170656, 371285273417236591, 371285273839692754, 371285273902154516, 371285273963282483, 371285274025137227, 371285274124181921, 371285274154426156]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 60800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 60800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362481540103367225, 362481594397904949⟩, ⟨221655845785718284, 223886382602501296⟩, true⟩

def words01 : List Nat := [371285274454409412, 371285274755205293, 371285275029925772, 371285275047078110, 371285275145067102, 371285275244142189, 371285275569126247, 371285275585502999, 371285275587057048, 371285275528825740]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 60810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 60800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362498941194891915, 362498995507891353⟩, ⟨(-836746948672654862), (-834515288920128028)⟩, true⟩

def words02 : List Nat := [371285275679778466, 371285275782646420, 371285275995464773, 371285276209108093, 371285276375619555, 371285276377685693, 371285276335346712, 371285276405207639, 371285276694446733, 371285276922155131]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 60820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 60800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362502511549832422, 362502565881629462⟩, ⟨(-1053931638156576211), (-1051698834854415813)⟩, true⟩

def words03 : List Nat := [371285277149374356, 371285277377294766, 371285277847397517, 371285278183705556, 371285278553953711, 371285278924958520, 371285279245270850, 371285279287856254, 371285279573386578, 371285279860116759]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 60830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 60800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491030313412027, 362491084663557326⟩, ⟨(-355348578187453661), (-353114658480958599)⟩, true⟩

def words04 : List Nat := [371285280283691269, 371285280415849473, 371285280515755051, 371285280616370492, 371285280785474151, 371285280820824096, 371285281088911443, 371285281357855308, 371285281626770458, 371285281724271514]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 60840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 60800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk608A
