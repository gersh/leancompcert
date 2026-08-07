import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk608

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

def state06 : KState := ⟨⟨362505021681193830, 362505076049983707⟩, ⟨(-1206846986446559394), (-1204611932123923156)⟩, true⟩

def words05 : List Nat := [371285281931773879, 371285282140307253, 371285282485368081, 371285282487429915, 371285282472676684, 371285282417401571, 371285282500210224, 371285282557527703, 371285282884156167, 371285283211677996]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 60850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 60800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487047885672635, 362487102273043542⟩, ⟨(-112951395783900260), (-110715210522730606)⟩, true⟩

def words06 : List Nat := [371285283537579824, 371285283539641882, 371285283606244888, 371285283709480717, 371285283797145333, 371285283799217356, 371285283629288406, 371285283460792773, 371285283390939325, 371285283423172130]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 60860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 60800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476900643856856, 362476955049851337⟩, ⟨504846663561145972, 507083982533277548⟩, true⟩

def words07 : List Nat := [371285283654767195, 371285283887249843, 371285284120832626, 371285284122909067, 371285284185006686, 371285284257676598, 371285284498732600, 371285284500795595, 371285284421881221, 371285284287409374]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 60870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 60800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362498262718445491, 362498317142880417⟩, ⟨(-795764017805470327), (-793525576085145487)⟩, true⟩

def words08 : List Nat := [371285284205503458, 371285284207776734, 371285284312599047, 371285284484655271, 371285284555126058, 371285284557224966, 371285284519494252, 371285284637408174, 371285285024205612, 371285285240364690]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 60880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 60800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362496364195575228, 362496418638829094⟩, ⟨(-680147133140567356), (-677907545443726512)⟩, true⟩

def words09 : List Nat := [371285285455105156, 371285285670527009, 371285285995812316, 371285286214258663, 371285286494927421, 371285286776418223, 371285287050321256, 371285287052384582, 371285287149459272, 371285287334820232]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 60890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 60800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 60800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk608
