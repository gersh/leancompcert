import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk312

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362499542321045716, 362499555854048689⟩, ⟨(-442844431352343625), (-442559034648031467)⟩, true⟩

def state01 : KState := ⟨⟨362472204233690412, 362472217775621549⟩, ⟨410299341134220429, 410585016444386259⟩, true⟩

def words00 : List Nat := [371285372957551196, 371285372958554913, 371285372825132124, 371285372681613053, 371285372683790440, 371285372684915073, 371285372782637688, 371285373100921921, 371285373334225118, 371285373335264112]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 31200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 31200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362489689752381171, 362489703303396883⟩, ⟨(-135594575165371812), (-135308616280049144)⟩, true⟩

def words01 : List Nat := [371285373090405387, 371285373267561276, 371285373700727283, 371285373701731362, 371285372769261863, 371285371663754725, 371285370557900301, 371285370010484259, 371285369265863907, 371285369405818970]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 31210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 31200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362453828154175395, 362453841714249896⟩, ⟨984193258473334675, 984479500221198355⟩, true⟩

def words02 : List Nat := [371285369535743638, 371285369536748129, 371285368455987595, 371285368398569839, 371285368589502992, 371285368590512124, 371285367860120537, 371285366918029018, 371285365975605165, 371285365233309173]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 31220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 31200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362460244531853857, 362460258100983836⟩, ⟨783946763275760335, 784233287871336057⟩, true⟩

def words03 : List Nat := [371285364237751083, 371285364251980498, 371285364252732539, 371285364172699114, 371285363431651774, 371285363004382432, 371285363170279439, 371285363171284358, 371285362401765138, 371285361599315185]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 31230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 31200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362494867553070351, 362494881131206249⟩, ⟨(-297835065046749982), (-297548259061511646)⟩, true⟩

def words04 : List Nat := [371285360796465821, 371285360421697389, 371285359741381374, 371285359872330547, 371285359873108455, 371285359832799045, 371285358749705116, 371285358688599706, 371285359585874753, 371285359891595949]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 31240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 31200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362491498871522776, 362491512458793174⟩, ⟨(-192519666083396574), (-192232574597139328)⟩, true⟩

def words05 : List Nat := [371285359983471591, 371285360075671064, 371285361188597830, 371285361789295363, 371285362429344798, 371285363069732492, 371285363608671910, 371285363609677480, 371285362983005120, 371285363180951866]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 31250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 31200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362494517587353162, 362494531183597349⟩, ⟨(-286782755340926785), (-286495383288048491)⟩, true⟩

def words06 : List Nat := [371285364215807190, 371285364791738374, 371285365231908589, 371285365672401405, 371285366205100860, 371285366239865814, 371285367294473242, 371285368349412468, 371285369193963443, 371285369487991579]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 31260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 31200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362551627107659387, 362551640713008943⟩, ⟨(-2072889420936871856), (-2072601764113240198)⟩, true⟩

def words07 : List Nat := [371285370801735711, 371285372115924384, 371285373963144279, 371285374754020717, 371285375385690301, 371285376017633714, 371285377668867538, 371285378945644525, 371285381064671035, 371285383184026071]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 31270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 31200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362503477115667310, 362503490730099711⟩, ⟨(-566663134960137004), (-566375193978593740)⟩, true⟩

def words08 : List Nat := [371285385305985492, 371285386067849612, 371285387041802347, 371285388016208991, 371285389302619166, 371285389303625607, 371285389230133001, 371285389160387198, 371285389891796921, 371285390471431769]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 31280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 31200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362434528167253550, 362434541790736196⟩, ⟨1591217078824611544, 1591505303034933214⟩, true⟩

def words09 : List Nat := [371285391479276372, 371285392487452290, 371285393409606428, 371285393410613300, 371285392973523930, 371285392549328500, 371285392124639077, 371285391856344872, 371285390228958124, 371285388605529645]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 31290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 31200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 31200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk312
