import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk272

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362524739387401123, 362524749554819190⟩, ⟨(-1072449110354447517), (-1072262155769224113)⟩, true⟩

def state01 : KState := ⟨⟨362484421143103549, 362484431318324877⟩, ⟨24450247311132209, 24637414185773279⟩, true⟩

def words00 : List Nat := [371285331049384888, 371285331673045872, 371285332991408294, 371285334310107075, 371285336034380419, 371285336174486802, 371285336316627655, 371285336459052808, 371285336771737695, 371285336772723473]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 27200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 27200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479298289786836, 362479308472792775⟩, ⟨164063439916976463, 164250818649998455⟩, true⟩

def words01 : List Nat := [371285338055932147, 371285339372662444, 371285340660232155, 371285340740203008, 371285341226191156, 371285341712610167, 371285343051838726, 371285343052704629, 371285342889649907, 371285342668922459]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 27210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 27200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362494804332169094, 362494814522926106⟩, ⟨(-258031136916683784), (-257843547159545934)⟩, true⟩

def words02 : List Nat := [371285343359657282, 371285343767358702, 371285344736389114, 371285345705697341, 371285346267546174, 371285346268411750, 371285345034024565, 371285344769965999, 371285345423698375, 371285345772341863]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 27220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 27200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362498034699633845, 362498044898286811⟩, ⟨(-345953431019318835), (-345765626215753831)⟩, true⟩

def words03 : List Nat := [371285346030273060, 371285346288490045, 371285347767206206, 371285348719355705, 371285349904544668, 371285351089972893, 371285352004998626, 371285352005864679, 371285351592280544, 371285352059322906]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 27230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 27200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486894393899914, 362486904600268783⟩, ⟨(-42339031187999158), (-42151016163502616)⟩, true⟩

def words04 : List Nat := [371285353871844026, 371285354113606956, 371285354340314849, 371285354567299504, 371285355199819241, 371285355312090736, 371285356117403914, 371285356923021088, 371285357773089954, 371285357830749738]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 27240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 27200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362528505465736633, 362528515679937132⟩, ⟨(-1176583634767043692), (-1176395406291221170)⟩, true⟩

def words05 : List Nat := [371285358058366881, 371285358286403077, 371285359858890477, 371285359859756945, 371285359639665006, 371285359130120584, 371285359218298105, 371285359458187474, 371285361041909814, 371285362625893216]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 27250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 27200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362463656924534478, 362463667146563464⟩, ⟨591511446263600022, 591699888182913560⟩, true⟩

def words06 : List Nat := [371285364168115805, 371285364168983161, 371285365386477790, 371285366607808185, 371285367721570960, 371285367722438158, 371285367045324240, 371285366233883877, 371285365422161126, 371285364978913406]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 27260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 27200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362466842913301096, 362466853143159187⟩, ⟨504798339220375626, 504986994679289734⟩, true⟩

def words07 : List Nat := [371285364731434221, 371285365279927983, 371285365825767294, 371285365826638776, 371285365094605796, 371285364777213349, 371285365483675628, 371285365484544395, 371285365074227141, 371285364396629836]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 27270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 27200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362509324510627470, 362509334748246500⟩, ⟨(-654155738439655097), (-653966871221939163)⟩, true⟩

def words08 : List Nat := [371285364382599489, 371285364383555139, 371285365715511842, 371285367053213989, 371285368035446271, 371285368036329013, 371285368655796998, 371285369407337132, 371285371139022192, 371285372017997629]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 27280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 27200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492649057589038, 362492659303118466⟩, ⟨(-199017168230698509), (-198828085098968951)⟩, true⟩

def words09 : List Nat := [371285372632028017, 371285373246293344, 371285374376050375, 371285374837282718, 371285375575748684, 371285376314503921, 371285377027917998, 371285377028786197, 371285376221989577, 371285376489847928]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 27290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 27200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 27200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk272
