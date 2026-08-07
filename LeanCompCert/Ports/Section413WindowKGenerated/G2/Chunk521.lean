import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk521

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360617608255005664, 360617625340766727⟩, ⟨(-1856577186311588019), (-1855975715953280679)⟩, true⟩

def state01 : KState := ⟨⟨360593429238544470, 360593446331191925⟩, ⟨(-596887979756822675), (-596286150583891935)⟩, true⟩

def words00 : List Nat := [360582003087279658, 360582003207620617, 360582003695573141, 360582004183722285, 360582004449666675, 360582004450388225, 360582004348789874, 360582003967629807, 360582003586333798, 360582003715418214]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 52100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 52100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360553894765096388, 360553911864536191⟩, ⟨1463461837050165891, 1464064020206109821⟩, true⟩

def words01 : List Nat := [360582004040991449, 360582004366689688, 360582004458463735, 360582004459185508, 360582004301309868, 360582003890034890, 360582003478567800, 360582003009993054, 360582002656402288, 360582002118185580]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 52110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 52100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360594001078398757, 360594018184662365⟩, ⟨(-626964202173914276), (-626361663328212252)⟩, true⟩

def words02 : List Nat := [360582001579826066, 360582001571047592, 360582001985117376, 360582002399309451, 360582002498087467, 360582002498809449, 360582002561798004, 360582002777532833, 360582002805754553, 360582003036989614]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 52120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 52100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360582155995567967, 360582173108702695⟩, ⟨(-9391002480809210), (-8788105409435138)⟩, true⟩

def words03 : List Nat := [360582003083635788, 360582003130359031, 360582003383418891, 360582003822515984, 360582004169146366, 360582004515895528, 360582004675762249, 360582004676484322, 360582004559630429, 360582004563691870]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 52130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 52100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360598971750169993, 360598988870110526⟩, ⟨(-886339179206906204), (-885735927246720464)⟩, true⟩

def words04 : List Nat := [360582004737687512, 360582004823768386, 360582004824425902, 360582004605813803, 360582004387092296, 360582004076454576, 360582004186180553, 360582004425032324, 360582004479564997, 360582004806003477]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 52140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 52100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360610933845647365, 360610950972401375⟩, ⟨(-1510265902037289239), (-1509662294720651635)⟩, true⟩

def words05 : List Nat := [360582005173255599, 360582005540701992, 360582006274971482, 360582006740351122, 360582006890131903, 360582007039961019, 360582007179121375, 360582007504079768, 360582008059561724, 360582008615185819]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 52150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 52100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360608152702110385, 360608169835742295⟩, ⟨(-1365272459576800422), (-1364668493475609018)⟩, true⟩

def words06 : List Nat := [360582008986564706, 360582009304425501, 360582009989017134, 360582010673817563, 360582011266399155, 360582011492468605, 360582011534413628, 360582011576435901, 360582011726934795, 360582012229150978]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 52160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 52100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360581641706865423, 360581658847306976⟩, ⟨17868776408592822, 18473097803339310⟩, true⟩

def words07 : List Nat := [360582012605280331, 360582012981523044, 360582013034128569, 360582013034852611, 360582012932149811, 360582012733268859, 360582012701201787, 360582012879105079, 360582012879748767, 360582012873711793]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 52170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 52100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360641534134932073, 360641551282192776⟩, ⟨(-3107603489613644936), (-3106998812362105650)⟩, true⟩

def words08 : List Nat := [360582013227354238, 360582013840210804, 360582014819433966, 360582015798762865, 360582016426103772, 360582016807037063, 360582017358036798, 360582017909226575, 360582018826712764, 360582019968127859]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 52180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 52100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360593257984790308, 360593275138948151⟩, ⟨(-587779657161329875), (-587174619914244615)⟩, true⟩

def words09 : List Nat := [360582020923229223, 360582021878378832, 360582022813827759, 360582023934546047, 360582024740472894, 360582025546479867, 360582026139302095, 360582026366089278, 360582026582177529, 360582026798496546]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 52190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 52100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 52100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk521
