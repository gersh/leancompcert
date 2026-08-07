import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk594

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488355294067317, 362488406986086715⟩, ⟨(-201254626380319379), (-199180535007794415)⟩, true⟩

def state01 : KState := ⟨⟨362491015456338873, 362491067166257466⟩, ⟨(-359231767918998933), (-357156613240308351)⟩, true⟩

def words00 : List Nat := [371285054152496817, 371285054236245431, 371285054318146687, 371285054400704930, 371285054566363188, 371285054591808295, 371285054900226420, 371285055209478263, 371285055438646400, 371285055541924594]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 59400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 59400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362508449524999635, 362508501253043321⟩, ⟨(-1395123002661005396), (-1393046771076214958)⟩, true⟩

def words01 : List Nat := [371285055788418820, 371285056035914475, 371285056422903062, 371285056474725147, 371285056476284306, 371285056447180792, 371285056669610861, 371285056782671134, 371285057178589501, 371285057575369162]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 59410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 59400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362496504556609173, 362496556302810070⟩, ⟨(-685345546859147972), (-683268236281169994)⟩, true⟩

def words02 : List Nat := [371285057957165114, 371285058139469538, 371285058393313934, 371285058648189680, 371285058988299054, 371285059000996542, 371285059012416828, 371285059024480138, 371285059274795902, 371285059470579733]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 59420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 59400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362477204750938269, 362477256515253815⟩, ⟨461813840016820284, 463892227239653804⟩, true⟩

def words03 : List Nat := [371285059909642101, 371285060349538666, 371285060737057681, 371285060747509332, 371285060842125974, 371285060937744813, 371285061148687980, 371285061150698461, 371285061022251485, 371285060893235640]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 59430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 59400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362493636936755443, 362493688719058560⟩, ⟨(-514924342873830692), (-512844886376857084)⟩, true⟩

def words04 : List Nat := [371285060915535854, 371285060929166317, 371285061225464530, 371285061522604564, 371285061772272426, 371285061774283049, 371285061800510408, 371285061957104687, 371285062226032360, 371285062373221201]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 59440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 59400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362497320842424783, 362497372643045552⟩, ⟨(-733961515416544775), (-731880969841866543)⟩, true⟩

def words05 : List Nat := [371285062448137283, 371285062523681910, 371285062881863727, 371285063101160281, 371285063283775253, 371285063467170506, 371285063648524233, 371285063650571877, 371285063845255980, 371285064054729818]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 59450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 59400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362500236013885844, 362500287832404786⟩, ⟨(-907292721729400243), (-905211111835426869)⟩, true⟩

def words06 : List Nat := [371285064497105667, 371285064670315292, 371285064844259840, 371285065018880997, 371285065210161836, 371285065327890252, 371285065728035741, 371285066128967575, 371285066523577889, 371285066781609686]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 59460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 59400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362517348200013332, 362517400036767206⟩, ⟨(-1924973400127805118), (-1922890705713562326)⟩, true⟩

def words07 : List Nat := [371285067322178547, 371285067863864238, 371285068687654942, 371285069169419047, 371285069617865408, 371285070066895028, 371285070658534078, 371285071132046458, 371285071676962090, 371285072222747376]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 59470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 59400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362501219225125156, 362501271080053490⟩, ⟨(-965590616155112393), (-963506840631594739)⟩, true⟩

def words08 : List Nat := [371285072764804920, 371285072930371157, 371285073271471227, 371285073613576606, 371285074039312683, 371285074233928176, 371285074425611606, 371285074618021228, 371285074963421497, 371285075237982730]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 59480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 59400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487516452294864, 362487568325335059⟩, ⟨(-150280517389586093), (-148195664301362621)⟩, true⟩

def words09 : List Nat := [371285075723488603, 371285076209777843, 371285076644075187, 371285076733704472, 371285076891680126, 371285077050664291, 371285077491624820, 371285077596222287, 371285077639612224, 371285077683760945]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 59490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 59400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 59400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk594
