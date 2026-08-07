import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk535

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362462066803404923, 362462108387659942⟩, ⟨1224622295536364723, 1226125244770299317⟩, true⟩

def state01 : KState := ⟨⟨362477510854177201, 362477552454532969⟩, ⟨398305941062456727, 399809751765030547⟩, true⟩

def words00 : List Nat := [371285026189403546, 371285025907922523, 371285025461389838, 371285025364573732, 371285025267174878, 371285025084833610, 371285024507792895, 371285024280627857, 371285024135570569, 371285024137428971]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 53500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 53500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362473386800588481, 362473428417302961⟩, ⟨619030735776638800, 620535421917535030⟩, true⟩

def words01 : List Nat := [371285023999142811, 371285023861429437, 371285023866157745, 371285023868156414, 371285023841448792, 371285023770273549, 371285023698506850, 371285023627197587, 371285023090252769, 371285022875858969]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 53510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 53500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362468479498893007, 362468521131616416⟩, ⟨881711798016868406, 883217341040404034⟩, true⟩

def words02 : List Nat := [371285022660451500, 371285022587134213, 371285022223300337, 371285021850617467, 371285021477279629, 371285021209663569, 371285020816300539, 371285020772291572, 371285020727686559, 371285020614916256]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 53520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 53500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490691910098770, 362490733559048696⟩, ⟨(-307401913171604121), (-305895501460482215)⟩, true⟩

def words03 : List Nat := [371285020327221872, 371285020348679524, 371285020516469296, 371285020518276075, 371285020440252315, 371285020317733446, 371285020207240609, 371285020209220230, 371285020155825478, 371285020264536818]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 53530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 53500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478161552733573, 362478203217939547⟩, ⟨363459533137649054, 364966815276989168⟩, true⟩

def words04 : List Nat := [371285020378201910, 371285020380002578, 371285020132208943, 371285020030070069, 371285019929712385, 371285019931510067, 371285019531154050, 371285019124169783, 371285018716474116, 371285018658000742]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 53540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 53500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362459405675701669, 362459447357082895⟩, ⟨1368045909100128171, 1369554057508559393⟩, true⟩

def words05 : List Nat := [371285018752986321, 371285018975987021, 371285019198367377, 371285019200164477, 371285018958010057, 371285018823719196, 371285018697676939, 371285018699474500, 371285018296570621, 371285017821188731]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 53550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 53500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469818749817136, 362469860447297761⟩, ⟨810300615228515582, 811809626000136502⟩, true⟩

def words06 : List Nat := [371285017345002867, 371285017128712137, 371285016764922441, 371285016661131091, 371285016556767858, 371285016396117941, 371285015770683038, 371285015275224543, 371285014778803998, 371285014631094665]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 53560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 53500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478158770741329, 362478200484582130⟩, ⟨363455188492691902, 364965075761636324⟩, true⟩

def words07 : List Nat := [371285014349582161, 371285014000326780, 371285013650375972, 371285013524406186, 371285013223843130, 371285013028926886, 371285012833407629, 371285012638338914, 371285012201062116, 371285012076141698]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 53570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 53500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362463382674781323, 362463424404634218⟩, ⟨1155228663438244072, 1156739408718171502⟩, true⟩

def words08 : List Nat := [371285012000018740, 371285012001817293, 371285011641892938, 371285011270557638, 371285010898541716, 371285010542352789, 371285010055745606, 371285009834319487, 371285009612311755, 371285009390801753]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 53580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 53500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487513109565499, 362487554855725056⟩, ⟨(-137975372455007764), (-136463753223207272)⟩, true⟩

def words09 : List Nat := [371285008989249778, 371285008936455124, 371285009175377586, 371285009177176387, 371285009051690123, 371285008868832489, 371285008848186045, 371285008850167999, 371285008888131086, 371285008937678318]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 53590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 53500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 53500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk535
