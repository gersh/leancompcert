import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk426

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362499637335922828, 362499663219343307⟩, ⟨(-615885000270206899), (-615139966567083471)⟩, true⟩

def state01 : KState := ⟨⟨362488192314988236, 362488218210932268⟩, ⟨(-128216618370162587), (-127471051097357993)⟩, true⟩

def words00 : List Nat := [371285224251539926, 371285224506314027, 371285224654404368, 371285224802941492, 371285225114549711, 371285225156988700, 371285225684895387, 371285226213365800, 371285226633531944, 371285226705192029]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 42600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 42600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362526968023049621, 362526993931669816⟩, ⟨(-1780560951291829134), (-1779814843822587066)⟩, true⟩

def words01 : List Nat := [371285227327961440, 371285227951413389, 371285229022396439, 371285229761673370, 371285230405787610, 371285231050337133, 371285232093846511, 371285232863806014, 371285233844610084, 371285234825974911]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 42610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 42600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362494076234509519, 362494102155824933⟩, ⟨(-378644722218629770), (-377898073617524686)⟩, true⟩

def words02 : List Nat := [371285235804714620, 371285236114707623, 371285236650849124, 371285237187712876, 371285237753417689, 371285237754822567, 371285237586890196, 371285237422739902, 371285237550074112, 371285237759643340]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 42620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 42600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362466988219567014, 362467014153542094⟩, ⟨776384676941535912, 777131865287068084⟩, true⟩

def words03 : List Nat := [371285238451476012, 371285239143859382, 371285239834696453, 371285239836101478, 371285239913331457, 371285240034883152, 371285240382485993, 371285240383891284, 371285239998352059, 371285239572521622]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 42630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 42600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490296073173625, 362490322019715869⟩, ⟨(-217478906867593245), (-216731182592740145)⟩, true⟩

def words04 : List Nat := [371285239269364836, 371285239270929581, 371285239622040049, 371285240073974952, 371285240445637341, 371285240447042815, 371285240085571261, 371285240006400687, 371285240396158837, 371285240516759485]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 42640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 42600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362492629596821565, 362492655556188564⟩, ⟨(-317051942879997313), (-316303671565604573)⟩, true⟩

def words05 : List Nat := [371285240536260116, 371285240556193070, 371285240807877342, 371285240809425732, 371285240899675876, 371285241013349591, 371285241081777890, 371285241083217617, 371285241028624544, 371285241204167618]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 42650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 42600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479533026822464, 362479558998697550⟩, ⟨241737937344853120, 242486742320599998⟩, true⟩

def words06 : List Nat := [371285241805421196, 371285241806827322, 371285241752868256, 371285241697178592, 371285241640960417, 371285241540059211, 371285241466114860, 371285241705205004, 371285241836289370, 371285241837748889]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 42660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 42600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362507748282732753, 362507774267357938⟩, ⟨(-962279347048693541), (-961529997963758231)⟩, true⟩

def words07 : List Nat := [371285242038051595, 371285242372292142, 371285243199271439, 371285243462138772, 371285243619328465, 371285243776934759, 371285244483755402, 371285244917840911, 371285245446683758, 371285245976128498]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 42670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 42600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362500070796825804, 362500096794125915⟩, ⟨(-634663412853533742), (-633913522737089088)⟩, true⟩

def words08 : List Nat := [371285246443127394, 371285246444534055, 371285246463502705, 371285246748996454, 371285247197134388, 371285247198565502, 371285247191699842, 371285247133673957, 371285247565004137, 371285247914438462]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 42680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 42600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478391618287923, 362478417628261292⟩, ⟨290973537691773788, 291723968894122004⟩, true⟩

def words09 : List Nat := [371285248544579127, 371285249175249951, 371285249689869631, 371285249691276764, 371285249474454954, 371285249421831396, 371285249863374692, 371285249864782645, 371285249729732946, 371285249571326729]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 42690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 42600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 42600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk426
