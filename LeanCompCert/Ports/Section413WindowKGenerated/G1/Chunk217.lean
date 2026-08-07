import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk217

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362459568733080591, 362459575082147736⟩, ⟨532203516425044098, 532296686831197272⟩, true⟩

def state01 : KState := ⟨⟨362465196428746219, 362465202783871101⟩, ⟨410221358193059248, 410314660083462890⟩, true⟩

def words00 : List Nat := [371284104742696193, 371284104743442279, 371284105674661547, 371284106675987474, 371284107321839119, 371284107322516835, 371284105143736434, 371284103850985932, 371284102583262428, 371284102583967069]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 21700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 21700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362479302731134227, 362479309092439559⟩, ⟨104036486632876815, 104129922731653649⟩, true⟩

def words01 : List Nat := [371284101713956860, 371284100842891708, 371284101216760407, 371284102008949077, 371284103147419546, 371284104286037690, 371284105307293199, 371284105307971514, 371284103507670001, 371284103287777113]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 21710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 21700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362432603689693564, 362432610057051627⟩, ⟨1118466212839613973, 1118559780434732477⟩, true⟩

def words02 : List Nat := [371284103282423055, 371284103283101476, 371284100678130853, 371284098000699037, 371284095323264904, 371284092727038919, 371284089316127660, 371284088020166191, 371284086724073763, 371284085426606838]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 21720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 21700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362503994111311547, 362504000484791988⟩, ⟨(-433241125775663815), (-433147425109918891)⟩, true⟩

def words03 : List Nat := [371284083058315302, 371284082448965410, 371284083036874818, 371284083037553611, 371284081418419286, 371284079167495937, 371284076916489005, 371284076777804398, 371284076499440995, 371284077416620795]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 21730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 21700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362448704403654477, 362448710783269039⟩, ⟨769048871077278125, 769142705129835551⟩, true⟩

def words04 : List Nat := [371284078332144795, 371284078332835483, 371284077988032704, 371284078475141443, 371284079609037646, 371284079609716863, 371284078291265957, 371284076596898473, 371284074902428084, 371284073666263515]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 21740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 21700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362466764822525666, 362466771208263072⟩, ⟨376271110837077903, 376365078091564411⟩, true⟩

def words05 : List Nat := [371284072524901700, 371284073009581295, 371284073504422707, 371284073505102134, 371284071547908716, 371284069990288185, 371284068983248761, 371284068983933958, 371284068191637497, 371284067397513604]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 21750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 21700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489407139007633, 362489413530833103⟩, ⟨(-116420219391020651), (-116326119628884749)⟩, true⟩

def words06 : List Nat := [371284067581465654, 371284067843006176, 371284068968935068, 371284070095021643, 371284070869433513, 371284070870113229, 371284068906844040, 371284068979173767, 371284070116262339, 371284070362415076]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 21760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 21700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362475456040039691, 362475462438057201⟩, ⟨187488177754750603, 187582412348498511⟩, true⟩

def words07 : List Nat := [371284070362928692, 371284070271444042, 371284072192842234, 371284073424524361, 371284074973342630, 371284076522283806, 371284077379858011, 371284077380538198, 371284075431946549, 371284075037338583]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 21770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 21700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362452199534674827, 362452205938744084⟩, ⟨694152508564764103, 694246874997706365⟩, true⟩

def words08 : List Nat := [371284075727296619, 371284075727976885, 371284074008547390, 371284072211615247, 371284070414570163, 371284069263647232, 371284067061184723, 371284066961265911, 371284066861135554, 371284066740717362]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 21780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 21700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362494664866206183, 362494671276442463⟩, ⟨(-231573148205811019), (-231478647362420477)⟩, true⟩

def words09 : List Nat := [371284065279082539, 371284064082546986, 371284062885762595, 371284062689190191, 371284060362662120, 371284057687638101, 371284055012590242, 371284054115016638, 371284052989095514, 371284053476921230]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 21790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 21700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 21700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk217
