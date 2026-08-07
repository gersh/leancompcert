import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk400

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362469535160683482, 362469557864878849⟩, ⟨627306879738552528, 627920564019078908⟩, true⟩

def state01 : KState := ⟨⟨362476945684018535, 362476968399933297⟩, ⟨330884831086479181, 331498984203375843⟩, true⟩

def words00 : List Nat := [371285255487435299, 371285255347328754, 371285255086317806, 371285255237525613, 371285255238567655, 371285255230993210, 371285254477060645, 371285254044595541, 371285253801830126, 371285253803187568]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 40000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 40000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494567285766616, 362494590013643361⟩, ⟨(-374194567213646410), (-373579935439125590)⟩, true⟩

def words01 : List Nat := [371285253597090056, 371285253391761663, 371285253603424802, 371285253844941057, 371285254219630810, 371285254594821172, 371285254969887568, 371285254971211768, 371285255181060195, 371285255415921188]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 40010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 40000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476257622757564, 362476280362308136⟩, ⟨358707456872865062, 359322555896586884⟩, true⟩

def words02 : List Nat := [371285256167988925, 371285256169301007, 371285256089923545, 371285256010238662, 371285256039484924, 371285256040955191, 371285256221639231, 371285256518940358, 371285256692598489, 371285256693956815]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 40020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 40000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362508048510735418, 362508071262188418⟩, ⟨(-914072499517931991), (-913456923982894415)⟩, true⟩

def words03 : List Nat := [371285256870031326, 371285257271033004, 371285257794435049, 371285257795748173, 371285257602784013, 371285257238899159, 371285257132738456, 371285257134184301, 371285257651169470, 371285258222454573]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 40030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 40000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474194537768113, 362474217301053180⟩, ⟨441544321605612431, 442160370957655547⟩, true⟩

def words04 : List Nat := [371285258787741645, 371285258789054341, 371285258703859309, 371285258885773528, 371285259256011931, 371285259257324795, 371285258797102787, 371285258215451465, 371285257633279387, 371285257510065856]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 40040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 40000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362458335762130573, 362458358537217447⟩, ⟨1076856428145014271, 1077472950220932421⟩, true⟩

def words05 : List Nat := [371285257257424333, 371285257280959054, 371285257302664936, 371285257304000697, 371285256808282556, 371285256502287855, 371285256354756182, 371285256356069355, 371285255686213640, 371285255016254415]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 40050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 40000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479667132034392, 362479689918902660⟩, ⟨222248877438880652, 222865871535891378⟩, true⟩

def words06 : List Nat := [371285254345773075, 371285253800363439, 371285253038978118, 371285252900786746, 371285252762174777, 371285252521421659, 371285251842342260, 371285251708258967, 371285251830982836, 371285251832342538]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 40060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 40000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362466089696055651, 362466112494891330⟩, ⟨766382148734209887, 766999622426271681⟩, true⟩

def words07 : List Nat := [371285251694525739, 371285251485891514, 371285251386602501, 371285251388049584, 371285251187595423, 371285250991688935, 371285250795369660, 371285250576342167, 371285249687848136, 371285249212017734]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 40070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 40000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473622246880049, 362473645057431840⟩, ⟨464502820035745563, 465120763370710963⟩, true⟩

def words08 : List Nat := [371285248792182980, 371285248793520042, 371285248347088440, 371285247906505581, 371285247465444407, 371285247213847874, 371285246839893444, 371285246964809898, 371285246970844676, 371285246972207862]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 40080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 40000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362513382162281001, 362513404984698945⟩, ⟨(-1129680527814669719), (-1129062108706109711)⟩, true⟩

def words09 : List Nat := [371285246911721188, 371285247141285512, 371285247991736024, 371285248014120985, 371285248015155490, 371285247849985081, 371285248035593611, 371285248117863130, 371285248820921397, 371285249524518249]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 40090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 40000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 40000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk400
