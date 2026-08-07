import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk035

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362444409483960126, 362444409623235597⟩, ⟨105999736864141619, 106000067594081115⟩, true⟩

def state01 : KState := ⟨⟨362080621588319059, 362080621728434912⟩, ⟨1381106751167129116, 1381107084842692390⟩, true⟩

def words00 : List Nat := [371274686706309169, 371274677408293571, 371274589049052817, 371274566731365286, 371274546979942494, 371274546980035541, 371274442108350323, 371274318926406962, 371274195814636931, 371274099530384398]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 3500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 3500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362022141933865822, 362022142074822383⟩, ⟨1588325347715743675, 1588325684346536167⟩, true⟩

def words01 : List Nat := [371273987460438956, 371273955558711433, 371273923675114458, 371273892031964168, 371273794585857987, 371273707414766852, 371273620293200745, 371273613126207855, 371273499188767299, 371273370962420831]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 3510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 3500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362221409657047430, 362221409798842168⟩, ⟨885817806083510466, 885818145669010406⟩, true⟩

def words02 : List Nat := [371273242808868106, 371273148033737760, 371273013410735749, 371272930321708113, 371272847279795595, 371272751039257302, 371272571179746679, 371272470859813530, 371272370596683995, 371272349783450953]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 3520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 3500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362338882609343104, 362338882751991829⟩, ⟨470507753451616363, 470508096056058253⟩, true⟩

def words03 : List Nat := [371272278715839944, 371272191057633117, 371272103449012354, 371272095204808562, 371272059770525229, 371272023171394740, 371271986592927127, 371271948953700730, 371271832199759655, 371271794643533089]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 3530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 3500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362510440360618419, 362510440504108012⟩, ⟨(-136352418485504555), (-136352072899980583)⟩, true⟩

def words04 : List Nat := [371271798681916775, 371271804082295149, 371271809561431574, 371271815037508834, 371271844418355428, 371271844418459933, 371271904725009342, 371271974227293405, 371272031469390727, 371272042285887798]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 3540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 3500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362763070924026156, 362763071068369942⟩, ⟨(-1035177200304966998), (-1035176851682722990)⟩, true⟩

def words05 : List Nat := [371272111958096235, 371272181591135006, 371272260868547777, 371272260868642159, 371272235362660955, 371272199429855927, 371272205961985803, 371272209350951600, 371272291053745775, 371272372710694367]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 3550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 3500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362398265633357106, 362398265778557719⟩, ⟨264681917123984740, 264682268800845404⟩, true⟩

def words06 : List Nat := [371272454550678261, 371272464368017863, 371272506645908698, 371272548900128935, 371272598848268137, 371272598848362855, 371272544699249256, 371272478448345500, 371272412234528653, 371272406470098573]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 3560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 3500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362031367999294709, 362031368145350732⟩, ⟨1577973232475282811, 1577973587210455569⟩, true⟩

def words07 : List Nat := [371272442756609944, 371272499773110636, 371272555215998717, 371272555216093886, 371272507002214951, 371272458166748498, 371272409358539459, 371272389393898844, 371272266046114102, 371272142890381586]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 3570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 3500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362336875112926727, 362336875259837714⟩, ⟨484031251843416368, 484031609643740662⟩, true⟩

def words08 : List Nat := [371272019803391392, 371271974102831962, 371271890622886320, 371271884464419194, 371271878309355715, 371271858328913788, 371271772025764454, 371271732085555151, 371271703006157754, 371271703006256584]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 3580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 3500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362421325154250898, 362421325302036828⟩, ⟨180622869715502447, 180623230661246645⟩, true⟩

def words09 : List Nat := [371271665460313576, 371271612326492994, 371271583030832369, 371271583030937550, 371271577372365400, 371271586079475027, 371271586079547389, 371271580527352082, 371271512362394677, 371271498421664953]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 3590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 3500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 3500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk035
