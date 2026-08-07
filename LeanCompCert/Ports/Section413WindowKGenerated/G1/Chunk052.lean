import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk052

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362531008674166860, 362531008993994007⟩, ⟨(-253486457234379365), (-253485330112119311)⟩, true⟩

def state01 : KState := ⟨⟨362583146193932942, 362583146515043634⟩, ⟨(-524869053404537400), (-524867919601283378)⟩, true⟩

def words00 : List Nat := [371282295726534326, 371282305007956601, 371282328759941524, 371282352502855585, 371282369354334429, 371282369354478021, 371282355584346003, 371282361518975205, 371282404111900870, 371282423444692208]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 5200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 5200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362483433546787253, 362483433869204859⟩, ⟨(-4324045011763185), (-4322904392829767)⟩, true⟩

def words01 : List Nat := [371282443341261776, 371282463230243650, 371282506483097725, 371282537858014337, 371282569327093133, 371282600784162636, 371282627511475441, 371282627511619177, 371282605726423591, 371282605885218491]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 5210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 5200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362427564426922874, 362427564750623531⟩, ⟨288034425671468986, 288035572994730110⟩, true⟩

def words02 : List Nat := [371282629747472957, 371282629747619166, 371282623628827465, 371282617633056644, 371282611639526138, 371282606334188554, 371282607266926478, 371282625922962992, 371282638473800493, 371282638473949484]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 5220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 5200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362725048341449070, 362725048666454853⟩, ⟨(-1268937412185643492), (-1268936258029996020)⟩, true⟩

def words03 : List Nat := [371282653774118834, 371282679592827829, 371282741740487928, 371282755497232039, 371282762664874974, 371282769829827945, 371282813288716145, 371282839034960048, 371282885258270907, 371282931464006848]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 5230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 5200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362458882940541151, 362458883266851115⟩, ⟨126416717004481066, 126417878000624478⟩, true⟩

def words04 : List Nat := [371282977790903632, 371282977791047997, 371282987491108013, 371282999105531569, 371283021678305902, 371283021678450501, 371283005286163849, 371282982485593227, 371282962862493531, 371282962862660758]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 5240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 5200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362335501355398397, 362335501683008954⟩, ⟨775424590348848970, 775425758179842082⟩, true⟩

def words05 : List Nat := [371282980285037634, 371283002284809210, 371283018856142909, 371283018856287721, 371282996534159619, 371282985210061832, 371282977304628744, 371282977304774517, 371282949060330295, 371282921028670521]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 5250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 5200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362437909638846374, 362437909967754689⟩, ⟨236996130526668080, 236997305190524258⟩, true⟩

def words06 : List Nat := [371282900921539902, 371282900921699269, 371282906282884909, 371282921826537157, 371282934024471235, 371282934024616292, 371282898469408972, 371282886536910517, 371282880993256900, 371282880993407540]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 5260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 5200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362647947433619568, 362647947763855051⟩, ⟨(-871316876496693303), (-871315694832069107)⟩, true⟩

def words07 : List Nat := [371282872461735549, 371282856242104161, 371282859557145937, 371282861898663395, 371282874192056529, 371282886480844297, 371282898984233597, 371282898984382264, 371282925851772500, 371282957100186794]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 5270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 5200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362543787900260039, 362543788231790198⟩, ⟨(-320208137066319663), (-320206948558906409)⟩, true⟩

def words08 : List Nat := [371283023974452592, 371283055135299183, 371283085232679593, 371283115318716886, 371283145954026126, 371283158665361214, 371283193079325565, 371283227480336260, 371283257617544899, 371283269057993391]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 5280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 5200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362612539926967138, 362612540259816444⟩, ⟨(-684468933571577139), (-684467738079240397)⟩, true⟩

def words09 : List Nat := [371283286883190748, 371283304701729202, 371283350478244021, 371283350478389952, 371283348980252923, 371283341210276044, 371283361134623191, 371283371031759022, 371283395403412579, 371283419765932415]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 5290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 5200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 5200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk052
