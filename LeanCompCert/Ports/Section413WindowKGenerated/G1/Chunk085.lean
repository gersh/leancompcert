import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk085

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362326913260909813, 362326914156480514⟩, ⟨1327522523474731855, 1327527678142489665⟩, true⟩

def state01 : KState := ⟨⟨362413706333206761, 362413707230969908⟩, ⟨589670649830428110, 589675823145345714⟩, true⟩

def words00 : List Nat := [371283075511563515, 371283070868052332, 371283061470278049, 371283059097768149, 371283056725743600, 371283050933245800, 371283026817238553, 371283014013610878, 371283001212869661, 371282999337097446]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 8500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 8500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362383831166243651, 362383832066249864⟩, ⟨844569552927970192, 844574745342562216⟩, true⟩

def words01 : List Nat := [371282991195804868, 371282983224972953, 371282980959884433, 371282982150766320, 371282985357249408, 371282988563069733, 371282989514558863, 371282989514804554, 371282972193347163, 371282960557487254]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 8510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 8500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362357564247302553, 362357565149498019⟩, ⟨1068660014870334614, 1068665225948728872⟩, true⟩

def words02 : List Nat := [371282950942212724, 371282950942458482, 371282934704330487, 371282918251290950, 371282901802021822, 371282886096342334, 371282866380093236, 371282860299143710, 371282854219533663, 371282848294392361]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 8520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 8500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362501366854491410, 362501367758910824⟩, ⟨(-158941619825297925), (-158936389765308413)⟩, true⟩

def words03 : List Nat := [371282833608925960, 371282828995245687, 371282824382523689, 371282822591512487, 371282807058250049, 371282788895311518, 371282770736525310, 371282766186965696, 371282756940158927, 371282759119434732]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 8530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 8500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362377388631956568, 362377389538599626⟩, ⟨900191610403607868, 900196859464833564⟩, true⟩

def words04 : List Nat := [371282761597150685, 371282761597396960, 371282745898171190, 371282743794399763, 371282743871097900, 371282743871344243, 371282727891432602, 371282706690083458, 371282685493597337, 371282675720993174]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 8540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 8500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362396410496786238, 362396411405652866⟩, ⟨737811153709105130, 737816421793186914⟩, true⟩

def words05 : List Nat := [371282663408428143, 371282659683843359, 371282655960045141, 371282652398656627, 371282641958664013, 371282632544478438, 371282625091732863, 371282625091981327, 371282614983103312, 371282604912871697]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 8550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 8500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362349617906082673, 362349618817163952⟩, ⟨1139123638010534612, 1139128925063319296⟩, true⟩

def words06 : List Nat := [371282594844883867, 371282590423951980, 371282581385458891, 371282583624558667, 371282583624750057, 371282583265409020, 371282564836779256, 371282555511194522, 371282546187650839, 371282539345176008]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 8560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 8500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362338052588889749, 362338053502220359⟩, ⟨1238618248081383014, 1238623554422271030⟩, true⟩

def words07 : List Nat := [371282523837190909, 371282508489342388, 371282493144977106, 371282491289706644, 371282482598090872, 371282474580767421, 371282466565229127, 371282458315706711, 371282432048880528, 371282415221849995]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 8570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 8500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362303345352503515, 362303346268041635⟩, ⟨1537089329793955851, 1537094655086804939⟩, true⟩

def words08 : List Nat := [371282398398603990, 371282395039256515, 371282380524067709, 371282366162121030, 371282351803424198, 371282337586262680, 371282317149396281, 371282307817427086, 371282298487552777, 371282286274454535]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 8580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 8500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362434817986664856, 362434818904445311⟩, ⟨406771069797325111, 406776414363326579⟩, true⟩

def words09 : List Nat := [371282265445849326, 371282250552184800, 371282235661857300, 371282229852665865, 371282206095090570, 371282180554526591, 371282155019802147, 371282142901797236, 371282123987821365, 371282118487510815]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 8590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 8500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 8500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk085
