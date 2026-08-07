import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk318

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362504474039913009, 362504488120834892⟩, ⟨(-613464356428903241), (-613161699634620517)⟩, true⟩

def state01 : KState := ⟨⟨362460266249918413, 362460280339976861⟩, ⟨792523033039292920, 792825980422802496⟩, true⟩

def words00 : List Nat := [371285207549924045, 371285207550948204, 371285206872526048, 371285206197579918, 371285205522294152, 371285205153984031, 371285204449430011, 371285204368815497, 371285204287828270, 371285204136909361]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 31800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 31800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362496441503487624, 362496455602784222⟩, ⟨(-358426271372101293), (-358123030075971473)⟩, true⟩

def words01 : List Nat := [371285203354111995, 371285203231085806, 371285203727695709, 371285203728720237, 371285203035143624, 371285202056964585, 371285201083400450, 371285201084528921, 371285200949534456, 371285201304362552]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 31810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 31800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362454033898286453, 362454048006844476⟩, ⟨991177757738713420, 991481293779447642⟩, true⟩

def words02 : List Nat := [371285201661845261, 371285201662887751, 371285201204941365, 371285201210190852, 371285201406965934, 371285201407990783, 371285200291312859, 371285199149794679, 371285198007953335, 371285197277776913]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 31820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 31800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362436643682244350, 362436657800040991⟩, ⟨1544969076244718273, 1545272906397974097⟩, true⟩

def words03 : List Nat := [371285196299889949, 371285196183384736, 371285196066538854, 371285195936603090, 371285194921467009, 371285194213567459, 371285193505176768, 371285193290776292, 371285191763710708, 371285190240568566]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 31830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 31800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362460711617668800, 362460725744656466⟩, ⟨778496818380731003, 778800941222999933⟩, true⟩

def words04 : List Nat := [371285188717054288, 371285187817519328, 371285186543282650, 371285185680896252, 371285184818257513, 371285183696976780, 371285181263805947, 371285179813232995, 371285178362212262, 371285177893517471]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 31840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 31800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362463462059341176, 362463476195664794⟩, ⟨690909235455301780, 691213655694892102⟩, true⟩

def words05 : List Nat := [371285177126587330, 371285176354725528, 371285175632623433, 371285175633753121, 371285175190969382, 371285174864995372, 371285174538689547, 371285173880942014, 371285172219243948, 371285171539534691]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 31850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 31800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362447134005550030, 362447148151005734⟩, ⟨1211279802216259978, 1211584513452058202⟩, true⟩

def words06 : List Nat := [371285171037241769, 371285171038267868, 371285170047823120, 371285169048593653, 371285168049006495, 371285167356273241, 371285166284929286, 371285165728005941, 371285165170787391, 371285164608911353]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 31860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 31800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362482133866785918, 362482148021550113⟩, ⟨95560353064151222, 95865361007215396⟩, true⟩

def words07 : List Nat := [371285163416798036, 371285162411955646, 371285161406630901, 371285161382096588, 371285160047980378, 371285158457841593, 371285156867390037, 371285156135677690, 371285155183756319, 371285155090590490]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 31870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 31800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362443850420494998, 362443864584509067⟩, ⟨1316241262023704484, 1316546564901750954⟩, true⟩

def words08 : List Nat := [371285154997036696, 371285154907573916, 371285153799616613, 371285153671922777, 371285153543754358, 371285153451380496, 371285152175500692, 371285150901062744, 371285149626282750, 371285148578391217]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 31880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 31800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362436254668790607, 362436268842056741⟩, ⟨1558667247282731098, 1558972845255472388⟩, true⟩

def words09 : List Nat := [371285147284554169, 371285146970584817, 371285146656276246, 371285146346130879, 371285144909274949, 371285143778773094, 371285142647790972, 371285142387669704, 371285140995053820, 371285139464165064]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 31890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 31800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 31800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk318
