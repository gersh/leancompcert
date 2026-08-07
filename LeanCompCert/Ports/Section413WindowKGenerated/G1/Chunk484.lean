import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk484

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362447489926223272, 362447523686389586⟩, ⟨1818224229308358668, 1819328181484883052⟩, true⟩

def state01 : KState := ⟨⟨362468846088649042, 362468879863208222⟩, ⟨784501014981692309, 785605663848806457⟩, true⟩

def words00 : List Nat := [371285112336096501, 371285111883600732, 371285111219589845, 371285110914883273, 371285110609724557, 371285110208531963, 371285109238782939, 371285108695204909, 371285108150801452, 371285108032261079]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 48400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 48400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362461177826893842, 362461211616162508⟩, ⟨1155808032790289908, 1156913393816401318⟩, true⟩

def words01 : List Nat := [371285107698270353, 371285107265039241, 371285106831143217, 371285106823150392, 371285106600457019, 371285106424957675, 371285106248894828, 371285106075213860, 371285105403667022, 371285104912193413]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 48410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 48400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362467153605389180, 362467187409008824⟩, ⟨866469858068631782, 867575914044562144⟩, true⟩

def words02 : List Nat := [371285104419838929, 371285104253295187, 371285103794086993, 371285103337498595, 371285102880305297, 371285102485183852, 371285101936152676, 371285101767851110, 371285101599038834, 371285101427469377]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 48420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 48400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482266356764960, 362482300175005724⟩, ⟨134427349753658493, 135534113902923811⟩, true⟩

def words03 : List Nat := [371285101058678730, 371285101004718937, 371285100949935931, 371285100843635407, 371285100233307292, 371285099550821759, 371285098867724040, 371285098610089189, 371285098210141453, 371285098154235760]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 48430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 48400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362467609002874028, 362467642835657080⟩, ⟨844428609821933375, 845536078472956053⟩, true⟩

def words04 : List Nat := [371285098097681478, 371285098003563980, 371285097408028588, 371285097205858214, 371285097002904924, 371285096932118316, 371285096293873941, 371285095574822823, 371285094855123373, 371285094560702962]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 48440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 48400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362452683832852783, 362452717680135772⟩, ⟨1567720867658567073, 1568829038907794393⟩, true⟩

def words05 : List Nat := [371285094201609727, 371285094126274109, 371285094050413387, 371285093976398359, 371285093547402401, 371285093132138640, 371285092716025708, 371285092660043931, 371285092036846471, 371285091370579598]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 48450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 48400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362463596435191689, 362463630296944097⟩, ⟨1038855413032279535, 1039964285542633675⟩, true⟩

def words06 : List Nat := [371285090703660116, 371285090117368364, 371285089343588273, 371285088994786159, 371285088645480413, 371285088220624950, 371285087413876552, 371285086882067519, 371285086349432434, 371285086131182650]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 48460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 48400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362464201014281181, 362464234890740831⟩, ⟨1009579741133067336, 1010689326577715468⟩, true⟩

def words07 : List Nat := [371285085689736581, 371285085224816314, 371285084759245168, 371285084718477427, 371285084466658036, 371285084238531245, 371285084009898420, 371285083723813859, 371285082870866923, 371285082442856708]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 48470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 48400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470664004937024, 362470697895796823⟩, ⟨696283181301097900, 697393464939170842⟩, true⟩

def words08 : List Nat := [371285082013937368, 371285082009539717, 371285081650604482, 371285081289141422, 371285080927082203, 371285080697274205, 371285080253426094, 371285080234157759, 371285080214335555, 371285080107901158]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 48480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 48400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362500095560143001, 362500129465576190⟩, ⟨(-730964673511782771), (-729853683136429969)⟩, true⟩

def words09 : List Nat := [371285079939642547, 371285080068811529, 371285080574066333, 371285080575681083, 371285080515054368, 371285080379885773, 371285080530751882, 371285080622837498, 371285080934226383, 371285081246299548]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 48490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 48400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 48400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk484
