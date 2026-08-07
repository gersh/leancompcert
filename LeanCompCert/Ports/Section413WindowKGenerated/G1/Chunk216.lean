import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk216

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362483204340077958, 362483210628290575⟩, ⟨18111359891489396, 18203212784814802⟩, true⟩

def state01 : KState := ⟨⟨362456460276669455, 362456466570895496⟩, ⟨596150216226674039, 596242199041347945⟩, true⟩

def words00 : List Nat := [371284055430203119, 371284055756385442, 371284055988283192, 371284056220383971, 371284056747677694, 371284056748423817, 371284057010956984, 371284057516337956, 371284057602082772, 371284057602780797]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 21600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 21600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362533481940169017, 362533488240485282⟩, ⟨(-1068596837210598819), (-1068504722754947715)⟩, true⟩

def words01 : List Nat := [371284057186909064, 371284058048010564, 371284061045471290, 371284061499622287, 371284061500148049, 371284061300474489, 371284063036338763, 371284063903144287, 371284066189651916, 371284068476239644]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 21610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 21600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362503970398495450, 362503976704906736⟩, ⟨(-430573460132018718), (-430481213871028718)⟩, true⟩

def words02 : List Nat := [371284070761440746, 371284070847598339, 371284071820227232, 371284072793114476, 371284074362667419, 371284074363347055, 371284074037890091, 371284073661515994, 371284074660024629, 371284075580877749]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 21620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 21600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362458126423794934, 362458132736290122⟩, ⟨561497496894599276, 561589874781923840⟩, true⟩

def words03 : List Nat := [371284078147376890, 371284080713925370, 371284083279612913, 371284083562393156, 371284084496177362, 371284085430207609, 371284086606018333, 371284086606694613, 371284085407774248, 371284084209246773]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 21630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 21600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484541197710781, 362484547516258738⟩, ⟨(-10270372674467385), (-10177863774592633)⟩, true⟩

def words04 : List Nat := [371284083010527260, 371284082539835271, 371284081003474552, 371284080961386558, 371284080919093929, 371284080509356107, 371284077603355136, 371284076828059985, 371284077406377116, 371284077428790511]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 21640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 21600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362499673364943743, 362499679689650592⟩, ⟨(-337968578873180804), (-337875936601879988)⟩, true⟩

def words05 : List Nat := [371284077429304907, 371284077033979169, 371284077929758265, 371284078184853387, 371284078858800397, 371284079532948813, 371284080205815866, 371284080206508995, 371284080615108548, 371284081336084188]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 21650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 21600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485172789210704, 362485179119934613⟩, ⟨(-23790387600523260), (-23697614968030058)⟩, true⟩

def words06 : List Nat := [371284084184285714, 371284084196233568, 371284084196744570, 371284084057598859, 371284083918207048, 371284083879429697, 371284083830115838, 371284084697385942, 371284085551395631, 371284085602562640]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 21660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 21600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362514009018344893, 362514015355199113⟩, ⟨(-648710639311778007), (-648617733804904627)⟩, true⟩

def words07 : List Nat := [371284087069229017, 371284088536134314, 371284092127618910, 371284092885849476, 371284093089329637, 371284093292992884, 371284095268109321, 371284096181776714, 371284097562281104, 371284098942957754]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 21670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 21600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489414997167581, 362489421340130145⟩, ⟨(-115482460194387137), (-115389422226976499)⟩, true⟩

def words08 : List Nat := [371284099990747575, 371284099991424895, 371284099418600227, 371284100194449742, 371284101617837251, 371284101618526064, 371284101284293385, 371284100949732820, 371284101402872651, 371284101648911346]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 21680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 21600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362459568733080591, 362459575082147736⟩, ⟨532203516425044098, 532296686831197272⟩, true⟩

def words09 : List Nat := [371284103863997372, 371284106079154778, 371284107883821427, 371284107884498841, 371284106861180602, 371284106486810449, 371284107151989904, 371284107152668841, 371284106013073750, 371284104883384197]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 21690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 21600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 21600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk216
