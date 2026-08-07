import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk420

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360636871273268520, 360636882182216246⟩, ⟨(-2283094130280857585), (-2282784483965034091)⟩, true⟩

def state01 : KState := ⟨⟨360590870031749465, 360590880946074719⟩, ⟨(-350784594229775941), (-350474722030295597)⟩, true⟩

def words00 : List Nat := [360582533159594736, 360582534290724359, 360582535056064039, 360582535821422564, 360582536342679207, 360582537145544006, 360582537692236576, 360582538239003447, 360582538295589528, 360582538494763627]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 42000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 42000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360672297433891194, 360672308353610461⟩, ⟨(-3772036379197204065), (-3771726280368085797)⟩, true⟩

def words01 : List Nat := [360582539047954664, 360582539601293004, 360582540720069552, 360582541852862426, 360582542507199410, 360582543161552615, 360582544381337007, 360582545952676962, 360582548089322060, 360582550225998837]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 42010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 42000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360622523001006825, 360622533926181790⟩, ⟨(-1680418825654534184), (-1680108497550834196)⟩, true⟩

def words02 : List Nat := [360582551853138598, 360582552917088517, 360582554546345234, 360582556175693622, 360582557549172449, 360582558359571665, 360582558886148482, 360582559412773776, 360582559895127777, 360582560846846280]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 42020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 42000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360555898304615227, 360555909235167930⟩, ⟨1120202192880715573, 1120512747038287011⟩, true⟩

def words03 : List Nat := [360582561884620942, 360582562922452945, 360582563676613544, 360582563867854382, 360582563868341296, 360582563670381278, 360582563696663259, 360582563697235208, 360582563359246851, 360582562725820601]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 42030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 42000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360586423082233673, 360586434018196711⟩, ⟨(-163111616885944153), (-162800835252182043)⟩, true⟩

def words04 : List Nat := [360582562092296339, 360582561741312638, 360582562397795358, 360582563054357112, 360582563233609450, 360582563234181480, 360582562850628822, 360582562711058010, 360582562571328450, 360582562508951933]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 42040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 42000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360577096476659849, 360577107418067660⟩, ⟨229061806960321674, 229372817574162870⟩, true⟩

def words05 : List Nat := [360582562509461690, 360582562278669259, 360582562047781495, 360582562121123519, 360582562121604688, 360582562033241596, 360582561944815201, 360582561572230061, 360582561013971955, 360582560884961958]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 42050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 42000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360565753980253582, 360565764927060831⟩, ⟨706134743048070771, 706445980788490195⟩, true⟩

def words06 : List Nat := [360582561190501807, 360582561191074064, 360582561063958424, 360582560498452973, 360582559932877506, 360582559132873023, 360582558731875778, 360582558306298082, 360582557880675836, 360582557082534768]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 42060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 42000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360593401073727831, 360593412025932562⟩, ⟨(-457076567397817716), (-456765102558495034)⟩, true⟩

def words07 : List Nat := [360582556848965003, 360582557014693483, 360582557744445014, 360582558050168019, 360582558050706364, 360582557746166849, 360582557441540218, 360582557122190256, 360582557341343865, 360582557599883788]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 42070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 42000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360605817105716241, 360605828063372976⟩, ⟨(-979846330077879652), (-979534635791572752)⟩, true⟩

def words08 : List Nat := [360582557600396322, 360582557492423478, 360582557102800111, 360582557190365444, 360582557190845707, 360582557012426342, 360582556750543898, 360582556205599083, 360582555678880007, 360582556232440198]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 42080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 42000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360571203624075908, 360571214587132283⟩, ⟨477204761559074433, 477516683143443349⟩, true⟩

def words09 : List Nat := [360582556760108108, 360582557287853959, 360582557530928211, 360582557607284398, 360582557607763709, 360582557539093898, 360582557470262998, 360582557294481072, 360582557294991324, 360582557026161819]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 42090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 42000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 42000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk420
