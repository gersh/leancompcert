import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk419

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360614042699264771, 360614053554166042⟩, ⟨(-1323082439659801621), (-1322775060591498665)⟩, true⟩

def state01 : KState := ⟨⟨360615276114280599, 360615286974615723⟩, ⟨(-1374814740848049341), (-1374507134074957997)⟩, true⟩

def words00 : List Nat := [360582484966035974, 360582485660240837, 360582486922689099, 360582488185250431, 360582489035796457, 360582489630503310, 360582489870041513, 360582490109630412, 360582490335114629, 360582491118299364]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 41900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 41900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360586958835237350, 360586969700936353⟩, ⟨(-187744120629698638), (-187436289029117342)⟩, true⟩

def words01 : List Nat := [360582492469455663, 360582493820659730, 360582494885221457, 360582495703881264, 360582496278072045, 360582496852397022, 360582497863017510, 360582498307652480, 360582498414825433, 360582498522075422]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 41910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 41900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360600034457593227, 360600045328683689⟩, ⟨(-736076942613322130), (-735768884976795766)⟩, true⟩

def words02 : List Nat := [360582498522539939, 360582498853131464, 360582499087333392, 360582499321625391, 360582499322154516, 360582499072274895, 360582498256413379, 360582498008615773, 360582497775376878, 360582498194463738]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 41920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 41900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360589811658833609, 360589822535359832⟩, ⟨(-307370732976101727), (-307062447391151895)⟩, true⟩

def words03 : List Nat := [360582498326696857, 360582498458984571, 360582498835638171, 360582499573466569, 360582500165687815, 360582500757973867, 360582500907208928, 360582500907782130, 360582501064808610, 360582501240030891]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 41930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 41900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360598717941798983, 360598728823693312⟩, ⟨(-680968457632135013), (-680659946881631775)⟩, true⟩

def words04 : List Nat := [360582501982473800, 360582502345168914, 360582502345681239, 360582502235605724, 360582502125432447, 360582501896726580, 360582502490963646, 360582503085281602, 360582503317812803, 360582503705176909]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 41940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 41900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360656903115727139, 360656914003019279⟩, ⟨(-3122327071835113245), (-3122018334620620633)⟩, true⟩

def words05 : List Nat := [360582503856441718, 360582504007858508, 360582504726234111, 360582505360718205, 360582505514915836, 360582505669152208, 360582506390341708, 360582507597271325, 360582509371002845, 360582511144778994]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 41950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 41900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360619177469523357, 360619188362246880⟩, ⟨(-1539421698874451800), (-1539112733731737544)⟩, true⟩

def words06 : List Nat := [360582512594442440, 360582513479245810, 360582514662187371, 360582515845242276, 360582516511384326, 360582516612776561, 360582516613290010, 360582516428892494, 360582516626219951, 360582517500610709]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 41960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 41900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360550148201578115, 360550159099689601⟩, ⟨1358165929605417035, 1358475120907605173⟩, true⟩

def words07 : List Nat := [360582518496917776, 360582519493295336, 360582520087504074, 360582520343992161, 360582520344471464, 360582520259878028, 360582520253722253, 360582520254293419, 360582519925247443, 360582519154975633]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 41970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 41900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360631173162738032, 360631184066239893⟩, ⟨(-2043671451685824230), (-2043362034069031946)⟩, true⟩

def words08 : List Nat := [360582518384611315, 360582518258487198, 360582518902954699, 360582519547501037, 360582519704493834, 360582519875894387, 360582520097937024, 360582520320133238, 360582521002197760, 360582522161687274]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 41980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 41900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360636871273268520, 360636882182216246⟩, ⟨(-2283094130280857585), (-2282784483965034091)⟩, true⟩

def words09 : List Nat := [360582523036765263, 360582523911864484, 360582524759611368, 360582525897279539, 360582526741799419, 360582527586372026, 360582528146719511, 360582528875441678, 360582530170030031, 360582531464757971]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 41990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 41900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 41900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk419
