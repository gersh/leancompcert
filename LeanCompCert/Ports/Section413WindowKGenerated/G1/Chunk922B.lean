import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk922A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk922B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk922A

def state06 : KState := ⟨⟨362483553048429894, 362483682096161469⟩, ⟨123159192018857159, 131197777942248633⟩, true⟩

def words05 : List Nat := [371285103303268587, 371285103532697642, 371285103737092982, 371285103795783789, 371285103889519678, 371285103984900055, 371285104138564391, 371285104149459005, 371285104151902148, 371285104140145235]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 92250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 92200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485368675696811, 362485497752271602⟩, ⟨(-44339682487274488), (-36298435338368970)⟩, true⟩

def words06 : List Nat := [371285104170360355, 371285104173915641, 371285104252781932, 371285104348151800, 371285104423913279, 371285104427139398, 371285104346104005, 371285104311874993, 371285104355246303, 371285104362849808]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 92260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 92200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362491553311513771, 362491682417518450⟩, ⟨(-615008989259693060), (-606965026469313462)⟩, true⟩

def words07 : List Nat := [371285104369279972, 371285104376843362, 371285104484319725, 371285104561569015, 371285104673063034, 371285104785774395, 371285104897812474, 371285104912329057, 371285104985809296, 371285105061112806]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 92270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 92200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480551821997872, 362480680956787380⟩, ⟨400251023310266675, 408297642513626907⟩, true⟩

def words08 : List Nat := [371285105183549162, 371285105186775717, 371285105152933116, 371285105118173225, 371285105082206803, 371285105083544734, 371285105025542970, 371285105027322974, 371285105027904041, 371285105029195156]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 92280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 92200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489999450840039, 362490128614716022⟩, ⟨(-471729164044972227), (-463679860301870739)⟩, true⟩

def words09 : List Nat := [371285105024304653, 371285105068987521, 371285105164296219, 371285105167523219, 371285105106773471, 371285105021596994, 371285104963708505, 371285104967264963, 371285104993977250, 371285105052021124]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 92290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 92200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 92200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk922B
