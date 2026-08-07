import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk009

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨359802372059009859, 359802372062331880⟩, ⟨633630167064194925, 633630169105941837⟩, true⟩

def state01 : KState := ⟨⟨360790019271690938, 360790019275091916⟩, ⟨(-265786901481943387), (-265786899368733659)⟩, true⟩

def words00 : List Nat := [360505624192311943, 360505006378581940, 360504536238566276, 360503059976108786, 360501586976108439, 360499766519686225, 360498616099979348, 360498624155653469, 360498624155661029, 360498266366893526]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨361560315471798225, 361560315475279228⟩, ⟨(-973555082283516134), (-973555080097074568)⟩, true⟩

def words01 : List Nat := [360499742740367379, 360501215879728717, 360502722625850809, 360503100929835441, 360503100929843234, 360502421485517513, 360501743523075439, 360500951949586570, 360502103431686638, 360503252413284576]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨359912733893360755, 359912733896923443⟩, ⟨539016526314142998, 539016528576146954⟩, true⟩

def words02 : List Nat := [360503784311279619, 360503784311288186, 360503204219266961, 360502766357807611, 360502329443073368, 360501366340491550, 360499299017680144, 360496597369386546, 360493901537341716, 360492321562059085]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨357729550185352400, 357729550188996867⟩, ⟨2576344006708404368, 2576344009046886254⟩, true⟩

def words03 : List Nat := [360491699018924275, 360490712678710955, 360489728452838004, 360488149155801504, 360485477899392445, 360481812547352694, 360478155018900645, 360475598860443259, 360473260528760890, 360470341687982917]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360243400098332542, 360243400102059805⟩, ⟨201794882269286815, 201794884686009271⟩, true⟩

def words04 : List Nat := [360467429050902886, 360465607504930890, 360464409742571841, 360463393126376994, 360462378661750298, 360460308343368099, 360458337536158416, 360457442251584063, 360456548853802988, 360455815770150342]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨359007025666240913, 359007025670052734⟩, ⟨1388157459229053926, 1388157461726542324⟩, true⟩

def words05 : List Nat := [360455592409834242, 360454805392725769, 360454292701178597, 360455179156760375, 360455731010741204, 360456281711423641, 360456281711431621, 360455923036607172, 360454530843897207, 360453023026017883]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360247236739887650, 360247236743784067⟩, ⟨191190684033582098, 191190686612709084⟩, true⟩

def words06 : List Nat := [360451518346154231, 360450687852159701, 360449862529838052, 360448467216494674, 360447074794990993, 360445370784299018, 360444748753631590, 360444950243026664, 360444950243034733, 360444340544415726]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360856841125227831, 360856841129210081⟩, ⟨(-404137565282193116), (-404137562619375996)⟩, true⟩

def words07 : List Nat := [360444954362226971, 360445769491618511, 360446479390767909, 360446479390777005, 360446187663126960, 360444997499260663, 360443809771756768, 360444034630092588, 360444455861221559, 360444876233573613]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360466631858946363, 360466631863016005⟩, ⟨(-26995936871606338), (-26995934122712236)⟩, true⟩

def words08 : List Nat := [360444876233581805, 360444767892618175, 360443674738718083, 360443578943804229, 360443483343395462, 360443097538726892, 360442716846296978, 360441527676258074, 360440340911010211, 360439390758956760]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360180254299426255, 360180254303583333⟩, ⟨264412881285758852, 264412884121670420⟩, true⟩

def words09 : List Nat := [360440397115886886, 360441401445916602, 360441866843069827, 360442505413324895, 360442868252997871, 360443230364810351, 360444557744865960, 360444931865248657, 360444931865257047, 360444667187705004]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk009
