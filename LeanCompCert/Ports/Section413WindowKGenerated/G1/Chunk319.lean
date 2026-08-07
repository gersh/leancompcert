import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk319

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362436254668790607, 362436268842056741⟩, ⟨1558667247282731098, 1558972845255472388⟩, true⟩

def state01 : KState := ⟨⟨362470453903544872, 362470468086001961⟩, ⟨467594882140034235, 467900773351855813⟩, true⟩

def words00 : List Nat := [371285137932918697, 371285136843210398, 371285135395479414, 371285134776474909, 371285134157183089, 371285133388114280, 371285131958078040, 371285131506941027, 371285131224184713, 371285131225248337]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 31900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 31900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362444856219503070, 362444870411349691⟩, ⟨1284541661855550619, 1284847852732808255⟩, true⟩

def words01 : List Nat := [371285130766521123, 371285130100809605, 371285129434726043, 371285128991905321, 371285128072042673, 371285127327771301, 371285126583209401, 371285125843027215, 371285123796822029, 371285122537061872]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 31910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 31900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362434339253504739, 362434353454502252⟩, ⟨1620398569694511847, 1620705052716205833⟩, true⟩

def words02 : List Nat := [371285121276767862, 371285120870314769, 371285119583449947, 371285118290977599, 371285116998201796, 371285115991741254, 371285114589897955, 371285113597684183, 371285112605172539, 371285111520669375]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 31920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 31900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362474086564964102, 362474100775243422⟩, ⟨351092320969523658, 351399100407902806⟩, true⟩

def words03 : List Nat := [371285109931750850, 371285109103621033, 371285108275016239, 371285107957900870, 371285106826411558, 371285105529814902, 371285104232867520, 371285103846732801, 371285102968919690, 371285102625600589]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 31930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 31900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362431819407001179, 362431833626584863⟩, ⟨1701191835531387915, 1701498912197640359⟩, true⟩

def words04 : List Nat := [371285102281952247, 371285101787645451, 371285099989442032, 371285098813448896, 371285097637004926, 371285096765590534, 371285094590772463, 371285092350233462, 371285090109407281, 371285088678609829]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 31940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 31900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362428508840386775, 362428523069239324⟩, ⟨1807085434773499276, 1807392807627369262⟩, true⟩

def words05 : List Nat := [371285087012535912, 371285086189260212, 371285085365676222, 371285084546501819, 371285082790674822, 371285080949599643, 371285079108119193, 371285078241869090, 371285076552461281, 371285074784121282]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 31950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 31900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362459427679032122, 362459441917117454⟩, ⟨818910339800701401, 819218007780403857⟩, true⟩

def words06 : List Nat := [371285073015423120, 371285072065236646, 371285070763748074, 371285070437140581, 371285070110242672, 371285069618290321, 371285068247369613, 371285067529757797, 371285066811643057, 371285066502909772]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 31960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 31900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362468576098014905, 362468590345467429⟩, ⟨526450542587129206, 526758510083755344⟩, true⟩

def words07 : List Nat := [371285065702185379, 371285064906242219, 371285064286718477, 371285064287852908, 371285064039999236, 371285064059891858, 371285064060678286, 371285063786297207, 371285062357396907, 371285061843593876]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 31970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 31900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362456640218951107, 362456654475588025⟩, ⟨908239255664136267, 908547516926451293⟩, true⟩

def words08 : List Nat := [371285061787528375, 371285061788558571, 371285060947424601, 371285059906880564, 371285058865994523, 371285058129830220, 371285056908267819, 371285056424398090, 371285055940213375, 371285055460799856]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 31980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 31900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362477626429368414, 362477640695327042⟩, ⟨236858246950174108, 237166806459732238⟩, true⟩

def words09 : List Nat := [371285054658543898, 371285054744606056, 371285055215199899, 371285055216233250, 371285054690074511, 371285054035318030, 371285053380203322, 371285053129348657, 371285052388470697, 371285052158028909]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 31990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 31900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 31900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk319
