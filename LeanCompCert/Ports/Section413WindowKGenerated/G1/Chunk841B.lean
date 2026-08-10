import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk841A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk841B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk841A

def state06 : KState := ⟨⟨362471679657262311, 362471786281327461⟩, ⟨1132530793002302518, 1138589886850328808⟩, true⟩

def words05 : List Nat := [371285315935218462, 371285315903297994, 371285315870365184, 371285315838189812, 371285315687925723, 371285315582301930, 371285315475200702, 371285315470236160, 371285315310986077, 371285315153557147]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 84150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 84100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476484284919155, 362476590935170558⟩, ⟨728150962986112867, 734212260799301755⟩, true⟩

def words06 : List Nat := [371285314994836388, 371285314854814807, 371285314663929585, 371285314615314949, 371285314565819379, 371285314505285400, 371285314255692457, 371285314096556007, 371285313935787817, 371285313903696153]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 84160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 84100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474738298646539, 362474844975456438⟩, ⟨875129188665594449, 881192722042447023⟩, true⟩

def words07 : List Nat := [371285313802245710, 371285313701770381, 371285313603023049, 371285313606242208, 371285313540740752, 371285313466995826, 371285313392248830, 371285313317839039, 371285313054426833, 371285312933665543]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 84170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 84100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470568705504480, 362470675408370995⟩, ⟨1226193275382720155, 1232259002341259355⟩, true⟩

def words08 : List Nat := [371285312827978602, 371285312830951905, 371285312733092471, 371285312609238454, 371285312484233276, 371285312396178449, 371285312236933524, 371285312185219463, 371285312132574138, 371285312051705611]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 84180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 84100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362498252086500000, 362498358815794479⟩, ⟨(-1104604868668206467), (-1098536916606857117)⟩, true⟩

def words09 : List Nat := [371285311879836572, 371285311850531538, 371285311900306935, 371285311903250104, 371285311882491642, 371285311840434355, 371285311881617476, 371285311898818193, 371285312055751262, 371285312214012947]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 84190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 84100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 84100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk841B
