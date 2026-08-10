import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk811A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492625909210958, 362492724638734961⟩, ⟨(-617511673572087262), (-612104986726557764)⟩, true⟩

def state01 : KState := ⟨⟨362490002408844487, 362490101163521166⟩, ⟨(-404665743188143878), (-399257016331437470)⟩, true⟩

def words00 : List Nat := [371285177445015687, 371285177637710825, 371285177884496773, 371285178132444626, 371285178354479282, 371285178391280573, 371285178488244816, 371285178586651855, 371285178746408490, 371285178810001528]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 81100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 81100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362494021991394085, 362494120771674606⟩, ⟨(-730704336647485073), (-725293532935517223)⟩, true⟩

def words01 : List Nat := [371285178865500269, 371285178921966357, 371285179092099324, 371285179209578337, 371285179372619815, 371285179536760080, 371285179699692496, 371285179702499608, 371285179772908964, 371285179886664122]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 81110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 81100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362485589359317361, 362485688164626537⟩, ⟨(-46616231795571993), (-41203397628367779)⟩, true⟩

def words02 : List Nat := [371285180106622071, 371285180152283874, 371285180168014196, 371285180184638599, 371285180190684409, 371285180193807184, 371285180178607696, 371285180236207809, 371285180292839321, 371285180302063172]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 81120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 81100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362495009535907007, 362495108366536849⟩, ⟨(-810901036289730887), (-805486147725372293)⟩, true⟩

def words03 : List Nat := [371285180462117138, 371285180623592813, 371285180875040534, 371285180943949727, 371285180985269749, 371285181027498638, 371285181112986729, 371285181123705151, 371285181247957237, 371285181373429476]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 81130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 81100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485028682058936, 362485127538038845⟩, ⟨(-1041075662313759), 4375869930444077⟩, true⟩

def words04 : List Nat := [371285181464217063, 371285181467027659, 371285181445335774, 371285181501805227, 371285181603444750, 371285181606266399, 371285181562770494, 371285181491789934, 371285181458059119, 371285181461266577]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 81140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 81100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk811A
