import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk920A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362496905271364920, 362497033564636670⟩, ⟨(-1106023213863705509), (-1098054136424235371)⟩, true⟩

def state01 : KState := ⟨⟨362490593362560982, 362490721684877005⟩, ⟨(-525340572967944832), (-517368823310328414)⟩, true⟩

def words00 : List Nat := [371285098435758830, 371285098438975188, 371285098488679702, 371285098575332124, 371285098696610389, 371285098699827021, 371285098675006821, 371285098651722058, 371285098718232230, 371285098783014072]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 92000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 92000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478728208414975, 362478856559655789⟩, ⟨566489669412522370, 574464080584973836⟩, true⟩

def words01 : List Nat := [371285098947355743, 371285099112974348, 371285099277315287, 371285099329168471, 371285099363411842, 371285099399275748, 371285099492532471, 371285099495749635, 371285099441567363, 371285099377310484]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 92010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 92000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484776996982573, 362484905377039261⟩, ⟨9888445107017757, 17865508065359185⟩, true⟩

def words02 : List Nat := [371285099318190524, 371285099321799096, 371285099337186436, 371285099389670815, 371285099422035932, 371285099425276496, 371285099397167302, 371285099425158061, 371285099500711001, 371285099504042036]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 92020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 92000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362488970709703582, 362489099119122059⟩, ⟨(-376065812127165678), (-368086046859028042)⟩, true⟩

def words03 : List Nat := [371285099504337355, 371285099505554176, 371285099621088871, 371285099681165503, 371285099769444981, 371285099858994326, 371285099925917902, 371285099929144515, 371285099918574693, 371285099966061369]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 92030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 92000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362486336396954957, 362486464835063470⟩, ⟨(-133588248983115851), (-125605842936910893)⟩, true⟩

def words04 : List Nat := [371285100129673003, 371285100137037717, 371285100139510084, 371285100125641119, 371285100112302431, 371285100115857197, 371285100150880141, 371285100225354515, 371285100292365683, 371285100310583162]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 92040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 92000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk920A
