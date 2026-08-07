import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk875

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362493619660354646, 362493735261906880⟩, ⟨(-755476000966651809), (-748646264016662813)⟩, true⟩

def state01 : KState := ⟨⟨362475825037514680, 362475940666516340⟩, ⟨801598274795561320, 808430413713465096⟩, true⟩

def words00 : List Nat := [371285179502488213, 371285179505534945, 371285179454406897, 371285179463121170, 371285179465276461, 371285179462207225, 371285179284442193, 371285179084970551, 371285178884290513, 371285178815456044]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 87500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 87500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362478458963384789, 362478574619872345⟩, ⟨571149953547515469, 577984497890009163⟩, true⟩

def words01 : List Nat := [371285178736819959, 371285178765016565, 371285178791862642, 371285178794971137, 371285178749394951, 371285178721125065, 371285178789670916, 371285178792717713, 371285178719489681, 371285178647499059]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 87510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 87500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479557181082283, 362479672864857704⟩, ⟨475064423620734472, 481901356338971616⟩, true⟩

def words02 : List Nat := [371285178574144747, 371285178556179164, 371285178542437650, 371285178603009084, 371285178641943068, 371285178644990318, 371285178524633627, 371285178462012302, 371285178418156137, 371285178421310795]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 87520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 87500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362480511327209738, 362480627038696501⟩, ⟨391519717815265816, 398359076250668250⟩, true⟩

def words03 : List Nat := [371285178360690064, 371285178294610258, 371285178227328753, 371285178214855700, 371285178136854749, 371285178045698424, 371285177953474656, 371285177862095923, 371285177681823818, 371285177633581704]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 87530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 87500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485233257335458, 362485348995991693⟩, ⟨(-21812617492747682), (-14970880502401686)⟩, true⟩

def words04 : List Nat := [371285177662032585, 371285177674438520, 371285177679058865, 371285177684716798, 371285177729223076, 371285177732581874, 371285177819341323, 371285177930132891, 371285177994759676, 371285177999880828]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 87540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 87500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362506214390121212, 362506330156375992⟩, ⟨(-1858827609128311282), (-1851983455753601324)⟩, true⟩

def words05 : List Nat := [371285178101669132, 371285178205122738, 371285178437217153, 371285178496476810, 371285178544994236, 371285178594479813, 371285178772992053, 371285178887618598, 371285179131248695, 371285179376282645]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 87550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 87500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362487375984857111, 362487491778662979⟩, ⟨(-209293516257444984), (-202446950369908878)⟩, true⟩

def words06 : List Nat := [371285179605002201, 371285179660676920, 371285179769719436, 371285179880270884, 371285180023190033, 371285180026238505, 371285179995531322, 371285179943229199, 371285179945122324, 371285179975093648]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 87560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 87500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362467298933273163, 362467414754448739⟩, ⟨1548992209441896994, 1555841172236330244⟩, true⟩

def words07 : List Nat := [371285180045023334, 371285180116146502, 371285180186329189, 371285180189377815, 371285180085690965, 371285180019988489, 371285179952713108, 371285179940467121, 371285179753757681, 371285179554314420]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 87570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 87500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482578740902500, 362482694589390633⟩, ⟨210723468873814487, 217574823838927193⟩, true⟩

def words08 : List Nat := [371285179353553136, 371285179240821900, 371285179081508720, 371285179053771752, 371285179024969976, 371285178975767974, 371285178751899474, 371285178659828309, 371285178600656136, 371285178603819666]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 87580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 87500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362485028838619214, 362485144714943341⟩, ⟨(-3914607438370772), 2939185821344150⟩, true⟩

def words09 : List Nat := [371285178577780341, 371285178512659289, 371285178446285064, 371285178448461051, 371285178400609815, 371285178393921490, 371285178386251551, 371285178379703622, 371285178263849776, 371285178267292900]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 87590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 87500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 87500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk875
