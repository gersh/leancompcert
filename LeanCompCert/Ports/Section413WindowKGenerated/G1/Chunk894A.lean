import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk894A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492643084807793, 362492763961523869⟩, ⟨(-688776715615319265), (-681480370559454313)⟩, true⟩

def state01 : KState := ⟨⟨362480415071961934, 362480535976459005⟩, ⟨404463299222673152, 411762128042852592⟩, true⟩

def words00 : List Nat := [371285141366479960, 371285141369597530, 371285141345730528, 371285141308498820, 371285141270040135, 371285141271017169, 371285141236109011, 371285141267910005, 371285141298452558, 371285141301680377]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 89400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 89400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362497983561311399, 362498104493982621⟩, ⟨(-1166429773277935410), (-1159128425260635116)⟩, true⟩

def words01 : List Nat := [371285141252324727, 371285141243655628, 371285141345988808, 371285141373497737, 371285141378940762, 371285141385360040, 371285141515423788, 371285141601005262, 371285141748100523, 371285141896547336]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 89410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 89400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486249530190835, 362486370490993021⟩, ⟨(-117160026219203494), (-109856162592791566)⟩, true⟩

def words02 : List Nat := [371285142032716614, 371285142035835023, 371285142081917311, 371285142162497413, 371285142246897791, 371285142250016868, 371285142185492882, 371285142120221690, 371285142083490362, 371285142100808491]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 89420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 89400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362477023451731698, 362477144440672674⟩, ⟨708037757939722647, 715344138158284551⟩, true⟩

def words03 : List Nat := [371285142241562758, 371285142383671250, 371285142519946699, 371285142523065907, 371285142515803142, 371285142529367704, 371285142620412633, 371285142623531937, 371285142560273653, 371285142474417736]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 89430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 89400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487113137514874, 362487234154345746⟩, ⟨(-194430137037864893), (-187121262200696695)⟩, true⟩

def words04 : List Nat := [371285142387125516, 371285142348734011, 371285142266391583, 371285142289961794, 371285142292376056, 371285142287499850, 371285142177645056, 371285142159306814, 371285142242088246, 371285142268707792]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 89440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 89400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk894A
