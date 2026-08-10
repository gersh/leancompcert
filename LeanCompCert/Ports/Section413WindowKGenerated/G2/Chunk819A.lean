import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk819A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360581703973246347, 360581747742652668⟩, ⟨41436649486000485, 43857618509476901⟩, true⟩

def state01 : KState := ⟨⟨360582214120322413, 360582257900769944⟩, ⟨(-333329760846986), 2088543593231026⟩, true⟩

def words00 : List Nat := [360582283381539304, 360582283435443890, 360582283436490785, 360582283395590482, 360582283354499851, 360582283331136270, 360582283382907812, 360582283434886372, 360582283435943924, 360582283398799406]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 81900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 81900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360607428539564969, 360607472331084567⟩, ⟨(-2065808898082254986), (-2063386117759888848)⟩, true⟩

def words01 : List Nat := [360582283510137321, 360582283622128323, 360582283778137799, 360582283937908399, 360582283965729355, 360582283993640408, 360582284042727084, 360582284202628399, 360582284511049395, 360582284819728995]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 81910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 81900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360598373044250224, 360598416846967249⟩, ⟨(-1324104087823595347), (-1321680390153770981)⟩, true⟩

def words02 : List Nat := [360582285011490237, 360582285054695733, 360582285094191155, 360582285134027390, 360582285135011765, 360582285105960939, 360582285103929350, 360582285027161177, 360582285021020024, 360582285219254250]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 81920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 81900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360580508257888137, 360580552071653810⟩, ⟨139714595347444203, 142139198289314877⟩, true⟩

def words03 : List Nat := [360582285565940973, 360582285912844141, 360582286176365007, 360582286336741772, 360582286394519551, 360582286452602187, 360582286659161153, 360582286764678342, 360582286765736444, 360582286745784752]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 81930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 81900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360597102655107565, 360597146479967436⟩, ⟨(-1220050794974296542), (-1217625282918957720)⟩, true⟩

def words04 : List Nat := [360582286810229796, 360582287011746922, 360582287361702407, 360582287711874305, 360582287933472032, 360582288006562350, 360582288130310262, 360582288254397841, 360582288330079523, 360582288512609882]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 81940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 81900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk819A
