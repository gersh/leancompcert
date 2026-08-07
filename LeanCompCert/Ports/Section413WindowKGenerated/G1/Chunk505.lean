import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk505

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362470980506488722, 362471017386114327⟩, ⟨706752691716631805, 708010926388837611⟩, true⟩

def state01 : KState := ⟨⟨362479127366609794, 362479164261319585⟩, ⟨295349507181302419, 296608503681112825⟩, true⟩

def words00 : List Nat := [371285037127992129, 371285037053620838, 371285036992845723, 371285037159510824, 371285037235154810, 371285037236841307, 371285036790149034, 371285036594741919, 371285036532463985, 371285036534209728]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 50500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 50500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488985564185329, 362489022474297631⟩, ⟨(-202602196113473176), (-201342421556054392)⟩, true⟩

def words01 : List Nat := [371285036419213909, 371285036293834863, 371285036431854073, 371285036502063334, 371285036691770145, 371285036882099376, 371285037071969483, 371285037073666108, 371285037071925462, 371285037152915314]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 50510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 50500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362479616078309521, 362479653003451389⟩, ⟨270779166696164194, 272039700625564390⟩, true⟩

def words02 : List Nat := [371285037517684421, 371285037519371425, 371285037362453849, 371285037128784734, 371285036894492457, 371285036738335329, 371285036536461173, 371285036632398843, 371285036728215116, 371285036729962879]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 50520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 50500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362502314330883403, 362502351271271340⟩, ⟨(-876326289367814440), (-875064984975254052)⟩, true⟩

def words03 : List Nat := [371285036690932143, 371285036759289440, 371285036989575990, 371285036991274737, 371285036871212480, 371285036695796079, 371285036666943980, 371285036668803192, 371285036964152201, 371285037308647426]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 50530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 50500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483434696251924, 362483471651867176⟩, ⟨77884669929436409, 79146743985597911⟩, true⟩

def words04 : List Nat := [371285037599363602, 371285037601052098, 371285037672720367, 371285037905525420, 371285038150898358, 371285038152586166, 371285037925963754, 371285037608491056, 371285037361987321, 371285037363914369]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 50540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 50500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362486605774380500, 362486642745213263⟩, ⟨(-82330991732297917), (-81068148353751719)⟩, true⟩

def words05 : List Nat := [371285037693989940, 371285038055725037, 371285038377390170, 371285038443489311, 371285038629085196, 371285038815502071, 371285039260744582, 371285039305480468, 371285039338459323, 371285039372092602]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 50550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 50500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362490599648537912, 362490636634501054⟩, ⟨(-284271426733388674), (-283007818287055854)⟩, true⟩

def words06 : List Nat := [371285039528167821, 371285039530045723, 371285039799345581, 371285040093862269, 371285040322496936, 371285040324185478, 371285040078797689, 371285040034944139, 371285040274859120, 371285040387278594]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 50560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 50500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495682213819202, 362495719215157141⟩, ⟨(-541313735591559897), (-540049349563517477)⟩, true⟩

def words07 : List Nat := [371285040499846810, 371285040612952136, 371285041071598387, 371285041335614008, 371285041551782088, 371285041768585705, 371285041955364176, 371285041957068120, 371285042080808960, 371285042293989835]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 50570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 50500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362493874733978957, 362493911750364213⟩, ⟨(-449796252538870214), (-448531105337334682)⟩, true⟩

def words08 : List Nat := [371285042896597869, 371285043175101052, 371285043447066851, 371285043719600075, 371285044070442539, 371285044226775721, 371285044772731578, 371285045319336599, 371285045745347622, 371285045922344658]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 50580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 50500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362531516437979114, 362531553469672119⟩, ⟨(-2354261652124693760), (-2352995730431974532)⟩, true⟩

def words09 : List Nat := [371285046489038444, 371285047056615400, 371285048013554551, 371285048519286269, 371285048959790120, 371285049400826609, 371285050124950127, 371285050655661358, 371285051575835976, 371285052496757909]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 50590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 50500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 50500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk505
