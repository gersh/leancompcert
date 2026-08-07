import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk381

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486548782064197, 362486569299156471⟩, ⟨(-60213208271036888), (-59684948652764230)⟩, true⟩

def state01 : KState := ⟨⟨362468665353762594, 362468685881953384⟩, ⟨621206120258573522, 621734802787746602⟩, true⟩

def words00 : List Nat := [371285003131281469, 371285003132526513, 371285002540302045, 371285001934001180, 371285001327235885, 371285000930264425, 371285000284417273, 371285000222991209, 371285000161136453, 371285000098767547]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 38100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 38100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362519751461625180, 362519772001080959⟩, ⟨(-1325941929087990214), (-1325412817193509796)⟩, true⟩

def words01 : List Nat := [371284999737206398, 371284999804373580, 371285000559029043, 371285000811087258, 371285000812083255, 371285000809738753, 371285001374831451, 371285001600410538, 371285002513385907, 371285003426877935]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 38110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 38100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362499625243292833, 362499645793999493⟩, ⟨(-558632650110755810), (-558103109275519648)⟩, true⟩

def words02 : List Nat := [371285004272015951, 371285004554279036, 371285005400608373, 371285006247538892, 371285007260408136, 371285007660882777, 371285008036450962, 371285008412435831, 371285008942085181, 371285009327364065]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 38120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 38100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362468253199524446, 362468273761430793⟩, ⟨637850968253431839, 638380936190416399⟩, true⟩

def words03 : List Nat := [371285010141322415, 371285010955730850, 371285011710577196, 371285011725417990, 371285011856721080, 371285011988668103, 371285012467252355, 371285012468498760, 371285012031528627, 371285011594052461]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 38130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 38100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488112728989356, 362488133302073221⟩, ⟨(-119670812511564185), (-119140418208581559)⟩, true⟩

def words04 : List Nat := [371285011280857245, 371285011282249387, 371285011318175291, 371285011478474959, 371285011528883871, 371285011530130465, 371285010665240712, 371285010333259757, 371285010354017168, 371285010437188721]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 38140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 38100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362477951088543132, 362477971672998710⟩, ⟨268143741520183519, 268674569710665799⟩, true⟩

def words05 : List Nat := [371285010497731820, 371285010558696482, 371285011305832558, 371285011710463239, 371285012225161091, 371285012740293452, 371285013123964737, 371285013125211636, 371285012594134319, 371285012411198676]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 38150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 38100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362470335342378174, 362470355937935796⟩, ⟨558791624910876364, 559322876813175424⟩, true⟩

def words06 : List Nat := [371285012613758734, 371285012615005712, 371285012087737806, 371285011560039774, 371285011031881402, 371285010569092580, 371285009762885796, 371285009643399414, 371285009523489899, 371285009406021025]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 38160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 38100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495676181277370, 362495696788104251⟩, ⟨(-408691167267499808), (-408159485160380788)⟩, true⟩

def words07 : List Nat := [371285009022994553, 371285008722187813, 371285008679389779, 371285008680637257, 371285008026393736, 371285007267842257, 371285006508806406, 371285006436128803, 371285006386368383, 371285006667752234]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 38170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 38100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483127616020934, 362483148234089840⟩, ⟨70375325928513138, 70907437313673084⟩, true⟩

def words08 : List Nat := [371285006824126853, 371285006825377961, 371285006427067443, 371285006571768777, 371285006753320022, 371285006754568135, 371285006126628796, 371285005501312487, 371285004934348091, 371285004935773885]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 38180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 38100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362477177371004183, 362477198000344731⟩, ⟨297784718110742520, 298317260016110478⟩, true⟩

def words09 : List Nat := [371285005459044350, 371285006031458396, 371285006557628068, 371285006558882359, 371285006606687629, 371285006735590488, 371285007548972624, 371285007554773143, 371285007555725105, 371285007352701174]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 38190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 38100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 38100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk381
