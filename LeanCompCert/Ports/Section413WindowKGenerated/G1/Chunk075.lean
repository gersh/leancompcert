import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk075

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362412612201310547, 362412612890207967⟩, ⟨540681701957727263, 540685200844369917⟩, true⟩

def state01 : KState := ⟨⟨362390343806836008, 362390344497638856⟩, ⟨708026925761742962, 708030438948987810⟩, true⟩

def words00 : List Nat := [371284696334153384, 371284696334368695, 371284684605449972, 371284670404945555, 371284656208138180, 371284645886400430, 371284626902751894, 371284625552608128, 371284624202754542, 371284622851693316]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 7500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 7500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362547984132475082, 362547984825217203⟩, ⟨(-477102636592916667), (-477099108831945843)⟩, true⟩

def words01 : List Nat := [371284610299804105, 371284599742584615, 371284589188065228, 371284587873463491, 371284573537964324, 371284555987100973, 371284538483925882, 371284538484165455, 371284540794544413, 371284549230371844]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 7510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 7500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362448806722228956, 362448807416903791⟩, ⟨268688188779976823, 268691731084792455⟩, true⟩

def words02 : List Nat := [371284556426585439, 371284556426799736, 371284541491674767, 371284542803658329, 371284544275275832, 371284544275490257, 371284526286922971, 371284508423771407, 371284490565277032, 371284490249717177]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 7520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 7500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362286879287650887, 362286879984259790⟩, ⟨1489351528794823926, 1489355085673126086⟩, true⟩

def words03 : List Nat := [371284491922718434, 371284498332232226, 371284505017007879, 371284505017222547, 371284488327865898, 371284471675038092, 371284455881909656, 371284455882124415, 371284433384427435, 371284407183951187]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 7530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 7500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362534179024306556, 362534179722839414⟩, ⟨(-376316431769240200), (-376312860374506892)⟩, true⟩

def words04 : List Nat := [371284380990330143, 371284372289440036, 371284354974626941, 371284350057944719, 371284345142497437, 371284337495019982, 371284319897765817, 371284319766332183, 371284336959653177, 371284343560692082]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 7540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 7500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362464537968237406, 362464538668737184⟩, ⟨149877778714811188, 149881364969464562⟩, true⟩

def words05 : List Nat := [371284350100061910, 371284356637773566, 371284367280294772, 371284369235792499, 371284376476737414, 371284383715845675, 371284386913525070, 371284386913740405, 371284366868617238, 371284364246114098]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 7550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 7500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362353023639970693, 362353024342390588⟩, ⟨994061470952547732, 994065071733212344⟩, true⟩

def words06 : List Nat := [371284376415389064, 371284376415604897, 371284373713528328, 371284370953214297, 371284368193550570, 371284366020297108, 371284357358205789, 371284352224642948, 371284347092361913, 371284340732315716]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 7560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 7500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362556405839586546, 362556406543953730⟩, ⟨(-546165379370678279), (-546161763838792549)⟩, true⟩

def words07 : List Nat := [371284323387806757, 371284320372329865, 371284331708238689, 371284331781505722, 371284331781673260, 371284328309409414, 371284338721091030, 371284344033492620, 371284353540568783, 371284363045228128]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 7570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 7500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478068515966902, 362478069222287151⟩, ⟨47512525049999365, 47516155395973345⟩, true⟩

def words08 : List Nat := [371284369044537493, 371284369044754126, 371284363763616717, 371284369791952305, 371284376763188990, 371284376763405163, 371284360642218770, 371284344513899913, 371284329585068739, 371284329585316924]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 7580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 7500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362391677666138301, 362391678374409215⟩, ⟨704278919773623678, 704282564934995654⟩, true⟩

def words09 : List Nat := [371284345248768857, 371284361732676512, 371284378147274393, 371284378147490966, 371284371511970495, 371284365902164229, 371284368713289604, 371284368713506435, 371284359327569238, 371284347132953294]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 7590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 7500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 7500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk075
