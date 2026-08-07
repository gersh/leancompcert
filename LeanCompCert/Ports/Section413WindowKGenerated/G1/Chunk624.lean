import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk624

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362479624136827714, 362479681405142508⟩, ⟨355702327706039122, 358116090061616516⟩, true⟩

def state01 : KState := ⟨⟨362467150050779568, 362467207337931325⟩, ⟨1134183847938628733, 1136598785820207777⟩, true⟩

def words00 : List Nat := [371285420519525644, 371285420521644683, 371285420391034845, 371285420207652680, 371285420023510408, 371285419854035661, 371285419555181355, 371285419419056427, 371285419282200053, 371285419143504474]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 62400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 62400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362489847565192559, 362489904871494381⟩, ⟨(-282441977730210168), (-280025844595486746)⟩, true⟩

def words01 : List Nat := [371285418853137047, 371285418801450618, 371285418863245610, 371285418865378489, 371285418752027642, 371285418626890961, 371285418630260834, 371285418640006778, 371285418713341506, 371285418787570774]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 62410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 62400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490073621880493, 362490130947297264⟩, ⟨(-296596489341842843), (-294179162955835227)⟩, true⟩

def words02 : List Nat := [371285418859999647, 371285418862122007, 371285418752956898, 371285418828646040, 371285418900533930, 371285418902700626, 371285418821891144, 371285418740777341, 371285418800671695, 371285418878566092]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 62420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 62400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483100731922674, 362483158076469170⟩, ⟨138830799622521996, 141249320373684364⟩, true⟩

def words03 : List Nat := [371285419177143971, 371285419476604205, 371285419721227906, 371285419761084071, 371285419877751176, 371285419995457226, 371285420303062160, 371285420305181489, 371285420271057836, 371285420237269518]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 62430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 62400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479078288377627, 362479135651876371⟩, ⟨390059628113094903, 392479332341389887⟩, true⟩

def words04 : List Nat := [371285420328093893, 371285420330451094, 371285420520304637, 371285420713703452, 371285420847759581, 371285420849879188, 371285420641987221, 371285420463931794, 371285420346754867, 371285420348951494]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 62440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 62400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362494959366268353, 362495016749075369⟩, ⟨(-601812179161891220), (-599391269034431668)⟩, true⟩

def words05 : List Nat := [371285420249918448, 371285420147783875, 371285420120391910, 371285420122768336, 371285420164231803, 371285420225299156, 371285420290021255, 371285420292161428, 371285420344447591, 371285420500711840]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 62450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 62400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478816598003202, 362478873999714640⟩, ⟨406544238537870432, 408966329532739254⟩, true⟩

def words06 : List Nat := [371285420761489190, 371285420763609308, 371285420682902205, 371285420595890951, 371285420508048016, 371285420465210585, 371285420429458077, 371285420541369908, 371285420601162069, 371285420603356913]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 62460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 62400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362505485808663553, 362505543229569089⟩, ⟨(-1259615089473487204), (-1257191799330688270)⟩, true⟩

def words07 : List Nat := [371285420624255003, 371285420751066662, 371285421133073473, 371285421174273697, 371285421175950128, 371285421126717915, 371285421281425250, 371285421395978884, 371285421719470210, 371285422043939367]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 62470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 62400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362493445157934302, 362493502597951933⟩, ⟨(-507252589805525838), (-504828105439348390)⟩, true⟩

def words08 : List Nat := [371285422344978077, 371285422434207185, 371285422778968520, 371285423124796069, 371285423547029802, 371285423655826271, 371285423755761320, 371285423856413373, 371285424053279082, 371285424184973435]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 62480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 62400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362468314342195446, 362468371801313597⟩, ⟨1063306723273975471, 1065732401324332859⟩, true⟩

def words09 : List Nat := [371285424325133168, 371285424466116588, 371285424577931915, 371285424580053229, 371285424350501836, 371285424168346558, 371285424056362732, 371285424058484135, 371285423790200875, 371285423519734787]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 62490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 62400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 62400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk624
