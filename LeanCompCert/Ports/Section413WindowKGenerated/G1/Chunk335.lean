import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk335

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488446899755156, 362488462593880704⟩, ⟨(-128666447857772530), (-128311106906061198)⟩, true⟩

def state01 : KState := ⟨⟨362477494382931375, 362477510086840189⟩, ⟨238302756748489120, 238658425490553582⟩, true⟩

def words00 : List Nat := [371284632631712917, 371284632632814833, 371284632260062727, 371284632519762404, 371284633051126990, 371284633052217585, 371284632788058422, 371284632434755829, 371284632091737613, 371284632092972405]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 33500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 33500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362447891137124755, 362447906850804530⟩, ⟨1230575327784472918, 1230931324000428384⟩, true⟩

def words01 : List Nat := [371284632105803438, 371284632331596232, 371284632556538155, 371284632557626888, 371284631937667999, 371284631590748459, 371284631333478284, 371284631334561985, 371284630240008679, 371284629145673278]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 33510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 33500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362467261755839277, 362467277479230786⟩, ⟨581221779907423397, 581578101710104583⟩, true⟩

def words02 : List Nat := [371284628050907980, 371284627845864056, 371284627230408392, 371284626980647438, 371284626730579101, 371284626302252733, 371284624688628060, 371284623658630188, 371284622628115761, 371284622486737798]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 33520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 33500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362466074266127951, 362466089999383565⟩, ⟨621143532886259764, 621500185481355224⟩, true⟩

def words03 : List Nat := [371284621970265940, 371284621454212533, 371284621309046666, 371284621310254595, 371284621485279866, 371284621666604767, 371284621675263577, 371284621676348370, 371284620669369720, 371284620118211274]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 33530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 33500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362464061929266265, 362464077672174516⟩, ⟨688632316987941693, 688989293383061545⟩, true⟩

def words04 : List Nat := [371284619567798682, 371284619568884138, 371284618577839562, 371284617586920595, 371284616595616302, 371284615877017223, 371284614714494409, 371284614440257306, 371284614165681052, 371284613865717976]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 33540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 33500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362488953209835233, 362488968962574148⟩, ⟨(-146662906700296205), (-146305600437381321)⟩, true⟩

def words05 : List Nat := [371284613254378403, 371284613008515938, 371284612876956795, 371284612878044026, 371284612077845387, 371284611129508522, 371284610180798721, 371284609858703994, 371284609438090807, 371284609569217652]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 33550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 33500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469736126354184, 362469751888884439⟩, ⟨498244927979765941, 498602562890843427⟩, true⟩

def words06 : List Nat := [371284609570043202, 371284609553476344, 371284608483044438, 371284608300277745, 371284608117012318, 371284607947453471, 371284606935352162, 371284605832064305, 371284604728386553, 371284604512146008]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 33560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 33500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362443780452095959, 362443796224405144⟩, ⟨1369835066946823992, 1370193030186401458⟩, true⟩

def words07 : List Nat := [371284604326242531, 371284604583206904, 371284604850663135, 371284604851748897, 371284603937502464, 371284603095189217, 371284602295238493, 371284602296324405, 371284601280825105, 371284600066876449]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 33570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 33500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362482395570251311, 362482411352274437⟩, ⟨72989821566689148, 73348111050932378⟩, true⟩

def words08 : List Nat := [371284598852526461, 371284598524988085, 371284597847937049, 371284597456462721, 371284597064660043, 371284596526230521, 371284595253688993, 371284594867886323, 371284594980535447, 371284594981659699]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 33580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 33500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487471375597407, 362487487167550588⟩, ⟨(-97530544775192262), (-97171921693839172)⟩, true⟩

def words09 : List Nat := [371284594917465706, 371284594852438988, 371284595084551173, 371284595085755663, 371284595334272342, 371284595594728140, 371284595856242991, 371284595857329712, 371284595144685781, 371284595232141111]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 33590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 33500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 33500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk335
