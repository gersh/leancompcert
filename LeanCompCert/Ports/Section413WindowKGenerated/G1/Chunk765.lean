import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk765

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362488754895366680, 362488842348999005⟩, ⟨(-282841323362190815), (-278323447690324027)⟩, true⟩

def state01 : KState := ⟨⟨362485877803292861, 362485965280417172⟩, ⟨(-62721304415378884), (-58201631483243784)⟩, true⟩

def words00 : List Nat := [371285204393162181, 371285204420923080, 371285204422928139, 371285204417446931, 371285204410953519, 371285204403153397, 371285204400884298, 371285204487043201, 371285204571438295, 371285204584158030]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 76500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 76500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362501725487993986, 362501812988981805⟩, ⟨(-1275295954914111903), (-1270774456065724801)⟩, true⟩

def words01 : List Nat := [371285204766570671, 371285204950384242, 371285205259199347, 371285205365083889, 371285205443059571, 371285205521852502, 371285205628770621, 371285205678098288, 371285205896919169, 371285206116932751]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 76510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 76500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362488284384015012, 362488371908774892⟩, ⟨(-246760515594687299), (-242237197583031115)⟩, true⟩

def words02 : List Nat := [371285206325848682, 371285206328486078, 371285206428363512, 371285206550219626, 371285206722681301, 371285206725319121, 371285206692542234, 371285206628351566, 371285206647729158, 371285206692096905]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 76520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 76500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485272339273542, 362485359887793527⟩, ⟨(-16251899544356225), (-11726763052010143)⟩, true⟩

def words03 : List Nat := [371285206753216605, 371285206815349717, 371285206859484494, 371285206862129515, 371285206731472516, 371285206654281477, 371285206665850163, 371285206669968525, 371285206673943420, 371285206678885204]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 76530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 76500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362492598506824531, 362492686078939056⟩, ⟨(-576964446051449170), (-572437503513142246)⟩, true⟩

def words04 : List Nat := [371285206853240802, 371285206943413797, 371285207203029466, 371285207463768312, 371285207681439870, 371285207684078007, 371285207791850732, 371285207912779081, 371285208120574264, 371285208220994508]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 76540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 76500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362486266019948904, 362486353616170423⟩, ⟨(-92148184726087789), (-87619396681548857)⟩, true⟩

def words05 : List Nat := [371285208298686768, 371285208377332256, 371285208586884601, 371285208712862502, 371285208875206366, 371285209038532600, 371285209195503973, 371285209198142621, 371285209158860319, 371285209177139043]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 76550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 76500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362486071326374871, 362486158946078423⟩, ⟨(-77237986918212355), (-72707400966977015)⟩, true⟩

def words06 : List Nat := [371285209364347262, 371285209366985812, 371285209327105922, 371285209283280598, 371285209243883312, 371285209246841452, 371285209255909275, 371285209322732658, 371285209388657018, 371285209403810894]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 76560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 76500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497046167158825, 362497133810711485⟩, ⟨(-917673886589368581), (-913141474389257143)⟩, true⟩

def words07 : List Nat := [371285209506221711, 371285209609989387, 371285209783444108, 371285209786083249, 371285209732555713, 371285209652373379, 371285209641675390, 371285209644583471, 371285209787422544, 371285209946118581]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 76570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 76500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477399149446504, 362477486816818082⟩, ⟨586976280759068907, 591510517131114293⟩, true⟩

def words08 : List Nat := [371285210088673403, 371285210091833894, 371285210178952370, 371285210267451141, 371285210364580327, 371285210367219849, 371285210252499376, 371285210104261750, 371285209954981914, 371285209894467007]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 76580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 76500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362475778260252903, 362475865951400932⟩, ⟨711183946570676720, 715720004104294284⟩, true⟩

def words09 : List Nat := [371285209851324588, 371285209910125127, 371285209934501655, 371285209937187275, 371285209819670105, 371285209755514198, 371285209793005708, 371285209795645496, 371285209673574989, 371285209554587673]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 76590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 76500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 76500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk765
