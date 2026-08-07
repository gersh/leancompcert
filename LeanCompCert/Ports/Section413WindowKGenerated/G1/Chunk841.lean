import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk841

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362465966205940329, 362466072672205108⟩, ⟨1612640465867729501, 1618686283954565683⟩, true⟩

def state01 : KState := ⟨⟨362481767084181276, 362481873576536340⟩, ⟨283719555250314990, 289767567663847284⟩, true⟩

def words00 : List Nat := [371285319606849201, 371285319490704816, 371285319309245841, 371285319247773744, 371285319185431647, 371285319085887686, 371285318858581808, 371285318756844873, 371285318675957140, 371285318678993407]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 84100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 84100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362473872322653576, 362473978841661346⟩, ⟨947823728850837779, 953873983159224231⟩, true⟩

def words01 : List Nat := [371285318640220007, 371285318590649997, 371285318584637357, 371285318587884352, 371285318581755956, 371285318602426524, 371285318604623320, 371285318597936410, 371285318416271875, 371285318285113073]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 84110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 84100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473984326689491, 362474090871695755⟩, ⟨938413876693647609, 944466318130691827⟩, true⟩

def words02 : List Nat := [371285318158743100, 371285318161662356, 371285317982005842, 371285317801534943, 371285317619978803, 371285317484292935, 371285317295847485, 371285317249883176, 371285317202872710, 371285317144346780]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 84120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 84100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362487796116612426, 362487902688027716⟩, ⟨(-223635109470784563), (-217580446113525433)⟩, true⟩

def words03 : List Nat := [371285317020669504, 371285317031957287, 371285317055774121, 371285317058700944, 371285316962522489, 371285316848448293, 371285316757062711, 371285316760282288, 371285316751200853, 371285316785244133]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 84130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 84100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475801897487389, 362475908495264644⟩, ⟨785588430867062448, 791645312452198854⟩, true⟩

def words04 : List Nat := [371285316818107468, 371285316821027640, 371285316665432875, 371285316652566966, 371285316665034121, 371285316667954360, 371285316508774721, 371285316323194330, 371285316136465302, 371285316045026406]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 84140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 84100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362471679657262311, 362471786281327461⟩, ⟨1132530793002302518, 1138589886850328808⟩, true⟩

def words05 : List Nat := [371285315935218462, 371285315903297994, 371285315870365184, 371285315838189812, 371285315687925723, 371285315582301930, 371285315475200702, 371285315470236160, 371285315310986077, 371285315153557147]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 84150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 84100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362476484284919155, 362476590935170558⟩, ⟨728150962986112867, 734212260799301755⟩, true⟩

def words06 : List Nat := [371285314994836388, 371285314854814807, 371285314663929585, 371285314615314949, 371285314565819379, 371285314505285400, 371285314255692457, 371285314096556007, 371285313935787817, 371285313903696153]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 84160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 84100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474738298646539, 362474844975456438⟩, ⟨875129188665594449, 881192722042447023⟩, true⟩

def words07 : List Nat := [371285313802245710, 371285313701770381, 371285313603023049, 371285313606242208, 371285313540740752, 371285313466995826, 371285313392248830, 371285313317839039, 371285313054426833, 371285312933665543]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 84170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 84100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362470568705504480, 362470675408370995⟩, ⟨1226193275382720155, 1232259002341259355⟩, true⟩

def words08 : List Nat := [371285312827978602, 371285312830951905, 371285312733092471, 371285312609238454, 371285312484233276, 371285312396178449, 371285312236933524, 371285312185219463, 371285312132574138, 371285312051705611]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 84180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 84100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362498252086500000, 362498358815794479⟩, ⟨(-1104604868668206467), (-1098536916606857117)⟩, true⟩

def words09 : List Nat := [371285311879836572, 371285311850531538, 371285311900306935, 371285311903250104, 371285311882491642, 371285311840434355, 371285311881617476, 371285311898818193, 371285312055751262, 371285312214012947]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 84190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 84100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 84100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk841
