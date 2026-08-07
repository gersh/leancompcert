import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk028

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362587022873426223, 362587022960435944⟩, ⟨(-324877744149750328), (-324877578811213446)⟩, true⟩

def state01 : KState := ⟨⟨362862990140410285, 362862990228072089⟩, ⟨(-1097412281701128863), (-1097412114533403243)⟩, true⟩

def words00 : List Nat := [371271205877238022, 371271313000182700, 371271547806174210, 371271782444774823, 371271965027059138, 371272022991572970, 371272129512408742, 371272235957440215, 371272452108945496, 371272591041116058]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 2800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 2800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362935449055582166, 362935449143910228⟩, ⟨(-1301110270389880230), (-1301110101346581448)⟩, true⟩

def words01 : List Nat := [371272727352676853, 371272863567346276, 371273076808535993, 371273247453724232, 371273452132833496, 371273656666654946, 371273861273229537, 371273898912714731, 371274062583059434, 371274226137406655]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 2810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 2800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362517371229940039, 362517371318924356⟩, ⟨(-119618520664512106), (-119618349767122324)⟩, true⟩

def words02 : List Nat := [371274418365755311, 371274492176178926, 371274563657924628, 371274635089089070, 371274745577844554, 371274795192927360, 371274903774232166, 371275012278803974, 371275103350732471, 371275118281210785]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 2820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 2800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨363137861423576196, 363137861513228583⟩, ⟨(-1878552418140818868), (-1878552245349422584)⟩, true⟩

def words03 : List Nat := [371275214227897713, 371275310106888124, 371275530826789692, 371275640967414346, 371275720247857440, 371275799472431017, 371276003339208989, 371276166463658263, 371276399454923411, 371276632282200980]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 2830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 2800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362828038944657445, 362828039034979573⟩, ⟨(-996403575408510800), (-996403400711617502)⟩, true⟩

def words04 : List Nat := [371276862976866402, 371277009675303212, 371277280344051878, 371277550822561615, 371277854239770315, 371277993865191196, 371278136083286038, 371278278201569267, 371278423806575038, 371278546435641931]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 2840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 2800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362691731425803386, 362691731516794525⟩, ⟨(-605585769930267780), (-605585593323266682)⟩, true⟩

def words05 : List Nat := [371278792440711907, 371279038273357710, 371279284259354505, 371279367268052706, 371279483293439029, 371279599237642075, 371279838002123259, 371279914240221651, 371279988302262161, 371280062312557103]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 2850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 2800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362853364265409488, 362853364357068683⟩, ⟨(-1067756344754793421), (-1067756166233690861)⟩, true⟩

def words06 : List Nat := [371280258793727106, 371280399144529341, 371280586396958855, 371280773518701347, 371280944416241863, 371280953739950812, 371281050345408996, 371281146883560280, 371281323880950361, 371281453466705155]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 2860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 2800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362607006094407632, 362607006186750227⟩, ⟨(-359573754431160187), (-359573573945247419)⟩, true⟩

def words07 : List Nat := [371281552400294576, 371281651265037660, 371281801594121203, 371281892702581211, 371281999311850360, 371282105847035894, 371282188415194381, 371282188415269509, 371282154251258301, 371282197587671697]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 2870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 2800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362703130289361351, 362703130382374005⟩, ⟨(-636476327439552405), (-636476145020372579)⟩, true⟩

def words08 : List Nat := [371282325568361896, 371282352072046404, 371282380448318426, 371282408804944787, 371282469996970278, 371282487139849436, 371282624392088572, 371282761549341792, 371282896422081173, 371282972601322337]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 2880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 2800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362912319658882686, 362912319752577068⟩, ⟨(-1242956566656650905), (-1242956382263780735)⟩, true⟩

def words09 : List Nat := [371283085954767929, 371283199229886519, 371283368867349528, 371283380149168382, 371283380149226693, 371283376297056323, 371283487897748958, 371283566257352100, 371283714103436510, 371283861847625748]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 2890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 2800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 2800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk028
