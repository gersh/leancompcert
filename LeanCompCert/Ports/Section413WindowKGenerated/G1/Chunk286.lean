import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk286

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362482902302625501, 362482913591208618⟩, ⟨60915866348313030, 61134108607725984⟩, true⟩

def state01 : KState := ⟨⟨362501228589891004, 362501239886651044⟩, ⟨(-463114383989149162), (-462895907827633996)⟩, true⟩

def words00 : List Nat := [371285051939040586, 371285052365302418, 371285054011935190, 371285055658814558, 371285057110578752, 371285057111491851, 371285057981431039, 371285059027404994, 371285060371276602, 371285060937721345]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 28600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 28600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362493418243983901, 362493429549064470⟩, ⟨(-239660753490381373), (-239442039237122971)⟩, true⟩

def words01 : List Nat := [371285061141699863, 371285061345951460, 371285062159955354, 371285062513510007, 371285062985752773, 371285063458336485, 371285063932879831, 371285063933793786, 371285063299182708, 371285063592625593]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 28610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 28600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362504131224794031, 362504142538027925⟩, ⟨(-546275228149115994), (-546056280504983312)⟩, true⟩

def words02 : List Nat := [371285065105283214, 371285065532203859, 371285065639742794, 371285065747580531, 371285066166599127, 371285066167610346, 371285067311763409, 371285068494073511, 371285069666632546, 371285070333756158]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 28620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 28600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362522213545753543, 362522224867255410⟩, ⟨(-1064018097111787823), (-1063798912713844271)⟩, true⟩

def words03 : List Nat := [371285072219474887, 371285074105541484, 371285076361229906, 371285077154481833, 371285077682447174, 371285078210649866, 371285079247776613, 371285079751840973, 371285081049431462, 371285082347346404]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 28630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 28600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362492738546283302, 362492749876031715⟩, ⟨(-219826884658170554), (-219607464037202664)⟩, true⟩

def words04 : List Nat := [371285083647363636, 371285083648278075, 371285084219829435, 371285085115279150, 371285086083786150, 371285086084700873, 371285085430824822, 371285084779484085, 371285084692997188, 371285084961577169]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 28640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 28600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362471485115179687, 362471496453172219⟩, ⟨389213571784930410, 389433228641915784⟩, true⟩

def words05 : List Nat := [371285085739153623, 371285086517035082, 371285087297319272, 371285087298234176, 371285086457005682, 371285085667966546, 371285085305155236, 371285085306087439, 371285084966360128, 371285084493250444]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 28650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 28600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362540038671817051, 362540050017993630⟩, ⟨(-1575791609235640901), (-1575571717781543955)⟩, true⟩

def words06 : List Nat := [371285084762187482, 371285085027841071, 371285086509434917, 371285087991304376, 371285089285690273, 371285089498842493, 371285090794901201, 371285092091331977, 371285094603101472, 371285096520808965]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 28660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 28600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362522302643338219, 362522313997882184⟩, ⟨(-1067082129903369117), (-1066861998515076973)⟩, true⟩

def words07 : List Nat := [371285098401703211, 371285100282802997, 371285103178760791, 371285105495784795, 371285107993573268, 371285110491527370, 371285112764283632, 371285113884578450, 371285115182288067, 371285116480413649]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 28670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 28600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362505632564117605, 362505643926819221⟩, ⟨(-588962699912598406), (-588742334520496072)⟩, true⟩

def words08 : List Nat := [371285118245231668, 371285118391624507, 371285118528834451, 371285118666328501, 371285119170282917, 371285119242786137, 371285120529298022, 371285121816110110, 371285123105565057, 371285123821750716]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 28680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 28600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362525995528501932, 362526006899486651⟩, ⟨(-1173292413302926300), (-1173071810226240622)⟩, true⟩

def words09 : List Nat := [371285125328796769, 371285126836207840, 371285128851491846, 371285129249728661, 371285129455098771, 371285129660749683, 371285131079521916, 371285131891366463, 371285133316209556, 371285134741365811]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 28690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 28600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 28600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk286
