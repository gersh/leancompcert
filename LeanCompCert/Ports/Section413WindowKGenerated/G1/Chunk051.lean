import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk051

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362505987264543182, 362505987571621927⟩, ⟨(-126754274409696136), (-126753212945985158)⟩, true⟩

def state01 : KState := ⟨⟨362497893062911058, 362497893371239923⟩, ⟨(-85425792751797240), (-85424724905969216)⟩, true⟩

def words00 : List Nat := [371281181996229071, 371281181996369147, 371281174170172869, 371281158828258220, 371281143492298161, 371281139581977481, 371281139324125539, 371281158265987368, 371281176203791738, 371281179474760571]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 5100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 5100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362642947853153353, 362642948162752990⟩, ⟨(-827227364076683013), (-827226289730746383)⟩, true⟩

def words01 : List Nat := [371281209489487927, 371281239492549017, 371281307546993403, 371281324871677269, 371281333810904456, 371281342746679197, 371281355395663991, 371281355395818705, 371281380527880336, 371281412078056496]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 5110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 5100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362563566721420661, 362563567032292510⟩, ⟨(-420799988013006039), (-420798907146893417)⟩, true⟩

def words02 : List Nat := [371281442548251277, 371281442548392715, 371281463600589151, 371281489319723810, 371281521173322712, 371281521173464615, 371281519618235028, 371281518257998577, 371281539954713741, 371281555941443379]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 5120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 5100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362393805954164492, 362393806266307266⟩, ⟨451287201016252323, 451288288408866721⟩, true⟩

def words03 : List Nat := [371281587338275909, 371281618722929095, 371281644589386019, 371281644589527560, 371281633207812364, 371281628591977950, 371281638737934193, 371281638738077863, 371281622628946244, 371281605544207824]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 5130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 5100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362543642839491324, 362543643152899916⟩, ⟨(-319207658646089592), (-319206564740716810)⟩, true⟩

def words04 : List Nat := [371281598979568566, 371281598979724057, 371281610108258949, 371281629595501421, 371281639727359371, 371281639727501026, 371281618421161045, 371281626557095217, 371281661295522122, 371281673328644293]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 5140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 5100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362418332168623658, 362418332483324961⟩, ⟨327655676797524694, 327656777366943624⟩, true⟩

def words05 : List Nat := [371281678805050909, 371281684279383777, 371281727247976686, 371281751439961162, 371281786921985621, 371281822390301867, 371281858193198063, 371281858193339862, 371281844167073501, 371281831858783672]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 5150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 5100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469897536751439, 362469897852718317⟩, ⟨61198649270300509, 61199756376560347⟩, true⟩

def words06 : List Nat := [371281830911065603, 371281830911207643, 371281804193568632, 371281777570286728, 371281750957261402, 371281735693942218, 371281716819252373, 371281726022836372, 371281735329625806, 371281735329773745]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 5160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 5100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362761378817345051, 362761379134596632⟩, ⟨(-1447247937076849981), (-1447246823322008797)⟩, true⟩

def words07 : List Nat := [371281767969015221, 371281802884028351, 371281852894599230, 371281868383977865, 371281874964945211, 371281881543414122, 371281917060944137, 371281933908750289, 371281987855802044, 371282041782092867]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 5170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 5100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362487458112026402, 362487458430564699⟩, ⟨(-27825596036395804), (-27824475609842532)⟩, true⟩

def words08 : List Nat := [371282087459807318, 371282087459949912, 371282110024928327, 371282136268924087, 371282163845272785, 371282163845415484, 371282142140066325, 371282114850571081, 371282097259764531, 371282098292708825]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 5180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 5100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362531008674166860, 362531008993994007⟩, ⟨(-253486457234379365), (-253485330112119311)⟩, true⟩

def words09 : List Nat := [371282125461961177, 371282152620809450, 371282178930381434, 371282178930526871, 371282186991906790, 371282196669137900, 371282243168522160, 371282252438595387, 371282261814963196, 371282271187781333]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 5190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 5100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 5100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk051
