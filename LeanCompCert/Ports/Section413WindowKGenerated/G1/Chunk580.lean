import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk580

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476486542085729, 362476535732771168⟩, ⟨488048591164977377, 489975846455953805⟩, true⟩

def state01 : KState := ⟨⟨362483055436712640, 362483104644943301⟩, ⟨107095498006722271, 109023771011610593⟩, true⟩

def words00 : List Nat := [371284983549806161, 371284983552000901, 371284983690015028, 371284983836228220, 371284983932323823, 371284983934294296, 371284983844786518, 371284983881414224, 371284984039072349, 371284984041099337]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 58000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 58000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362484880790776454, 362484930016829111⟩, ⟨1245832232947991, 3175139182591835⟩, true⟩

def words01 : List Nat := [371284984010166611, 371284983965305921, 371284984170133335, 371284984323593468, 371284984528574217, 371284984734363140, 371284984934478135, 371284984936436704, 371284984740277816, 371284984741737464]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 58010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 58000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362472731233052532, 362472780476562343⟩, ⟨706217703647935129, 708148023552986651⟩, true⟩

def words02 : List Nat := [371284984926305680, 371284984928264736, 371284984762221241, 371284984537435000, 371284984311900888, 371284984094340369, 371284983762182857, 371284983728103098, 371284983693384795, 371284983613277025]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 58020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 58000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362496081070617031, 362496130331854007⟩, ⟨(-648867975357835619), (-646936626658582723)⟩, true⟩

def words03 : List Nat := [371284983491292411, 371284983580667076, 371284983941034642, 371284983942993828, 371284983907622965, 371284983837196897, 371284983815482631, 371284983817647353, 371284983937033106, 371284984131294772]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 58030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 58000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362479623070401695, 362479672349336090⟩, ⟨306382132828528365, 308314508775759089⟩, true⟩

def words04 : List Nat := [371284984325890608, 371284984327850146, 371284984220917834, 371284984317692875, 371284984450483888, 371284984452443650, 371284984189583907, 371284983873647653, 371284983556897945, 371284983538117757]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 58040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 58000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362476470568915557, 362476519865495539⟩, ⟨489381669057053255, 491315069420499645⟩, true⟩

def words05 : List Nat := [371284983478532549, 371284983511196693, 371284983516276936, 371284983518236899, 371284983127594920, 371284982769869777, 371284982411123598, 371284982350034107, 371284982204541687, 371284982060972985]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 58050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 58000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488245852877545, 362488295166984802⟩, ⟨(-194271143313199353), (-192336725225011323)⟩, true⟩

def words06 : List Nat := [371284982067744173, 371284982073721844, 371284982326237391, 371284982579570245, 371284982773924483, 371284982775884969, 371284982668724998, 371284982765258904, 371284983011946664, 371284983071012200]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 58060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 58000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362483904119983964, 362483953452002600⟩, ⟨57932940831967711, 59868399120346211⟩, true⟩

def words07 : List Nat := [371284983125954690, 371284983181610537, 371284983533225724, 371284983738374417, 371284983959389735, 371284984181126160, 371284984395582870, 371284984397543928, 371284984259272947, 371284984243998474]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 58070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 58000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478179392283164, 362478228741756966⟩, ⟨390495983313141675, 392432455487948915⟩, true⟩

def words08 : List Nat := [371284984491831513, 371284984493792510, 371284984403574700, 371284984304970860, 371284984205627978, 371284984196431741, 371284984183676628, 371284984288152944, 371284984333726473, 371284984335757448]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 58080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 58000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488045040022643, 362488094407223043⟩, ⟨(-182686385071917999), (-180748883069585007)⟩, true⟩

def words09 : List Nat := [371284984255660978, 371284984292842544, 371284984421719902, 371284984423682796, 371284984219687467, 371284983966922011, 371284983713349546, 371284983596882838, 371284983408731680, 371284983464501411]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 58090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 58000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 58000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk580
