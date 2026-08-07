import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk084

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362535697171763664, 362535698045413290⟩, ⟨(-441646660575202408), (-441641691146363300)⟩, true⟩

def state01 : KState := ⟨⟨362427805027368765, 362427805903172999⟩, ⟨465351889139215272, 465356876678211248⟩, true⟩

def words00 : List Nat := [371283145638526565, 371283145638768759, 371283144569625778, 371283143639214029, 371283144063441468, 371283144063710437, 371283138855550161, 371283139178883618, 371283139657580688, 371283139657831526]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 8400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 8400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362614811221145292, 362614812099138003⟩, ⟨(-1108403770591940417), (-1108398764636581513)⟩, true⟩

def words01 : List Nat := [371283135839891021, 371283138600151766, 371283152752306162, 371283155293498088, 371283155293689298, 371283152067476177, 371283156016580263, 371283157654631860, 371283173290716749, 371283188923192560]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 8410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 8400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362564563158500969, 362564564038687076⟩, ⟨(-685625507373625291), (-685620482938790027)⟩, true⟩

def words02 : List Nat := [371283201504924058, 371283201505166838, 371283203263635666, 371283211136210364, 371283222797099721, 371283222797344121, 371283222034042797, 371283221037999992, 371283233020268411, 371283242667208155]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 8420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 8400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362371606373163807, 362371607255539040⟩, ⟨942778729077200004, 942783771977594248⟩, true⟩

def words03 : List Nat := [371283266281082150, 371283289889457581, 371283313211887484, 371283317880923871, 371283322932589223, 371283327983171240, 371283335674386414, 371283335674629684, 371283324730317948, 371283311493925011]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 8430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 8400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362456252444007607, 362456253328566505⟩, ⟨228491705562434782, 228496766903761916⟩, true⟩

def words04 : List Nat := [371283298260559437, 371283294696760195, 371283292071031347, 371283297724465040, 371283300757236857, 371283300757480438, 371283289731276185, 371283291183166234, 371283294365816601, 371283294366069909]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 8440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 8400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362420944615378449, 362420945502153782⟩, ⟨527389085282160067, 527394165363769255⟩, true⟩

def words05 : List Nat := [371283291166510022, 371283287992006130, 371283293403662853, 371283294983653152, 371283298971172134, 371283302957846755, 371283307058313149, 371283307058556905, 371283292607345764, 371283285238012384]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 8450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 8400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362446514706490969, 362446515595443209⟩, ⟨310890768676752211, 310895867186205647⟩, true⟩

def words06 : List Nat := [371283284384682726, 371283284384926545, 371283272364623263, 371283259085850771, 371283245810119820, 371283236837822013, 371283222579339418, 371283222180076191, 371283221780829337, 371283221128759172]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 8460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 8400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362579771433455333, 362579772324615635⟩, ⟨(-818324419194933008), (-818319301972071844)⟩, true⟩

def words07 : List Nat := [371283223895666265, 371283230994106024, 371283248124797403, 371283251207130728, 371283252669397436, 371283254131393353, 371283260957495655, 371283261025437372, 371283272406653105, 371283283785295736]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 8470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 8400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362386461940547817, 362386462833912163⟩, ⟨821501587439132620, 821506723363736798⟩, true⟩

def words08 : List Nat := [371283292213640135, 371283292213884537, 371283282199971557, 371283280912845137, 371283282652868684, 371283282653113260, 371283267260550785, 371283249942805337, 371283232629040180, 371283224520998587]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 8480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 8400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362326913260909813, 362326914156480514⟩, ⟨1327522523474731855, 1327527678142489665⟩, true⟩

def words09 : List Nat := [371283213125373961, 371283207433423166, 371283201742731832, 371283194899214400, 371283173026913599, 371283155490994009, 371283137959070824, 371283130785457434, 371283112259294936, 371283093883320807]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 8490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 8400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 8400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk084
