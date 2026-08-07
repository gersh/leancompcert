import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk156

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362478930188016432, 362478933375329472⟩, ⟨78228185534553655, 78261820229192107⟩, true⟩

def state01 : KState := ⟨⟨362478682981045302, 362478686172585910⟩, ⟨82208604334409690, 82242305001241678⟩, true⟩

def words00 : List Nat := [371283953622824231, 371283953623298868, 371283953093600762, 371283951795685757, 371283950497760576, 371283950426866188, 371283951000250460, 371283953339379591, 371283954737429455, 371283954737928719]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 15600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 15600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362539026427711687, 362539029623534093⟩, ⟨(-860040175713705243), (-860006408186141263)⟩, true⟩

def words01 : List Nat := [371283957377194596, 371283960353808706, 371283966015597461, 371283967074120197, 371283967367608550, 371283967661209800, 371283968641425921, 371283968641949603, 371283971594309206, 371283975119457137]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 15610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 15600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362505867491616682, 362505870691722244⟩, ⟨(-342210272106592761), (-342176437654483579)⟩, true⟩

def words02 : List Nat := [371283978211902823, 371283978212377972, 371283977647284344, 371283978629079772, 371283980861972920, 371283980862450276, 371283979233837888, 371283977592994025, 371283978404702812, 371283979805812547]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 15620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 15600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362421538197405183, 362421541401799274⟩, ⟨976258222803278002, 976292124307044384⟩, true⟩

def words03 : List Nat := [371283981092392158, 371283982378997362, 371283983728754798, 371283983729230204, 371283979631132362, 371283976135401381, 371283972639878798, 371283972079986667, 371283968162836790, 371283964171895633]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 15630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 15600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362513238614921545, 362513241823570009⟩, ⟨(-458172215708972820), (-458138247645059126)⟩, true⟩

def words04 : List Nat := [371283960278524029, 371283960279055847, 371283961925068970, 371283964791743523, 371283966480090312, 371283966480566120, 371283963061887945, 371283963395666343, 371283967813642921, 371283969684560038]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 15640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 15600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362449474773429884, 362449477986418010⟩, ⟨540217425045390173, 540251461046725729⟩, true⟩

def words05 : List Nat := [371283971030854483, 371283972377140312, 371283975727358219, 371283977053389372, 371283979157813886, 371283981262155880, 371283982849798926, 371283982850275069, 371283979005117793, 371283976802576805]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 15650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 15600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362445671911028849, 362445675128258300⟩, ⟨599909752752826267, 599943855195527509⟩, true⟩

def words06 : List Nat := [371283976476005025, 371283976476481448, 371283973772397980, 371283970567898308, 371283967363618508, 371283964884556647, 371283961031873181, 371283961144521022, 371283961270406926, 371283961270900006]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 15660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 15600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362550371887282836, 362550375108832543⟩, ⟨(-1041313690319279134), (-1041279520156678160)⟩, true⟩

def words07 : List Nat := [371283960460822775, 371283962093906949, 371283965368335151, 371283965368813058, 371283964554475802, 371283962792038492, 371283962575029534, 371283962739812033, 371283966975618680, 371283971211111947]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 15670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 15600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362527857632533204, 362527860858377047⟩, ⟨(-688347255809281175), (-688313018292229921)⟩, true⟩

def words08 : List Nat := [371283975428112317, 371283975428589104, 371283977096938273, 371283979965706262, 371283984042857039, 371283985639752157, 371283986558684977, 371283987477655619, 371283991321932359, 371283994118316361]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 15680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 15600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487801352846140, 362487804582984192⟩, ⟨(-59461238950355103), (-59426934035099237)⟩, true⟩

def words09 : List Nat := [371283998404006839, 371284002689337531, 371284006959100957, 371284008754760287, 371284011480201145, 371284014205540364, 371284018931034731, 371284019185952990, 371284019427418311, 371284019669027432]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 15690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 15600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 15600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk156
