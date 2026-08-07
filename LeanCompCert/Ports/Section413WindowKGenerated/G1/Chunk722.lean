import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk722

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362486013810294211, 362486091359600866⟩, ⟨(-63660588970437713), (-59879320521744221)⟩, true⟩

def state01 : KState := ⟨⟨362477447344020233, 362477524915658074⟩, ⟨554836344356445280, 558619225231689536⟩, true⟩

def words00 : List Nat := [371285262019470694, 371285262010977309, 371285261818317912, 371285261797344604, 371285261775184401, 371285261761455805, 371285261516483014, 371285261271091010, 371285261024665126, 371285260952567529]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 72200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 72200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362463540482314357, 362463618076276525⟩, ⟨1559195466622066653, 1562979959649006747⟩, true⟩

def words01 : List Nat := [371285260931557545, 371285261018708577, 371285261105500203, 371285261107978516, 371285260939213804, 371285260755853373, 371285260571154805, 371285260563619413, 371285260300067497, 371285260003161724]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 72210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 72200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362495024801547517, 362495102417694999⟩, ⟨(-714737160712435519), (-710951065351106107)⟩, true⟩

def words02 : List Nat := [371285259705180471, 371285259599754566, 371285259397235831, 371285259387262608, 371285259376503241, 371285259335416771, 371285259243406685, 371285259295253990, 371285259537301239, 371285259676138727]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 72220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 72200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362485505407431909, 362485583046221440⟩, ⟨(-27090116608872088), (-23302385700932406)⟩, true⟩

def words03 : List Nat := [371285259814777645, 371285259954271957, 371285260122750040, 371285260196954353, 371285260328217328, 371285260460403821, 371285260563127143, 371285260565611641, 371285260474045065, 371285260481670826]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 72230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 72200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362473555052854140, 362473632713700917⟩, ⟨836276298702987372, 840065623143423556⟩, true⟩

def words04 : List Nat := [371285260614327111, 371285260616807467, 371285260526427117, 371285260418956133, 371285260310561016, 371285260261242150, 371285260114909330, 371285260049952164, 371285259984119170, 371285259919557574]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 72240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 72200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362501428974688358, 362501506657923449⟩, ⟨(-1177708764914619589), (-1173917822804164139)⟩, true⟩

def words05 : List Nat := [371285259790739350, 371285259824136977, 371285260047591150, 371285260161667871, 371285260244170281, 371285260327478143, 371285260551020754, 371285260679640126, 371285260906160286, 371285261133742990]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 72250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 72200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491012460538237, 362491090166200041⟩, ⟨(-425035337456907406), (-421242774680063988)⟩, true⟩

def words06 : List Nat := [371285261319078746, 371285261321558612, 371285261347360765, 371285261446163295, 371285261572936053, 371285261575419644, 371285261496281007, 371285261410682204, 371285261426993418, 371285261510519616]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 72260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 72200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362483108847133857, 362483186575118126⟩, ⟨146256129905973568, 150050306042359764⟩, true⟩

def words07 : List Nat := [371285261784100931, 371285262058716508, 371285262332996979, 371285262352859278, 371285262365547773, 371285262379408368, 371285262583219788, 371285262585700556, 371285262559871989, 371285262533973167]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 72270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 72200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484395728949074, 362484473479169305⟩, ⟨53280967224228837, 57076750689534995⟩, true⟩

def words08 : List Nat := [371285262577161012, 371285262581858288, 371285262703857463, 371285262826846170, 371285262917806919, 371285262920288521, 371285262852598916, 371285262916528554, 371285263029107683, 371285263031675731]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 72280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 72200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483769642769661, 362483847415557173⟩, ⟨98547569915348625, 102344984883827487⟩, true⟩

def words09 : List Nat := [371285263022608486, 371285263014945433, 371285263093277419, 371285263096011487, 371285263124442307, 371285263162787284, 371285263186682610, 371285263189165182, 371285262992044279, 371285262975514073]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 72290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 72200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 72200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk722
