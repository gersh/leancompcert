import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk078

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362546890186135577, 362546890934046716⟩, ⟨(-485751025485334524), (-485747075069171036)⟩, true⟩

def state01 : KState := ⟨⟨362465161523025889, 362465162272924622⟩, ⟨152183678521340853, 152187644451117019⟩, true⟩

def words00 : List Nat := [371284643277972543, 371284645333537614, 371284645385164884, 371284645436849384, 371284645437009315, 371284645408260982, 371284641256984906, 371284645246976515, 371284648526783024, 371284648527015675]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 7800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 7800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362581366706445235, 362581367458364637⟩, ⟨(-755819281967066231), (-755815300245663009)⟩, true⟩

def words01 : List Nat := [371284657256971004, 371284668478891374, 371284690099984330, 371284690100207935, 371284689966157780, 371284687220316060, 371284698039816176, 371284703523921700, 371284715885193607, 371284728243399075]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 7810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 7800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362588740271210037, 362588741025152183⟩, ⟨(-814189570695880801), (-814185573146376351)⟩, true⟩

def words02 : List Nat := [371284737577296679, 371284737577520560, 371284729113230177, 371284733023978396, 371284741729784441, 371284741857789823, 371284741883497044, 371284741909271028, 371284758193074997, 371284771471692041]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 7820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 7800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362425386164528300, 362425386920494005⟩, ⟨466226676468049914, 466230689872311396⟩, true⟩

def words03 : List Nat := [371284796678067601, 371284821878100790, 371284843676213104, 371284843825400002, 371284848872964934, 371284853919348758, 371284869123038144, 371284869123262488, 371284862706671322, 371284855120732821]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 7830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 7800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362377981623902396, 362377982381875685⟩, ⟨838616978278635818, 838621007432739016⟩, true⟩

def words04 : List Nat := [371284856152636249, 371284856724962398, 371284861594736487, 371284866463356243, 371284868795228076, 371284868795452673, 371284849547511998, 371284833148921914, 371284816754391310, 371284813083459474]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 7840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 7800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362423731643890847, 362423732403911010⟩, ⟨479635854962238713, 479639900194781297⟩, true⟩

def words05 : List Nat := [371284799476354676, 371284785769078818, 371284774519346802, 371284774519600642, 371284776737209947, 371284780289579029, 371284782428828239, 371284782429053332, 371284763056415445, 371284755291976504]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 7850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 7800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362301207224727478, 362301207986756452⟩, ⟨1443226305760763427, 1443230366793041837⟩, true⟩

def words06 : List Nat := [371284747529393847, 371284746575323149, 371284724137032492, 371284701616498632, 371284679101606162, 371284656458500362, 371284628539083047, 371284616710227419, 371284604884301098, 371284591769068148]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 7860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 7800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362544911374793019, 362544912138862203⟩, ⟨(-476122279137003495), (-476118202037992669)⟩, true⟩

def words07 : List Nat := [371284568470558307, 371284555293788906, 371284545014237008, 371284545014462705, 371284530673773480, 371284512346478704, 371284494023747054, 371284491760504800, 371284491046978190, 371284498713911310]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 7870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 7800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362388653960731753, 362388654726841538⟩, ⟨756095645979990661, 756099739169337139⟩, true⟩

def words08 : List Nat := [371284504582985094, 371284504583214751, 371284505812271773, 371284514446702085, 371284526726059791, 371284526726285759, 371284517633637167, 371284505280768824, 371284492930940522, 371284484858548679]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 7880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 7800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362326095384663298, 362326096152806995⟩, ⟨1250291314393388271, 1250295423640778013⟩, true⟩

def words09 : List Nat := [371284472714471772, 371284470867894500, 371284469021713226, 371284467143998593, 371284443941726965, 371284425579559332, 371284407221919974, 371284401353417983, 371284381432165371, 371284361396305828]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 7890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 7800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 7800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk078
