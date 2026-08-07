import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk894

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492643084807793, 362492763961523869⟩, ⟨(-688776715615319265), (-681480370559454313)⟩, true⟩

def state01 : KState := ⟨⟨362480415071961934, 362480535976459005⟩, ⟨404463299222673152, 411762128042852592⟩, true⟩

def words00 : List Nat := [371285141366479960, 371285141369597530, 371285141345730528, 371285141308498820, 371285141270040135, 371285141271017169, 371285141236109011, 371285141267910005, 371285141298452558, 371285141301680377]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 89400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 89400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362497983561311399, 362498104493982621⟩, ⟨(-1166429773277935410), (-1159128425260635116)⟩, true⟩

def words01 : List Nat := [371285141252324727, 371285141243655628, 371285141345988808, 371285141373497737, 371285141378940762, 371285141385360040, 371285141515423788, 371285141601005262, 371285141748100523, 371285141896547336]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 89410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 89400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362486249530190835, 362486370490993021⟩, ⟨(-117160026219203494), (-109856162592791566)⟩, true⟩

def words02 : List Nat := [371285142032716614, 371285142035835023, 371285142081917311, 371285142162497413, 371285142246897791, 371285142250016868, 371285142185492882, 371285142120221690, 371285142083490362, 371285142100808491]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 89420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 89400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362477023451731698, 362477144440672674⟩, ⟨708037757939722647, 715344138158284551⟩, true⟩

def words03 : List Nat := [371285142241562758, 371285142383671250, 371285142519946699, 371285142523065907, 371285142515803142, 371285142529367704, 371285142620412633, 371285142623531937, 371285142560273653, 371285142474417736]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 89430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 89400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362487113137514874, 362487234154345746⟩, ⟨(-194430137037864893), (-187121262200696695)⟩, true⟩

def words04 : List Nat := [371285142387125516, 371285142348734011, 371285142266391583, 371285142289961794, 371285142292376056, 371285142287499850, 371285142177645056, 371285142159306814, 371285142242088246, 371285142268707792]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 89440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 89400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362484622910864173, 362484743956167305⟩, ⟨28330616133123182, 35642037953419946⟩, true⟩

def words05 : List Nat := [371285142292862697, 371285142318049105, 371285142371335963, 371285142374783559, 371285142413555573, 371285142454325069, 371285142493864085, 371285142496984026, 371285142369809288, 371285142369289968]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 89450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 89400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477036294803719, 362477157367859342⟩, ⟨707085261648522838, 714399166351094770⟩, true⟩

def words06 : List Nat := [371285142476521605, 371285142479642975, 371285142446402304, 371285142390756275, 371285142333889027, 371285142301169271, 371285142225726351, 371285142203297048, 371285142179864196, 371285142157915798]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 89460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 89400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497633908938538, 362497755010244584⟩, ⟨(-1135890843907379601), (-1128574411498167417)⟩, true⟩

def words07 : List Nat := [371285142070797751, 371285142037430101, 371285142081144434, 371285142098247013, 371285142100664553, 371285142098367905, 371285142213960475, 371285142275211141, 371285142418293233, 371285142562780898]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 89470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 89400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483595461243643, 362483716590727838⟩, ⟨120287746828248752, 127606700760881558⟩, true⟩

def words08 : List Nat := [371285142682402741, 371285142685523556, 371285142692026172, 371285142749275625, 371285142811722910, 371285142814844097, 371285142722453096, 371285142618534862, 371285142519674010, 371285142523242766]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 89480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 89400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362478455374484258, 362478576532031252⟩, ⟨580349030681485807, 587670496095195591⟩, true⟩

def words09 : List Nat := [371285142618239212, 371285142730425893, 371285142831569513, 371285142834693773, 371285142800207172, 371285142773601375, 371285142820462319, 371285142823584325, 371285142752708990, 371285142682825612]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 89490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 89400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 89400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk894
