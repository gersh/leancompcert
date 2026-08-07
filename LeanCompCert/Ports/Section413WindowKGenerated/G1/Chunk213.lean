import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk213

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362491408526531732, 362491414633954318⟩, ⟨(-150248970021857229), (-150160995168932199)⟩, true⟩

def state01 : KState := ⟨⟨362411537701829704, 362411543815170428⟩, ⟨1551385674659209056, 1551473775599815564⟩, true⟩

def words00 : List Nat := [371284365815811993, 371284365816476169, 371284363549138570, 371284361252271742, 371284358955361551, 371284357343414464, 371284354817203771, 371284352801533351, 371284350785822491, 371284348778830673]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 21300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 21300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362504500701854793, 362504506821211514⟩, ⟨(-430182839853353802), (-430094610683007110)⟩, true⟩

def words01 : List Nat := [371284345362972960, 371284343769569277, 371284342774333243, 371284342774997820, 371284340447048176, 371284337509268828, 371284334571501903, 371284333825839262, 371284333527271948, 371284334474197631]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 21310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 21300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362453347563291778, 362453353688655270⟩, ⟨660713827068721222, 660802184334134490⟩, true⟩

def words02 : List Nat := [371284335215000829, 371284335215677187, 371284335241967946, 371284336351083728, 371284338093636301, 371284338094301334, 371284336912805057, 371284335740261459, 371284334567560024, 371284333631662028]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 21320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 21300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362415424769463038, 362415430900807743⟩, ⟨1469984262223861571, 1470072747099339943⟩, true⟩

def words03 : List Nat := [371284332655601488, 371284333132103376, 371284333525898658, 371284333526563882, 371284330998601480, 371284328614820126, 371284326230900932, 371284325477963255, 371284322260815100, 371284319033286625]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 21330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 21300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362468188542117584, 362468194679424690⟩, ⟨343800775444003576, 343889387587494620⟩, true⟩

def words04 : List Nat := [371284315805767444, 371284314766043565, 371284312626213691, 371284311398880008, 371284310171444011, 371284308552393933, 371284304838927370, 371284303312518691, 371284301909991911, 371284301910693426]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 21340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 21300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362448577981521693, 362448584124895869⟩, ⟨762700025681074168, 762788767387146930⟩, true⟩

def words05 : List Nat := [371284301156792948, 371284299989426341, 371284299511827844, 371284299512560974, 371284299374583143, 371284299645123203, 371284299645635002, 371284299547630461, 371284296880624580, 371284295209511373]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 21350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 21300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362429777140781861, 362429783290084989⟩, ⟨1164528588773824841, 1164617457153570661⟩, true⟩

def words06 : List Nat := [371284293538174980, 371284293504805843, 371284291525189695, 371284289552292748, 371284287579319935, 371284286285225597, 371284283905653729, 371284283060073041, 371284282214343100, 371284281065337847]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 21360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 21300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362462262192511666, 362462268347838949⟩, ⟨469938112536060753, 470027109682782675⟩, true⟩

def words07 : List Nat := [371284278515717775, 371284276507729878, 371284274499593452, 371284273029236192, 371284268648206772, 371284264042833860, 371284259437612529, 371284257013419488, 371284253805242287, 371284252777665085]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 21370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 21300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362437808876113239, 362437815037453404⟩, ⟨992702047093706045, 992791172825712243⟩, true⟩

def words08 : List Nat := [371284251749941039, 371284250729195035, 371284246799672048, 371284245049989820, 371284243300134646, 371284241586062687, 371284237899546623, 371284234220967410, 371284230542468183, 371284228837024499]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 21380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 21300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362430227836641611, 362430234004001616⟩, ⟨1155114642256665484, 1155203896784086828⟩, true⟩

def words09 : List Nat := [371284226675391780, 371284226683831300, 371284226684334993, 371284226684081149, 371284224433124288, 371284222261503281, 371284220094286103, 371284220094956685, 371284218016367312, 371284215494505546]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 21390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 21300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 21300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk213
