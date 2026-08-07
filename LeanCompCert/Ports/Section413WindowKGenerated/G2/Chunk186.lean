import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk186

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360668121502920932, 360668123497953840⟩, ⟨(-1538211982837122006), (-1538186866372725690)⟩, true⟩

def state01 : KState := ⟨⟨360614440771208614, 360614442768472911⟩, ⟨(-539772620040007284), (-539747462060559864)⟩, true⟩

def words00 : List Nat := [360585433230695580, 360585434995896811, 360585434996111097, 360585434808531234, 360585434620932999, 360585434364150079, 360585436621625310, 360585438878902904, 360585439680529606, 360585441239159035]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 18600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 18600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360683603131352768, 360683605130859824⟩, ⟨(-1827480413316574985), (-1827455213588724417)⟩, true⟩

def words01 : List Nat := [360585444388998445, 360585447538572513, 360585450581645361, 360585452180853714, 360585452181072865, 360585451017573621, 360585451569644476, 360585455110889698, 360585460382296617, 360585465653195428]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 18610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 18600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360583683382904442, 360583685384671742⟩, ⟨33077886139028154, 33103127963809816⟩, true⟩

def words02 : List Nat := [360585469462492626, 360585470407444857, 360585471771444370, 360585473135365303, 360585473535988710, 360585473536226109, 360585472176388654, 360585468608021395, 360585465039992862, 360585462256811507]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 18620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 18600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360568340776572251, 360568342780574067⟩, ⟨319263737449523836, 319289020914781470⟩, true⟩

def words03 : List Nat := [360585463693588314, 360585465225618267, 360585465307037856, 360585466846327252, 360585467648473070, 360585468450595344, 360585472124218256, 360585472938433823, 360585472938647760, 360585472019893530]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 18630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 18600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360595174614915222, 360595176621163343⟩, ⟨(-181029055263440547), (-181003729916079357)⟩, true⟩

def words04 : List Nat := [360585471101187701, 360585470928429865, 360585473809148045, 360585476689602613, 360585476822302966, 360585476822540660, 360585474097548136, 360585472858515660, 360585471619540482, 360585471847697252]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 18640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 18600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360553266541274980, 360553268549785941⟩, ⟨600715994263535784, 600741361824364994⟩, true⟩

def words05 : List Nat := [360585471847909057, 360585470923943922, 360585470346464977, 360585472147164049, 360585472147367566, 360585471213835198, 360585470280377470, 360585467903624819, 360585464345743482, 360585462620623260]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 18650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 18600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360607657665984986, 360607659676739838⟩, ⟨(-414227877812377145), (-414202468369396229)⟩, true⟩

def words06 : List Nat := [360585462032805730, 360585464304674187, 360585465134906609, 360585465965076083, 360585466065691298, 360585468355244213, 360585471069862791, 360585473784235778, 360585474220233898, 360585475408710842]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 18660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 18600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360713844985230012, 360713846998230265⟩, ⟨(-2397423760636325431), (-2397398309260675407)⟩, true⟩

def words07 : List Nat := [360585479455698414, 360585483502321817, 360585489435547650, 360585492519526842, 360585493189999500, 360585493860421377, 360585495730798033, 360585499746371981, 360585506617402567, 360585513487751133]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 18670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 18600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360550806205671116, 360550808220942266⟩, ⟨648430780220092095, 648456274027288721⟩, true⟩

def words08 : List Nat := [360585518569218449, 360585520802915538, 360585521662334980, 360585522521730612, 360585522521930191, 360585521787484952, 360585518206446766, 360585513188235980, 360585508170518071, 360585503580708307]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 18680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 18600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360452565284664131, 360452567302179443⟩, ⟨2485478063651538983, 2485503599413421109⟩, true⟩

def words09 : List Nat := [360585502721377841, 360585503718246410, 360585503718460815, 360585502910742549, 360585501325855035, 360585499014167098, 360585496702659686, 360585494293081851, 360585489041029328, 360585481933164118]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 18690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 18600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 18600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk186
