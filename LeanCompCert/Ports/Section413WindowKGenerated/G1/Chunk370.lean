import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk370

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362472300166310937, 362472319469320199⟩, ⟨462919834009119033, 463402501175689635⟩, true⟩

def state01 : KState := ⟨⟨362478410977896881, 362478430291718578⟩, ⟨236967887751598843, 237450955033827765⟩, true⟩

def words00 : List Nat := [371284843791683058, 371284843793034508, 371284844522471716, 371284845253108942, 371284845872275811, 371284845873482245, 371284845688496546, 371284845859141890, 371284846149833183, 371284846151081827]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 37000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 37000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362491112374078666, 362491131698870192⟩, ⟨(-233142030369411485), (-232658557037316853)⟩, true⟩

def words01 : List Nat := [371284845978638239, 371284845822525138, 371284846238320788, 371284846498157771, 371284846801460702, 371284847105236476, 371284847413486794, 371284847414693782, 371284847025401247, 371284847196640720]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 37010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 37000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362490516199255691, 362490535534821874⟩, ⟨(-211061870303284545), (-210577998039019875)⟩, true⟩

def words02 : List Nat := [371284848096789948, 371284848133003034, 371284848133921768, 371284847944563095, 371284847780525600, 371284847781880086, 371284848011233836, 371284848430531419, 371284848847131686, 371284849001969966]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 37020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 37000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362501316754273526, 362501336100749172⟩, ⟨(-611042928003584524), (-610558651705189442)⟩, true⟩

def words03 : List Nat := [371284849687019444, 371284850372664942, 371284851593699626, 371284851843355470, 371284851967194299, 371284852091383048, 371284852171004886, 371284852172334736, 371284852334482492, 371284852780868360]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 37030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 37000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474893073531327, 362474912430906552⟩, ⟨367695835109058144, 368180515181748378⟩, true⟩

def words04 : List Nat := [371284853224665339, 371284853225872914, 371284852698296922, 371284852627971270, 371284852656589398, 371284852657797073, 371284851787201838, 371284850891039507, 371284849994415588, 371284849826727922]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 37040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 37000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362456191766494726, 362456211134741843⟩, ⟨1060699407155987580, 1061184490087864992⟩, true⟩

def words05 : List Nat := [371284849559353486, 371284849507746584, 371284849455755507, 371284849341838681, 371284848353985898, 371284847585797754, 371284846817008967, 371284846776742089, 371284846134070040, 371284845362752849]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 37050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 37000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362484365113949387, 362484384492999299⟩, ⟨16527660571472602, 17013143910683356⟩, true⟩

def words06 : List Nat := [371284844590948514, 371284844547713610, 371284844399191885, 371284844569339201, 371284844570290259, 371284844545439208, 371284843680639242, 371284843423713817, 371284843438163470, 371284843439422571]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 37060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 37000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476182609252791, 362476201999347533⟩, ⟨319998858968819106, 320484751793855330⟩, true⟩

def words07 : List Nat := [371284843427955185, 371284843407463358, 371284844024971710, 371284844335347941, 371284844861443599, 371284845387970348, 371284845824763395, 371284845825972283, 371284845293271424, 371284845061693646]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 37070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 37000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362460430558003974, 362460449958863594⟩, ⟨904149845192664339, 904636137235515477⟩, true⟩

def words08 : List Nat := [371284844964269872, 371284844965478840, 371284844132069031, 371284843263897299, 371284842395320708, 371284841746289368, 371284840830037457, 371284840641066528, 371284840451690844, 371284840256443414]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 37080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 37000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492790455108226, 362492809866899021⟩, ⟨(-296258556403168902), (-295771858867880060)⟩, true⟩

def words09 : List Nat := [371284839599684923, 371284839479201987, 371284839531729439, 371284839532942146, 371284838968562480, 371284838293583597, 371284837668311215, 371284837669657060, 371284837578226148, 371284837794478659]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 37090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 37000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 37000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk370
