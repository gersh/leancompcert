import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk462

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362461896134213063, 362461926778441534⟩, ⟨1087139044675944919, 1088095583897936621⟩, true⟩

def state01 : KState := ⟨⟨362445968788282524, 362445999446153161⟩, ⟨1823144054009083767, 1824101223569581039⟩, true⟩

def words00 : List Nat := [371285478122178094, 371285478004340388, 371285477439354607, 371285476875416855, 371285476310931743, 371285475889988571, 371285475279193344, 371285474723249316, 371285474166787786, 371285473612428201]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 46200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 46200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362485096943612228, 362485127615304463⟩, ⟨14802281256792635, 15760089585780427⟩, true⟩

def words01 : List Nat := [371285472759259872, 371285472148123670, 371285471536238572, 371285471288207825, 371285470650816080, 371285469982311350, 371285469313199351, 371285469074438769, 371285468600844836, 371285468595174342]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 46210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 46200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362475441417026730, 362475472102587475⟩, ⟨461046680885779466, 462005130285741322⟩, true⟩

def words02 : List Nat := [371285468588964672, 371285468512270680, 371285468033159873, 371285467853028553, 371285467672111089, 371285467605112644, 371285467032799826, 371285466441106796, 371285465848794128, 371285465724267894]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 46220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 46200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362458910291813895, 362458940991177770⟩, ⟨1225436211270549310, 1226395298860839986⟩, true⟩

def words03 : List Nat := [371285465705625525, 371285465903777825, 371285466020044229, 371285466021577919, 371285465514814933, 371285465029775264, 371285464543980076, 371285464525597141, 371285463952703399, 371285463380859017]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 46230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 46200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474750949680088, 362474781662793714⟩, ⟨492964825332014155, 493924548780078623⟩, true⟩

def words04 : List Nat := [371285462808336486, 371285462544573696, 371285462110498585, 371285462091863715, 371285462072755915, 371285461979863262, 371285461402484978, 371285461240928067, 371285461110906403, 371285461112497068]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 46240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 46200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362470464072618009, 362470494799711007⟩, ⟨691282159316714339, 692242529380572887⟩, true⟩

def words05 : List Nat := [371285460882754269, 371285460641389349, 371285460488022807, 371285460489721086, 371285460404516883, 371285460301058780, 371285460197041456, 371285460031199509, 371285459291842343, 371285458970255335]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 46250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 46200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362459228599728150, 362459259340499643⟩, ⟨1211115402704329625, 1212076405607334243⟩, true⟩

def words06 : List Nat := [371285458790725496, 371285458792260018, 371285458314153801, 371285457740462333, 371285457166198122, 371285456699244237, 371285456072185209, 371285455753867848, 371285455435071440, 371285455070035138]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 46260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 46200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362489538296138620, 362489569050798995⟩, ⟨(-191417079154168314), (-190455433543012642)⟩, true⟩

def words07 : List Nat := [371285454504939973, 371285454406842231, 371285454674121462, 371285454675660659, 371285454565142808, 371285454379201657, 371285454192682046, 371285454050299892, 371285453763107825, 371285453853773369]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 46270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 46200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362469327016852507, 362469357785360727⟩, ⟨744014230154968374, 744976516714850782⟩, true⟩

def words08 : List Nat := [371285453944255646, 371285453945791080, 371285453486588839, 371285453417093114, 371285453417737552, 371285453419273067, 371285452869796986, 371285452282455861, 371285451694485758, 371285451466862453]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 46280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 46200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362447221325294499, 362447252107631661⟩, ⟨1767425300819926770, 1768388227592679906⟩, true⟩

def words09 : List Nat := [371285451120262456, 371285450848826208, 371285450576903187, 371285450302229928, 371285449474388047, 371285448768319218, 371285448061456059, 371285447755185747, 371285447061049806, 371285446237817249]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 46290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 46200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 46200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk462
