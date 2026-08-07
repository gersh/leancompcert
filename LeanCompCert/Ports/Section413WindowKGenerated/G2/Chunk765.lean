import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk765

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588819442291189, 360588857426989565⟩, ⟨(-512755261081347249), (-510792630389961857)⟩, true⟩

def state01 : KState := ⟨⟨360595408236163603, 360595446231145155⟩, ⟨(-1016882238574642866), (-1014918821168754284)⟩, true⟩

def words00 : List Nat := [360582180716352394, 360582180854788124, 360582180861609473, 360582180868532797, 360582180869456390, 360582180734149763, 360582180850001156, 360582180993859872, 360582181051311536, 360582181225836523]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 76500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 76500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360609633188360108, 360609671193638244⟩, ⟨(-2105315436295195347), (-2103351231046765449)⟩, true⟩

def words01 : List Nat := [360582181570648061, 360582181915770721, 360582182336252089, 360582182640059295, 360582182798231894, 360582182956493409, 360582183041445674, 360582183231367856, 360582183591475813, 360582183951821661]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 76510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 76500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360595345009804398, 360595383025464330⟩, ⟨(-1012033803927967796), (-1010068804212374014)⟩, true⟩

def words02 : List Nat := [360582184205243371, 360582184288382813, 360582184486700207, 360582184685353304, 360582184839999740, 360582184865762311, 360582184866750263, 360582184763205598, 360582184686257979, 360582184859959994]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 76520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 76500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360585462424613689, 360585500450567539⟩, ⟨(-255743287631414220), (-253777500072071412)⟩, true⟩

def words03 : List Nat := [360582184930789245, 360582185001807774, 360582185002780131, 360582184968120361, 360582184876865348, 360582184743025442, 360582184644258282, 360582184785859903, 360582184830152367, 360582184874600776]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 76530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 76500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360605903762610076, 360605941798860151⟩, ⟨(-1820356153334889427), (-1818389577650765101)⟩, true⟩

def words04 : List Nat := [360582185089237333, 360582185389630933, 360582185860129191, 360582186330830918, 360582186640032810, 360582186779006288, 360582187018679828, 360582187258666996, 360582187524996868, 360582187836434438]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 76540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 76500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360586089107070294, 360586127153731988⟩, ⟨(-303419035520083753), (-301451662775331531)⟩, true⟩

def words05 : List Nat := [360582188013642873, 360582188190979827, 360582188466732327, 360582188827939074, 360582189118040008, 360582189408311132, 360582189587200048, 360582189643738803, 360582189696067123, 360582189748750662]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 76550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 76500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594593759689589, 360594631816626691⟩, ⟨(-954624526095477321), (-952656366613891925)⟩, true⟩

def words06 : List Nat := [360582189971401943, 360582190024050531, 360582190025032649, 360582189980588033, 360582189935966693, 360582189891824940, 360582190014751980, 360582190137886545, 360582190175594848, 360582190339218614]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 76560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 76500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360601545481871526, 360601583549120909⟩, ⟨(-1487050233498565439), (-1485081284353360367)⟩, true⟩

def words07 : List Nat := [360582190529298110, 360582190719699427, 360582190905805383, 360582190921939223, 360582190922947385, 360582190793869524, 360582190664586104, 360582190746394240, 360582191000512804, 360582191254891879]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 76570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 76500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360578215604007415, 360578253681664791⟩, ⟨299600283005903006, 301570029244028502⟩, true⟩

def words08 : List Nat := [360582191402560526, 360582191560921523, 360582191711005716, 360582191861401835, 360582191898135902, 360582191899227795, 360582191808989050, 360582191585761260, 360582191362332503, 360582191141244946]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 76580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 76500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360569463601370438, 360569501689305570⟩, ⟨970021002175420277, 971991535639362273⟩, true⟩

def words09 : List Nat := [360582191178715919, 360582191267802580, 360582191268782138, 360582191226673950, 360582191189070138, 360582191108987158, 360582191117458532, 360582191118550503, 360582191038369564, 360582190873843943]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 76590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 76500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 76500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk765
